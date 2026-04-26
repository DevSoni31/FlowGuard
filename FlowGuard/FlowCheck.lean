import FlowGuard.CapHypergraph
import FlowGuard.InfoFlow
import FlowGuard.AgentProgram
import Mathlib.Tactic

namespace FlowGuard

/-! ## Unified Pipeline

    A pipeline bundles:
      · A list of agents with their capability contracts
      · The hyperedges that govern capability emergence (Layer 1)
      · The channels that connect agents (Layer 2)
-/

structure Pipeline where
  agents : List Agent
  capEdges : List HyperEdge
  channels : List Channel

/-! ## ValidPipeline — the dual-obligation certificate

    A pipeline is valid if and only if it satisfies BOTH:
      1. Capability safety   — no emergent capability reaches a forbidden set
      2. Transitive IFC      — no high-confidentiality data reaches a low output

    This is the `flow_check` certificate.
    A pipeline that cannot produce an instance of this class
    is rejected at compile time.
-/

class ValidPipeline (P : Pipeline) : Prop where
  capSafe : ∀ a ∈ P.agents, isCapSafe P.capEdges a = true
  ifcSafe : isTransitivelySafe P.channels = true

/-! ## Negative result 1 — the capability counterexample pipeline is invalid

    The team {webAgent, execAgent} with the exfil hyperedge cannot be
    a ValidPipeline because capSafe fails for the composed agent.
-/

def unsafePipelineCap : Pipeline :=
  { agents   := [webAgent, execAgent, compose webAgent execAgent]
    capEdges := demoEdges
    channels := [] }

theorem unsafePipelineCap_not_valid :
    ¬ (∀ a ∈ unsafePipelineCap.agents, isCapSafe unsafePipelineCap.capEdges a = true) := by
  intro h
  have := h (compose webAgent execAgent) (by simp [unsafePipelineCap])
  simp only [unsafePipelineCap] at this
  exact absurd this (by decide)

/-! ## Negative result 2 — the medical IFC pipeline is invalid -/

def unsafePipelineIFC : Pipeline :=
  { agents   := []
    capEdges := []
    channels := medicalPipeline }

theorem unsafePipelineIFC_not_valid :
    isTransitivelySafe unsafePipelineIFC.channels = false := by
  decide

/-! ## Positive result — a ValidPipeline instance exists

    A pipeline with no hyperedges (no emergence possible) and
    an upward-only channel sequence (Low → High) is fully certified.
-/

def trustedPipeline : Pipeline :=
  { agents   := [webAgent, execAgent]
    capEdges := []
    channels := safePipelineIFC }

instance trustedPipeline_valid : ValidPipeline trustedPipeline where
  capSafe := by
    intro a ha
    simp only [trustedPipeline, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · decide
    · decide
  ifcSafe := by
    decide

/-! ## The master theorem

    FlowGuard is sound: if a pipeline has a ValidPipeline certificate,
    then it is both capability-safe and IFC-safe.
    This is trivially true by definition, but stating it explicitly
    makes the guarantee machine-checkable.
-/

theorem flowguard_sound (P : Pipeline) [h : ValidPipeline P] :
    (∀ a ∈ P.agents, isCapSafe P.capEdges a = true) ∧
    isTransitivelySafe P.channels = true :=
  ⟨h.capSafe, h.ifcSafe⟩

/-! ## Corollary: trustedPipeline satisfies both guarantees -/

theorem trustedPipeline_certified :
    (∀ a ∈ trustedPipeline.agents, isCapSafe trustedPipeline.capEdges a = true) ∧
    isTransitivelySafe trustedPipeline.channels = true :=
  flowguard_sound trustedPipeline

end FlowGuard
