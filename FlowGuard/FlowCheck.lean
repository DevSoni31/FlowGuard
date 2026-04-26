import FlowGuard.CapHypergraph
import FlowGuard.InfoFlow

namespace FlowGuard

/-! ## Pipeline structure -/

structure Pipeline where
  agents : List Agent
  capEdges : List HyperEdge

/-! ## ValidPipeline typeclass -/

/-- A pipeline is valid if every individual agent passes the capability safety check -/
class ValidPipeline (P : Pipeline) : Prop where
  allAgentsSafe : ∀ a ∈ P.agents, isCapSafe P.capEdges a = true

/-! ## Existence proof: a safe pipeline exists -/

def safePipeline : Pipeline :=
  { agents := [webAgent, execAgent]
    capEdges := [] }

/-- With no hyperedges, no capability emergence is possible,
    so any pipeline of individually safe agents is valid -/
instance : ValidPipeline safePipeline where
  allAgentsSafe := by
    intro a ha
    simp only [safePipeline, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · decide
    · decide

end FlowGuard
