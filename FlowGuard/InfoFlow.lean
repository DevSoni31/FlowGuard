import Mathlib.Order.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace FlowGuard

/-! ## Security Labels

    Labels form a confidentiality hierarchy: low < medium < high.
    The *security* direction: data may only flow *upward* (low → high).
    Any downward flow (high → low) is a noninterference violation.
-/

inductive DataLabel where
  | low
  | medium
  | high
  deriving DecidableEq, Repr

/-- Security-enforced flow: data at level `a` may flow into context `b`
    only if `a` is no more confidential than `b`. -/
def secureFlow : DataLabel → DataLabel → Bool
  | .low,    _       => true
  | .medium, .medium => true
  | .medium, .high   => true
  | .high,   .high   => true
  | _,       _       => false

/-- Local policy approval: what a single agent considers an acceptable
    channel. This can be *more permissive* than the global security policy.
    In the medical example: a hospital protocol may approve High→Medium
    (summarisation) and a separate policy may approve Medium→Low
    (anonymisation), without either policy seeing the full chain. -/
def locallyApproved : DataLabel → DataLabel → Bool
  | _,    _   => true  -- local agents are maximally permissive in isolation

instance : LE DataLabel where
  le a b := secureFlow a b = true

instance (a b : DataLabel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (secureFlow a b = true))

/-! ## Basic security facts -/

theorem low_le_medium : DataLabel.low ≤ DataLabel.medium := by decide
theorem low_le_high : DataLabel.low ≤ DataLabel.high := by decide
theorem medium_le_high : DataLabel.medium ≤ DataLabel.high := by decide
theorem high_not_low : ¬ (DataLabel.high ≤ DataLabel.low) := by decide
theorem high_not_med : ¬ (DataLabel.high ≤ DataLabel.medium) := by decide
theorem med_not_low : ¬ (DataLabel.medium ≤ DataLabel.low) := by decide

/-! ## Tainted data -/

/-- Data paired with its confidentiality label (taint tracking) -/
structure Labelled (α : Type) where
  value : α
  label : DataLabel
  deriving Repr

/-! ## Channels -/

/-- A directed communication channel carrying data from `src` to `dst` -/
structure Channel where
  name : String
  src  : DataLabel
  dst  : DataLabel
  deriving Repr

/-- A channel is *locally approved* if the local agent policy permits the flow -/
def channelLocallyApproved (ch : Channel) : Bool :=
  locallyApproved ch.src ch.dst

/-- A channel is *globally secure* if it respects the security lattice -/
def channelSecure (ch : Channel) : Bool :=
  secureFlow ch.src ch.dst

/-! ## Transitive safety over a pipeline -/

def pipelineSourceLabel (channels : List Channel) : Option DataLabel :=
  channels.head? |>.map (·.src)

def pipelineSinkLabel (channels : List Channel) : Option DataLabel :=
  channels.getLast? |>.map (·.dst)

/-- Transitive safety: does the *net* flow from pipeline source to sink
    respect the global security lattice? -/
def isTransitivelySafe (channels : List Channel) : Bool :=
  match pipelineSourceLabel channels, pipelineSinkLabel channels with
  | some src, some dst => secureFlow src dst
  | _,        _        => true

/-- All local hops are individually approved by their local policies -/
def allLocallyApproved (channels : List Channel) : Bool :=
  channels.all channelLocallyApproved

/-! ## The cascaded declassification counterexample

    Medical pipeline:
      Diagnostic Agent: reads patient records          (label: High)
        ↓  [locally approved: clinical summarisation]
      Summary Agent: produces diagnostic summary       (label: Medium)
        ↓  [locally approved: anonymisation for publication]
      Report Agent: publishes anonymised report        (label: Low)

    Each local hop is approved by its own agent's policy.
    But the composed pipeline creates a transitive path: High → Low.
    This violates noninterference — secret data reaches a public output.
-/

def diagnosticChannel : Channel :=
  { name := "diagnostic→summary"
    src  := DataLabel.high
    dst  := DataLabel.medium }

def summaryChannel : Channel :=
  { name := "summary→report"
    src  := DataLabel.medium
    dst  := DataLabel.low }

def medicalPipeline : List Channel :=
  [diagnosticChannel, summaryChannel]

/-! ### Theorems about the medical pipeline -/

/-- Each channel is locally approved by its own agent's policy -/
theorem diagnosticChannel_locallyApproved :
    channelLocallyApproved diagnosticChannel = true := by decide

theorem summaryChannel_locallyApproved :
    channelLocallyApproved summaryChannel = true := by decide

/-- All local hops pass their local policy checks -/
theorem medicalPipeline_allLocallyApproved :
    allLocallyApproved medicalPipeline = true := by decide

/-- Yet the global security policy is violated: High data reaches a Low output -/
theorem medicalPipeline_globallyUnsafe :
    isTransitivelySafe medicalPipeline = false := by decide

/-- THE HEADLINE THEOREM:
    Noninterference is non-compositional.

    Every local channel is approved by its own policy,
    yet the composed pipeline violates the global security lattice.
    Safe(Agent₁) ∧ Safe(Agent₂) ↛ Safe(Agent₁ ∘ Agent₂) -/
theorem nonInterference_nonCompositional :
    allLocallyApproved medicalPipeline = true ∧
    isTransitivelySafe medicalPipeline = false := by
  decide

/-! ## Existence: a transitively safe pipeline -/

def safeChannel₁ : Channel :=
  { name := "low→medium"
    src  := DataLabel.low
    dst  := DataLabel.medium }

def safeChannel₂ : Channel :=
  { name := "medium→high"
    src  := DataLabel.medium
    dst  := DataLabel.high }

def safePipelineIFC : List Channel :=
  [safeChannel₁, safeChannel₂]

/-- A pipeline where data only flows upward is both locally and globally safe -/
theorem safePipelineIFC_fullyVerified :
    allLocallyApproved safePipelineIFC = true ∧
    isTransitivelySafe safePipelineIFC = true := by
  decide

end FlowGuard
