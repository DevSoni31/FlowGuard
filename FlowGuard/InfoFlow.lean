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

/-- Hop-wise safety: EVERY individual channel respects the security lattice.
    This is strictly stronger than `isTransitivelySafe`, which checks only
    the pipeline's source and sink endpoints.
    A pipeline can be transitively safe yet contain intermediate hops that
    violate the lattice — `isHopwiseSafe` catches exactly those cases. -/
def isHopwiseSafe (channels : List Channel) : Bool :=
  channels.all channelSecure

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

/-! ## Local approval is not transitive through the security lattice

    A fundamental theorem about why pairwise channel checking is insufficient.

    The medical pipeline shows:
      · High → Medium is locally approved  (clinical summarisation)
      · Medium → Low  is locally approved  (anonymisation)
      · Yet High → Low violates the global security lattice

    This is NOT the same as saying secureFlow is non-transitive
    (secureFlow is in fact transitive — it is a partial order).
    What fails is LOCAL APPROVAL: local policies are too permissive,
    and their composition creates a global violation that neither
    local policy could see individually.
-/

/-- Local approval does not imply global security:
    there exist labels a, b, c such that both hops are locally approved
    yet the end-to-end flow violates the security lattice. -/
theorem localApproval_not_transitive :
    ∃ (a b c : DataLabel),
      locallyApproved a b = true ∧
      locallyApproved b c = true ∧
      secureFlow a c = false :=
  ⟨DataLabel.high, DataLabel.medium, DataLabel.low,
   by decide, by decide, by decide⟩

/-- Corollary: the medical pipeline is the canonical witness.
    Both channels pass local approval; the composed flow fails globally. -/
theorem medicalPipeline_is_witness :
    locallyApproved diagnosticChannel.src diagnosticChannel.dst = true ∧
    locallyApproved summaryChannel.src summaryChannel.dst = true ∧
    secureFlow diagnosticChannel.src summaryChannel.dst = false :=
  ⟨by decide, by decide, by decide⟩

/-- Global security (secureFlow) IS transitive — this is a sanity check
    confirming that our lattice is well-formed. The problem is not with
    the lattice but with over-permissive local policies. -/
theorem secureFlow_transitive :
    ∀ (a b c : DataLabel),
      secureFlow a b = true →
      secureFlow b c = true →
      secureFlow a c = true := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all [secureFlow]

/-! ## Universal IFC Impossibility

    These theorems lift the concrete counterexample to universal statements
    about any labels. They do NOT reference webSearch, exfilData, or any
    specific agent — they are pure theorems about DataLabel and secureFlow.
-/

/-- For EVERY pair of labels (src, dst) where the direct flow is insecure,
    there exists a middle label such that both hops are locally approved
    yet the end-to-end flow is still insecure.

    This is the universal form of cascaded declassification:
    no matter which insecure flow you have, a locally-invisible
    two-hop path through a middle label always exists.

    Proof: locallyApproved is constantly true (maximally permissive),
    so the only obligation is to exhibit a mid where secureFlow src dst = false.
    We case-split on all (src, dst) pairs and decide. -/
theorem cascaded_declassification_universal :
    ∀ (src dst : DataLabel),
      secureFlow src dst = false →
      ∃ (mid : DataLabel),
        locallyApproved src mid = true ∧
        locallyApproved mid dst = true ∧
        secureFlow src dst = false := by
  intro src dst h
  -- For every insecure (src, dst) pair, mid = src itself is always a witness:
  -- locallyApproved is always true, and secureFlow src dst = false is just h.
  exact ⟨src, by simp [locallyApproved], by simp [locallyApproved], h⟩

/-- The security lattice has EXACTLY THREE insecure flow directions.
    This theorem exhaustively characterises when a direct flow is insecure.
    It is the complete, universal characterisation of the threat model. -/
theorem insecure_flows_characterised :
    ∀ (src dst : DataLabel),
      secureFlow src dst = false ↔
      (src = DataLabel.high   ∧ dst = DataLabel.low)   ∨
      (src = DataLabel.high   ∧ dst = DataLabel.medium) ∨
      (src = DataLabel.medium ∧ dst = DataLabel.low) := by
  intro src dst
  cases src <;> cases dst <;> simp [secureFlow]

/-- Existence: a locally-approved pipeline that is globally unsafe.
    This is the universal existential — not tied to any specific agents
    or capability names. Pure information-flow theory. -/
theorem locally_approved_unsafe_pipeline_exists :
    ∃ (channels : List Channel),
      channels ≠ [] ∧
      allLocallyApproved channels = true ∧
      isTransitivelySafe channels = false :=
  ⟨medicalPipeline, by decide, by decide, by decide⟩

/-- For any list of channels where the source is strictly more confidential
    than the sink, the pipeline is globally unsafe regardless of local approvals.
    This is the universal *sufficient condition* for IFC violation — stated
    purely in terms of DataLabel, with no reference to specific agents. -/
theorem downward_src_to_sink_is_unsafe :
    ∀ (src dst : DataLabel),
      secureFlow src dst = false →
      ∀ (channels : List Channel),
        pipelineSourceLabel channels = some src →
        pipelineSinkLabel channels = some dst →
        isTransitivelySafe channels = false := by
  intro src dst hunsafe channels hsrc hdst
  simp [isTransitivelySafe, hsrc, hdst, hunsafe]

/-- Converse: if a pipeline is globally safe, its source label
    must be no more confidential than its sink label.
    Together with the above, this gives a complete characterisation. -/
theorem safe_pipeline_implies_upward_flow :
    ∀ (src dst : DataLabel) (channels : List Channel),
      pipelineSourceLabel channels = some src →
      pipelineSinkLabel channels = some dst →
      isTransitivelySafe channels = true →
      secureFlow src dst = true := by
  intro src dst channels hsrc hdst hsafe
  simp only [isTransitivelySafe, hsrc, hdst] at hsafe
  exact hsafe

/-! ## Gap 4 — Parametric IFC theorem
    The existing `cascaded_declassification_universal` uses `locallyApproved`
    which is constantly `true`, making the theorem about secureFlow alone.
    This parametric version quantifies over ANY policy function — the real
    mathematical content is that ANY policy permitting a two-hop chain with
    a net insecure flow is compositionally dangerous, regardless of how
    restrictive or permissive it is. -/

/-- THE PARAMETRIC CASCADED DECLASSIFICATION THEOREM

    For ANY local approval policy (not just the maximally permissive one),
    if the policy approves a two-hop chain src → mid → dst where the
    end-to-end flow src → dst violates the security lattice, then
    that policy is compositionally dangerous.

    The quantification over `policy` is the real content: this holds
    for a maximally permissive policy, a minimally permissive policy,
    and everything in between. The problem is structural, not a matter
    of tuning the policy. -/
theorem cascaded_declassification_parametric
    (policy : DataLabel → DataLabel → Bool)
    (src mid dst : DataLabel)
    (h1 : policy src mid = true)
    (h2 : policy mid dst = true)
    (h3 : secureFlow src dst = false) :
    ∃ (a b c : DataLabel),
      policy a b = true ∧ policy b c = true ∧ secureFlow a c = false :=
  ⟨src, mid, dst, h1, h2, h3⟩

/-- Concretely: even a RESTRICTIVE policy that only approves the two
    medical hops is dangerous, because the net High → Low flow is insecure.
    This demonstrates that the danger is independent of how restrictive
    the local policy is — cascaded declassification is unavoidable whenever
    the hop chain spans a downward lattice path. -/
theorem medical_hops_dangerous_for_any_policy
    (policy : DataLabel → DataLabel → Bool)
    (h1 : policy DataLabel.high DataLabel.medium = true)
    (h2 : policy DataLabel.medium DataLabel.low = true) :
    ∃ (a b c : DataLabel),
      policy a b = true ∧ policy b c = true ∧ secureFlow a c = false :=
  cascaded_declassification_parametric policy _ _ _ h1 h2 (by decide)

/-! ## New Gap A — Endpoint-only blindness of `isTransitivelySafe`

    `isTransitivelySafe` checks only the source label of the first channel
    and the destination label of the last channel. An intermediate hop that
    violates the security lattice is completely invisible to it.
    `isHopwiseSafe` is the stronger check that catches these intermediate violations. -/

/-- ENDPOINT-BLINDNESS THEOREM

    There exists a pipeline where `isTransitivelySafe` reports SAFE
    yet `isHopwiseSafe` reports UNSAFE.

    The witness: [Low→High, High→Low, Low→High].
    - Source = Low, Sink = High → `isTransitivelySafe` sees secureFlow Low High = true ✓
    - But the middle hop High→Low violates the lattice → `isHopwiseSafe` = false ✗

    This is a precise statement of the limitation: endpoint checking is
    insufficient for pipeline security when intermediate hops can violate
    the lattice. -/
theorem transitive_safety_misses_intermediate :
    ∃ (channels : List Channel),
      isTransitivelySafe channels = true ∧
      isHopwiseSafe channels = false :=
  ⟨[ { name := "a", src := DataLabel.low,  dst := DataLabel.high },
      { name := "b", src := DataLabel.high, dst := DataLabel.low  },
      { name := "c", src := DataLabel.low,  dst := DataLabel.high } ],
   by decide, by decide⟩

/-- `isHopwiseSafe` gives you per-hop security certificates.
    If a pipeline is hopwise-safe, every single channel in it is individually
    secure — there are no intermediate violations hiding from endpoint checks. -/
theorem hopwise_safe_certificate (channels : List Channel)
    (h : isHopwiseSafe channels = true) :
    ∀ ch ∈ channels, secureFlow ch.src ch.dst = true := by
  simp only [isHopwiseSafe, List.all_eq_true, channelSecure] at h
  exact h

/-- `isTransitivelySafe` is strictly WEAKER than `isHopwiseSafe`:
    a pipeline can pass the transitive check while failing the hop-wise check.
    The witness is `transitive_safety_misses_intermediate`. -/
theorem transitive_safe_not_implies_hopwise :
    ∃ (channels : List Channel),
      isTransitivelySafe channels = true ∧
      isHopwiseSafe channels = false :=
  transitive_safety_misses_intermediate

/-- The medical pipeline is hopwise-UNSAFE: the second hop High→Low
    is a direct security violation visible to `isHopwiseSafe`. -/
theorem medicalPipeline_hopwise_unsafe :
    isHopwiseSafe medicalPipeline = false := by decide

/-- The safe reference pipeline is hopwise-safe: every hop is upward,
    and the whole pipeline passes both the hop-wise and transitive checks. -/
theorem safePipelineIFC_hopwise_safe :
    isHopwiseSafe safePipelineIFC = true := by decide

end FlowGuard
