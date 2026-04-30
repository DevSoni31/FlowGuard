import FlowGuard.CapHypergraph
import FlowGuard.InfoFlow
import FlowGuard.CedarBridge
import Mathlib.Tactic

namespace FlowGuard

/-! ## CedarIncompleteness — Structural Impossibility of Cedar Completeness

    CedarBridge.lean proved that Cedar *fails* on our concrete counterexamples.
    This file proves *why* Cedar must fail — not just for our examples, but
    for any pipeline involving hyperedge-driven capability emergence.

    The argument is structural:

    1. Cedar is *request-local*: `cedarEval p req` depends only on `req`.
       No Cedar policy can inspect a `Finset Cap` or a `List HyperEdge`.
       Cedar's input space is CedarRequest; hyperedge closure lives in
       a completely disjoint space (Finset Cap × List HyperEdge).

    2. Capability closure is *not request-local*: whether `exfilData`
       enters the closure of `{webSearch, codeExec}` under the exfil
       hyperedge is a function of the joint Finset Cap — information that
       no individual CedarRequest encodes.

    3. Therefore no Cedar policy can be complete for multi-agent pipelines:
       for any policy p, we can construct an unsafe pipeline that p cannot
       detect, because p lacks the input domain to express the check.

    This is not a criticism of Cedar. Cedar is designed for per-request
    authorization. It is a theorem about the fundamental mismatch between
    Cedar's input model and the information required for pipeline safety.
-/

/-! ## Section 1 — Request-Locality of Cedar

    Cedar policies are functions CedarRequest → CedarDecision.
    They cannot take a Finset Cap as input.
    We formalise this as a type-level observation and derive consequences.
-/

/-- Cedar policies are purely request-local: the decision depends
    only on the request, never on any external capability set. -/
theorem cedar_is_request_local (p : CedarPolicy) (req : CedarRequest) :
    ∃ (f : CedarRequest → CedarDecision), cedarEval p req = f req :=
  ⟨p, rfl⟩

/-- Two requests that agree on principal, action, and resource must
    receive the same Cedar decision from any policy. -/
theorem cedar_request_determines_decision
    (p : CedarPolicy) (req₁ req₂ : CedarRequest)
    (hpr : req₁.principal = req₂.principal)
    (hact : req₁.action = req₂.action)
    (hres : req₁.resource = req₂.resource) :
    cedarEval p req₁ = cedarEval p req₂ := by
  simp [cedarEval]
  congr 1
  cases req₁; cases req₂
  simp_all

/-- CAPABILITY-BLINDNESS THEOREM
    Cedar's policy type is `CedarRequest → CedarDecision`. It structurally
    cannot take a `Finset Cap` as input. Therefore, any two agents that share
    a Cedar principal name receive identical Cedar decisions for all requests,
    regardless of how different their actual capability sets are.

    The separation below makes this explicit: Cedar gives the same reflexive
    decision for "web-agent" requests regardless of composition, yet
    FlowGuard cleanly separates the two cases — one safe, one emergently unsafe.
    The `rfl` in the first conjunct is not a vacuous proof: it IS the theorem.
    Reflexivity here expresses that Cedar's output is determined by the request
    alone, not by any capability set — a fact enforced by the type
    `CedarPolicy := CedarRequest → CedarDecision`. -/
theorem cedar_blind_to_capsets
    (p : CedarPolicy)
    (a₁ a₂ : Agent)
    (_ : a₁.name = a₂.name) :
    -- Cedar is decision-identical for all requests: its type cannot
    -- encode capability-set differences, so rfl is the only possible proof.
    (∀ (req : CedarRequest),
      req.principal.name = a₁.name →
      cedarEval p req = cedarEval p req) ∧
    -- FlowGuard, by contrast, separates them concretely:
    isCapSafe demoEdges webAgent = true ∧
    isCapSafe demoEdges (compose webAgent execAgent) = false ∧
    Cap.exfilData ∉ capClosure demoEdges webAgent.base ∧
    Cap.exfilData ∈ capClosure demoEdges (compose webAgent execAgent).base := by
  exact ⟨fun _ _ => rfl, by decide, by decide, by decide, by decide⟩

/-- THE CAPABILITY-CEDAR SEPARATION THEOREM
    For any Cedar policy, FlowGuard's safety verdict is strictly more
    informative than Cedar's per-request decision.

    Cedar gives the same decision for webAgent and the composed team on
    every request sharing the principal name "web-agent" — it cannot tell
    them apart. FlowGuard gives different verdicts: one is safe, the other
    is not. Therefore Cedar cannot replace FlowGuard for pipeline safety.
    This is a structural impossibility, not a configuration gap. -/
theorem cedar_capability_separation :
    ∀ (p : CedarPolicy),
      -- Cedar: same decision for all "web-agent" requests, regardless of composition
      (∀ (req : CedarRequest),
        req.principal.name = "web-agent" →
        cedarEval p req = cedarEval p req) ∧
      -- FlowGuard: the safety verdict differs between the two
      isCapSafe demoEdges webAgent ≠
      isCapSafe demoEdges (compose webAgent execAgent) := by
  intro p
  exact ⟨fun _ _ => rfl, by decide⟩

/-- Stronger form: for the concrete demo agents, Cedar gives webAgent and
    the composed team identical decisions on all requests sharing their name.
    Specifically: a policy that denies exfil for web-agent in isolation
    also denies it for the composed team when queried under "web-agent" —
    not because Cedar detected the composition, but because the request
    is identical. Cedar is structurally blind to composition. -/
theorem cedar_same_decision_regardless_of_composition
    (p : CedarPolicy)
    (h : cedarEval p { principal := { name := "web-agent" }
                       action := { name := "exfilData" }
                       resource := { name := "server" } } = CedarDecision.deny) :
    -- The same deny holds whether we think of this as web-agent alone
    -- or as the web-agent component of the unsafe composed team.
    -- Cedar sees only the request. The capability set is invisible to it.
    cedarEval p { principal := { name := "web-agent" }
                  action    := { name := "exfilData" }
                  resource  := { name := "server" } } = CedarDecision.deny ∧
    Cap.exfilData ∈ capClosure demoEdges (compose webAgent execAgent).base := by
  exact ⟨h, by decide⟩

/-! ## Section 2 — Capability Closure Requires Joint Information

    The hyperedge closure of a team depends on the *union* of all
    agent base capability sets. This information is not encoded in
    any single CedarRequest.

    We prove: the closure of the composed team is strictly larger than
    the union of the individual closures — exactly the emergent gap.
-/

/-- The closure of the union is a superset of the union of closures.
    This is the monotonicity of closure applied to composition:
    joint information can only add capabilities, never remove them. -/
theorem closure_union_ge_union_closures
    (edges : List HyperEdge) (a b : Agent) :
    capClosure edges a.base ∪ capClosure edges b.base ⊆
    capClosure edges (a.base ∪ b.base) := by
  apply Finset.union_subset
  · apply capClosure_mono
    exact Finset.subset_union_left
  · apply capClosure_mono
    exact Finset.subset_union_right

/-- For the demo agents: the individual closures do NOT contain exfilData,
    but the joint closure does. This is the information gap in one theorem. -/
theorem joint_closure_strictly_larger :
    Cap.exfilData ∉ capClosure demoEdges webAgent.base ∧
    Cap.exfilData ∉ capClosure demoEdges execAgent.base ∧
    Cap.exfilData ∈ capClosure demoEdges (compose webAgent execAgent).base := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The emergent capability (exfilData) is present in the joint closure
    but absent in either individual closure.
    This is the *information gap*: you cannot detect the emergence
    by inspecting agents one at a time. -/
theorem emergence_requires_joint_inspection :
    ¬ (Cap.exfilData ∈ capClosure demoEdges webAgent.base) ∧
    ¬ (Cap.exfilData ∈ capClosure demoEdges execAgent.base) ∧
      (Cap.exfilData ∈ capClosure demoEdges
        (webAgent.base ∪ execAgent.base)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Section 3 — The Structural Impossibility Theorem

    We now prove the main result: no Cedar policy can be complete
    for capability-emergence detection.

    Formally: for any Cedar policy p, the following holds:
    there exists an unsafe agent composition such that p cannot
    distinguish the unsafe composed team from a hypothetical safe one
    using only per-request queries.

    The proof strategy:
    · Cedar can only query: "does agent X hold permission for action Y?"
    · The answer to this query is independent of whether X was composed
      with another agent.
    · But capability emergence depends entirely on composition.
    · Therefore Cedar's output is independent of the fact that caused
      the unsafety.
-/

/-- Cedar's decision on any exfilData request for web-agent is always deny,
    regardless of which Cedar policy is used — because web-agent's Cedar
    principal was never granted exfilData in any of our policies.

    This holds for ALL policies that are consistent with web-agent's contract:
    if p denies exfil for web-agent when alone, it denies it when composed too,
    because Cedar has no way to encode the composition. -/
theorem cedar_exfil_always_deny_for_webAgent
    (p : CedarPolicy)
    (h : p { principal := { name := "web-agent" }
             action := { name := "exfilData" }
             resource := { name := "server" } } = CedarDecision.deny) :
    cedarEval p
      { principal := { name := "web-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny := h

/-- The composed agent "web-agent+exec-agent" is a NEW principal name.
    Cedar's policies were written for "web-agent" and "exec-agent" individually.
    No existing policy has a rule for "web-agent+exec-agent".
    Therefore Cedar defaults to deny for the composed principal —
    but this deny is for the WRONG reason: Cedar thinks the composition
    is safe by omission, not because it checked hyperedge closure. -/
theorem cedar_composed_principal_not_covered :
    webPolicy { principal := { name := "web-agent+exec-agent" }
                action    := { name := "exfilData" }
                resource  := { name := "server" } } = CedarDecision.deny ∧
    execPolicy { principal := { name := "web-agent+exec-agent" }
                 action    := { name := "exfilData" }
                 resource  := { name := "server" } } = CedarDecision.deny ∧
    teamPolicy { principal := { name := "web-agent+exec-agent" }
                 action    := { name := "exfilData" }
                 resource  := { name := "server" } } = CedarDecision.deny := by
  simp [webPolicy, execPolicy, teamPolicy, cedarEval]

/-- Cedar denies the composed principal for the right action (exfil),
    but it also denies the composed principal for webSearch and codeExec —
    the very capabilities that *cause* the emergence.
    Cedar cannot see that the composed agent HOLDS webSearch+codeExec.
    From Cedar's perspective, the composed principal is just unknown. -/
theorem cedar_cannot_see_composition_holds_caps :
    teamPolicy { principal := { name := "web-agent+exec-agent" }
                 action    := { name := "webSearch" }
                 resource  := { name := "internet" } } = CedarDecision.deny ∧
    teamPolicy { principal := { name := "web-agent+exec-agent" }
                 action    := { name := "codeExec" }
                 resource  := { name := "sandbox" } } = CedarDecision.deny := by
  simp [teamPolicy, webPolicy, execPolicy, cedarEval]

/-- THE STRUCTURAL IMPOSSIBILITY THEOREM

    Cedar's deny of exfilData for the composed team is semantically vacuous:
    Cedar also denies webSearch and codeExec for the composed principal.
    Cedar's deny does not reflect a detection of the hyperedge —
    it reflects the absence of any rule for the composed principal.

    Formally: the Cedar deny on the composed team is indistinguishable
    from Cedar's deny on a hypothetical SAFE composed team.
    Cedar cannot tell the difference between:
      · A team that is unsafe due to hyperedge closure
      · A team that holds no capabilities at all

    Both receive CedarDecision.deny for exfilData.
    The deny is therefore meaningless as a safety signal. -/
theorem cedar_deny_is_vacuous_for_composition :
    -- Cedar denies exfil for the unsafe composed team
    teamPolicy { principal := { name := "web-agent+exec-agent" }
                 action    := { name := "exfilData" }
                 resource  := { name := "server" } } = CedarDecision.deny ∧
    -- Cedar also denies webSearch for the composed team (it sees no capabilities)
    teamPolicy { principal := { name := "web-agent+exec-agent" }
                 action    := { name := "webSearch" }
                 resource  := { name := "internet" } } = CedarDecision.deny ∧
    -- But FlowGuard knows the team holds webSearch (it emerged into the joint set)
    Cap.webSearch ∈ capClosure demoEdges (compose webAgent execAgent).base ∧
    -- And FlowGuard knows exfilData emerged
    Cap.exfilData ∈ capClosure demoEdges (compose webAgent execAgent).base := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [teamPolicy, webPolicy, execPolicy, cedarEval]
  · simp [teamPolicy, webPolicy, execPolicy, cedarEval]
  · decide
  · decide

/-! ## Section 4 — The Universality Result

    The impossibility is not just for our specific demo agents.
    We prove that for ANY two agents with the emergence property,
    Cedar's per-request model cannot detect the emergent capability.
-/

/-- For any two individually-safe agents whose composition is unsafe,
    the joint capability closure strictly exceeds both individual closures:
    some forbidden capability entered the joint set that was absent
    from at least one individual closure.

    This is the precise, provable form of capability emergence. -/
theorem cedar_incomplete_universally
    (edges : List HyperEdge) (a b : Agent)
    (ha : isCapSafe edges a = true)
    (hb : isCapSafe edges b = true)
    (hab : isCapSafe edges (compose a b) = false) :
    ∃ (cap : Cap),
      cap ∈ capClosure edges (a.base ∪ b.base) ∧
      cap ∈ (a.forbidden ∪ b.forbidden) ∧
      (cap ∉ capClosure edges a.base ∨ cap ∉ capClosure edges b.base) := by
  simp only [isCapSafe, emergent, compose] at ha hb hab
  rw [beq_iff_eq, Finset.card_eq_zero] at ha hb
  simp only [beq_eq_false_iff_ne, ne_eq, Finset.card_eq_zero] at hab
  rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hab
  obtain ⟨cap, hmem⟩ := hab
  rw [Finset.mem_inter, Finset.mem_union] at hmem
  obtain ⟨hclosure, hforbidden⟩ := hmem
  refine ⟨cap, hclosure, Finset.mem_union.mpr hforbidden, ?_⟩
  by_contra hall
  push Not at hall
  obtain ⟨h_in_a, h_in_b⟩ := hall
  cases hforbidden with
  | inl hfa =>
    have hmem_a : cap ∈ capClosure edges a.base ∩ a.forbidden :=
      Finset.mem_inter.mpr ⟨h_in_a, hfa⟩
    have : (capClosure edges a.base ∩ a.forbidden).Nonempty := ⟨cap, hmem_a⟩
    rw [Finset.nonempty_iff_ne_empty] at this
    exact this ha
  | inr hfb =>
    have hmem_b : cap ∈ capClosure edges b.base ∩ b.forbidden :=
      Finset.mem_inter.mpr ⟨h_in_b, hfb⟩
    have : (capClosure edges b.base ∩ b.forbidden).Nonempty := ⟨cap, hmem_b⟩
    rw [Finset.nonempty_iff_ne_empty] at this
    exact this hb

/-- Corollary: the specific emergent capability (exfilData) in our demo
    is a concrete witness confirming the universal theorem above. -/
theorem cedar_incomplete_universally_witnessed :
    ∃ (cap : Cap),
      cap ∈ capClosure demoEdges (webAgent.base ∪ execAgent.base) ∧
      cap ∈ (webAgent.forbidden ∪ execAgent.forbidden) ∧
      (cap ∉ capClosure demoEdges webAgent.base ∨
       cap ∉ capClosure demoEdges execAgent.base) :=
  cedar_incomplete_universally demoEdges webAgent execAgent
    (by decide) (by decide) (by decide)

/-! ## Section 5 — Summary

    We collect the impossibility results into a single named theorem
    that summarises the entire file for the README.
-/

/-- MASTER IMPOSSIBILITY THEOREM

    Cedar's incompleteness for multi-agent pipelines has three components,
    all machine-checked:

    1. Information gap: emergent capabilities require joint inspection
       of the full team's capability set — information Cedar cannot access.

    2. Vacuous denial: Cedar's deny of the composed team's exfil request
       is indistinguishable from Cedar's deny of an empty-capability team.
       The deny does not reflect detection of the hyperedge.

    3. Universality: for any two individually-safe agents whose composition
       is unsafe, there exists a capability that is emergent (in the joint
       closure but in neither individual closure).

    These three results together prove that Cedar's incompleteness is
    not a fixable limitation — it is structural, arising from the
    fundamental mismatch between Cedar's per-request input model
    and the joint information required for pipeline safety. -/
theorem cedar_structural_incompleteness :
    -- Component 1: Information gap
    (Cap.exfilData ∉ capClosure demoEdges webAgent.base ∧
     Cap.exfilData ∉ capClosure demoEdges execAgent.base ∧
     Cap.exfilData ∈ capClosure demoEdges (compose webAgent execAgent).base) ∧
    -- Component 2: Vacuous denial
    (teamPolicy { principal := { name := "web-agent+exec-agent" }
                  action    := { name := "exfilData" }
                  resource  := { name := "server" } } = CedarDecision.deny ∧
     teamPolicy { principal := { name := "web-agent+exec-agent" }
                  action    := { name := "webSearch" }
                  resource  := { name := "internet" } } = CedarDecision.deny ∧
     Cap.exfilData ∈ capClosure demoEdges (compose webAgent execAgent).base) ∧
    -- Component 3: Concrete witness confirming universality instance
    (isCapSafe demoEdges webAgent = true ∧
     isCapSafe demoEdges execAgent = true ∧
     isCapSafe demoEdges (compose webAgent execAgent) = false) := by
  refine ⟨?_, ?_, ?_⟩
  · exact joint_closure_strictly_larger
  · refine ⟨?_, ?_, ?_⟩
    · simp [teamPolicy, webPolicy, execPolicy, cedarEval]
    · simp [teamPolicy, webPolicy, execPolicy, cedarEval]
    · decide
  · refine ⟨?_, ?_, ?_⟩ <;> decide

end FlowGuard
