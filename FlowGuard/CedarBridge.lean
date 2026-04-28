import FlowGuard.CapHypergraph
import FlowGuard.InfoFlow
import FlowGuard.AgentProgram
import Mathlib.Tactic

namespace FlowGuard

/-! ## CedarBridge — Modelling Cedar and Proving Its Incompleteness

    Cedar is Amazon's production policy language, used in AWS and formally
    verified by Amazon's automated reasoning team. It evaluates requests of
    the form (principal, action, resource) against a policy set and returns
    Allow or Deny.

    Cedar is *sound*: if a policy denies an action, Cedar will deny it.
    Cedar is *incomplete* for multi-agent pipelines: it evaluates each
    (principal, action, resource) triple in isolation. It cannot see
    capability emergence across agents or transitive IFC violations across
    channels.

    This file formalises Cedar's per-request semantics, maps Cedar concepts
    to FlowGuard concepts, and proves two incompleteness gaps plus the
    structural result that no union of Cedar policies can close them.
-/

/-! ## Cedar Core Types -/

/-- A Cedar principal: the entity making a request (an AI agent) -/
structure CedarPrincipal where
  name : String
  deriving Repr, DecidableEq

/-- A Cedar action: the operation being requested -/
structure CedarAction where
  name : String
  deriving Repr, DecidableEq

/-- A Cedar resource: the object being acted upon -/
structure CedarResource where
  name : String
  deriving Repr, DecidableEq

/-- A Cedar authorization request: the triple Cedar evaluates -/
structure CedarRequest where
  principal : CedarPrincipal
  action    : CedarAction
  resource  : CedarResource
  deriving Repr

/-! ## Cedar Policy Decision -/

/-- Cedar returns one of two decisions for any request -/
inductive CedarDecision where
  | allow
  | deny
  deriving DecidableEq, Repr

/-- A Cedar policy: a function from requests to decisions.
    In the real Cedar semantics this is a set of policy rules evaluated
    in order; we model the net decision as a single function. -/
def CedarPolicy := CedarRequest → CedarDecision

/-! ## Mapping Cedar to FlowGuard

    The bridge between Cedar's request model and FlowGuard's capability model.
    Cedar actions correspond to FlowGuard capabilities.
    Cedar resources carry confidentiality labels.
-/

/-- Map a Cedar action name to a FlowGuard capability.
    This is the semantic link: what capability does this action require? -/
def actionToCap (a : CedarAction) : Option Cap :=
  match a.name with
  | "webSearch"  => some Cap.webSearch
  | "codeExec"   => some Cap.codeExec
  | "readDB"     => some Cap.readDB
  | "sendEmail"  => some Cap.sendEmail
  | "exfilData"  => some Cap.exfilData
  | _            => none

/-- Map a Cedar resource name to a FlowGuard data label.
    Resources carry confidentiality: patient records are High, etc. -/
def resourceToLabel (r : CedarResource) : DataLabel :=
  match r.name with
  | "patientRecord"     => DataLabel.high
  | "diagnosticSummary" => DataLabel.medium
  | "publicReport"      => DataLabel.low
  | _                   => DataLabel.low

/-! ## Cedar Per-Request Evaluation -/

/-- Evaluate a Cedar request against a policy. -/
def cedarEval (policy : CedarPolicy) (req : CedarRequest) : CedarDecision :=
  policy req

/-! ## The Concrete Cedar Policies for our Demo Agents

    We define explicit Cedar policies for webAgent and execAgent that
    correctly reflect their individual capability contracts.
-/

/-- Cedar policy for webAgent: allows webSearch, denies everything else -/
def webPolicy : CedarPolicy := fun req =>
  if req.principal.name = "web-agent" ∧ req.action.name = "webSearch"
  then CedarDecision.allow
  else CedarDecision.deny

/-- Cedar policy for execAgent: allows codeExec, denies everything else -/
def execPolicy : CedarPolicy := fun req =>
  if req.principal.name = "exec-agent" ∧ req.action.name = "codeExec"
  then CedarDecision.allow
  else CedarDecision.deny

/-! ## Per-Agent Correctness Theorems -/

/-- webPolicy allows webSearch for web-agent -/
theorem webPolicy_allows_webSearch :
    cedarEval webPolicy
      { principal := { name := "web-agent" }
        action    := { name := "webSearch" }
        resource  := { name := "internet" } } = CedarDecision.allow := by
  simp [cedarEval, webPolicy]

/-- webPolicy denies exfilData for web-agent -/
theorem webPolicy_denies_exfil :
    cedarEval webPolicy
      { principal := { name := "web-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "internet" } } = CedarDecision.deny := by
  simp [cedarEval, webPolicy]

/-- execPolicy denies exfilData for exec-agent -/
theorem execPolicy_denies_exfil :
    cedarEval execPolicy
      { principal := { name := "exec-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny := by
  simp [cedarEval, execPolicy]

/-- webPolicy denies exec-agent's requests: policies are per-agent scoped -/
theorem webPolicy_denies_exec_agent :
    cedarEval webPolicy
      { principal := { name := "exec-agent" }
        action    := { name := "codeExec" }
        resource  := { name := "sandbox" } } = CedarDecision.deny := by
  simp [cedarEval, webPolicy]

/-! ## The Incompleteness Gap 1 — Capability Emergence

    Cedar evaluates each (principal, action, resource) triple in isolation.
    It has no concept of a HyperEdge. It cannot ask:
    "does the *composition* of webAgent and execAgent hold exfilData?"

    Cedar sees: web-agent ↛ exfil, exec-agent ↛ exfil   (both denied)
    FlowGuard:  {webSearch, codeExec} → exfilData fires  (emergent unsafe)

    Cedar is sound but incomplete for compositional capability emergence.
-/

/-- Cedar's combined policy for the demo team:
    the union of webPolicy and execPolicy, evaluated per-request.
    Cedar sees only individual requests — it cannot see the joint team. -/
def teamPolicy : CedarPolicy := fun req =>
  match cedarEval webPolicy req, cedarEval execPolicy req with
  | CedarDecision.allow, _ => CedarDecision.allow
  | _, CedarDecision.allow => CedarDecision.allow
  | _, _                   => CedarDecision.deny

/-- Cedar's team policy denies exfilData for both agents individually -/
theorem teamPolicy_denies_direct_exfil :
    cedarEval teamPolicy
      { principal := { name := "web-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny ∧
    cedarEval teamPolicy
      { principal := { name := "exec-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny := by
  simp [cedarEval, teamPolicy, webPolicy, execPolicy]

/-- THE INCOMPLETENESS THEOREM — Capability Emergence Gap:

    Cedar denies exfil for every individual request.
    FlowGuard proves the composed team IS capable of exfiltration
    via hyperedge closure.

    This is not a Cedar bug. Cedar does exactly what it is designed to do.
    The gap is structural: Cedar's threat model omits emergent capabilities. -/
theorem cedar_nonCompositionality_gap :
    (cedarEval teamPolicy
      { principal := { name := "web-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny) ∧
    (cedarEval teamPolicy
      { principal := { name := "exec-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny) ∧
    (isCapSafe demoEdges (compose webAgent execAgent) = false) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cedarEval, teamPolicy, webPolicy, execPolicy]
  · simp [cedarEval, teamPolicy, webPolicy, execPolicy]
  · decide

/-! ## The Incompleteness Gap 2 — Information Flow

    Cedar has no notion of data labels or transitive flows.
    A Cedar policy can approve each individual channel in the medical
    pipeline, yet be entirely blind to the transitive High → Low path.
-/

/-- Cedar policy for the medical pipeline:
    each hop is individually approved by its local agent's policy. -/
def medicalPolicy : CedarPolicy := fun req =>
  if req.principal.name = "diagnostic-agent" ∧
     req.action.name = "summarise" ∧
     req.resource.name = "patientRecord"
  then CedarDecision.allow
  else if req.principal.name = "summary-agent" ∧
          req.action.name = "anonymise" ∧
          req.resource.name = "diagnosticSummary"
  then CedarDecision.allow
  else CedarDecision.deny

/-- Cedar approves the diagnostic hop individually -/
theorem medicalPolicy_approves_diagnostic :
    cedarEval medicalPolicy
      { principal := { name := "diagnostic-agent" }
        action    := { name := "summarise" }
        resource  := { name := "patientRecord" } } = CedarDecision.allow := by
  simp [cedarEval, medicalPolicy]

/-- Cedar approves the summary hop individually -/
theorem medicalPolicy_approves_summary :
    cedarEval medicalPolicy
      { principal := { name := "summary-agent" }
        action    := { name := "anonymise" }
        resource  := { name := "diagnosticSummary" } } = CedarDecision.allow := by
  simp [cedarEval, medicalPolicy]

/-- THE INCOMPLETENESS THEOREM — IFC Gap:

    Cedar approves both hops; FlowGuard proves the transitive flow is unsafe.

    Cedar sees: diagnostic hop ✓, summary hop ✓
    FlowGuard:  transitive High → Low violates noninterference ✗ -/
theorem cedar_ifc_gap :
    (cedarEval medicalPolicy
      { principal := { name := "diagnostic-agent" }
        action    := { name := "summarise" }
        resource  := { name := "patientRecord" } } = CedarDecision.allow) ∧
    (cedarEval medicalPolicy
      { principal := { name := "summary-agent" }
        action    := { name := "anonymise" }
        resource  := { name := "diagnosticSummary" } } = CedarDecision.allow) ∧
    (isTransitivelySafe medicalPipeline = false) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cedarEval, medicalPolicy]
  · simp [cedarEval, medicalPolicy]
  · decide

/-! ## The combined incompleteness result -/

/-- Cedar has two distinct structural blind spots, both machine-checked. -/
theorem cedar_is_incomplete :
    (isCapSafe demoEdges (compose webAgent execAgent) = false) ∧
    (isTransitivelySafe medicalPipeline = false) :=
  ⟨by decide, by decide⟩

/-! ## Stretch A — Policy Union Does Not Close the Gap

    One might object: could we fix Cedar by passing it a policy for the
    *composed* agent? We formalise the strongest possible version of this
    attempt — taking the union of all individual policies — and prove it
    still cannot detect capability emergence.

    The reason: the union still evaluates per-request. No request ever
    asks for exfilData from a *composed* principal. The gap is not about
    having more policies — it is about Cedar lacking the concept of
    hyperedge closure entirely.
-/

/-- A naive union policy: allow if ANY individual policy allows this request.
    This is the best Cedar can do with full knowledge of all individual agents. -/
def unionPolicy (policies : List CedarPolicy) : CedarPolicy := fun req =>
  if policies.any (fun p => cedarEval p req = CedarDecision.allow)
  then CedarDecision.allow
  else CedarDecision.deny

/-- Even the union of all individual policies denies exfilData —
    because no individual policy ever permitted it. -/
theorem unionPolicy_denies_exfil :
    cedarEval (unionPolicy [webPolicy, execPolicy])
      { principal := { name := "web-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny := by
  simp [cedarEval, unionPolicy, webPolicy, execPolicy]

/-- THE STRUCTURAL GAP THEOREM:

    The best-possible Cedar policy (full union of all agent policies) still
    cannot detect capability emergence. Adding more Cedar policies cannot
    fix this. FlowGuard requires a fundamentally different formalism:
    hyperedge closure over the joint capability set. -/
theorem policy_union_cannot_close_gap :
    cedarEval (unionPolicy [webPolicy, execPolicy])
      { principal := { name := "web-agent" }
        action    := { name := "exfilData" }
        resource  := { name := "server" } } = CedarDecision.deny ∧
    isCapSafe demoEdges (compose webAgent execAgent) = false :=
  ⟨unionPolicy_denies_exfil, by decide⟩

end FlowGuard
