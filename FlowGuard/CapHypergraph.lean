import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace FlowGuard

/-! ## Capabilities -/

inductive Cap where
  | webSearch
  | codeExec
  | readDB
  | sendEmail
  | exfilData
  deriving DecidableEq, Fintype, Repr

/-! ## Hyperedges and closure -/

structure HyperEdge where
  premises : Finset Cap
  conclusion : Cap
  deriving DecidableEq

def step (edges : List HyperEdge) (S : Finset Cap) : Finset Cap :=
  edges.foldl
    (fun acc e => if e.premises ⊆ acc then insert e.conclusion acc else acc)
    S

def closureAux : Nat → List HyperEdge → Finset Cap → Finset Cap
  | 0,     _,     S => S
  | n + 1, edges, S => closureAux n edges (step edges S)

def capClosure (edges : List HyperEdge) (S : Finset Cap) : Finset Cap :=
  closureAux (Fintype.card Cap) edges S

/-! ## Monotonicity of the closure operator -/

/-- A single foldl step preserves any superset relationship. -/
private theorem foldl_step_mono (edges : List HyperEdge) (S T : Finset Cap)
    (h : S ⊆ T) :
    let f := fun (acc : Finset Cap) (e : HyperEdge) =>
      if e.premises ⊆ acc then insert e.conclusion acc else acc
    List.foldl f S edges ⊆ List.foldl f T edges := by
  induction edges generalizing S T with
  | nil => simpa
  | cons e rest ih =>
    simp only [List.foldl_cons]
    by_cases hS : e.premises ⊆ S
    · have hT : e.premises ⊆ T := hS.trans h
      simp only [hS, hT, ite_true]
      exact ih _ _ (Finset.insert_subset_insert _ h)
    · by_cases hT : e.premises ⊆ T
      · simp only [hS, hT, ite_true, ite_false]
        apply ih
        exact h.trans (Finset.subset_insert e.conclusion T)
      · simp only [hS, hT, ite_false]
        exact ih _ _ h

/-- `step` is monotone: S ⊆ T → step edges S ⊆ step edges T -/
theorem step_mono (edges : List HyperEdge) {S T : Finset Cap} (h : S ⊆ T) :
    step edges S ⊆ step edges T := by
  unfold step
  exact foldl_step_mono edges S T h

/-- `step` is extensive: S ⊆ step edges S -/
private theorem step_extensive (edges : List HyperEdge) (S : Finset Cap) :
    S ⊆ step edges S := by
  unfold step
  induction edges generalizing S with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons]
    by_cases h : e.premises ⊆ S
    · simp only [h, ite_true]
      exact (ih S).trans (foldl_step_mono rest S (insert e.conclusion S)
        (Finset.subset_insert e.conclusion S))
    · simp only [h, ite_false]
      exact ih S

/-- `closureAux` is monotone in its Finset argument. -/
theorem closureAux_mono (n : Nat) (edges : List HyperEdge) {S T : Finset Cap}
    (h : S ⊆ T) : closureAux n edges S ⊆ closureAux n edges T := by
  induction n generalizing S T with
  | zero => simpa [closureAux]
  | succ n ih => exact ih (step_mono edges h)

/-- The closure operator is monotone:
    a larger base set always yields a larger emergent set. -/
theorem capClosure_mono (edges : List HyperEdge) {S T : Finset Cap} (h : S ⊆ T) :
    capClosure edges S ⊆ capClosure edges T :=
  closureAux_mono _ edges h

/-- The closure is extensive: every base capability survives into the closure. -/
theorem capClosure_extensive (edges : List HyperEdge) (S : Finset Cap) :
    S ⊆ capClosure edges S := by
  unfold capClosure
  induction (Fintype.card Cap) generalizing S with
  | zero => simp [closureAux]
  | succ n ih =>
    simp only [closureAux]
    exact (step_extensive edges S).trans (ih (step edges S))

/-! ## Empty-edges simplification -/

/-- With no hyperedges, `step` is the identity. -/
private lemma step_empty (S : Finset Cap) : step [] S = S := by
  simp [step]

/-- With no hyperedges, `closureAux` is the identity at every iteration count. -/
lemma closureAux_empty (n : Nat) (S : Finset Cap) : closureAux n [] S = S := by
  induction n generalizing S with
  | zero => simp [closureAux]
  | succ n ih =>
    simp only [closureAux, step_empty, ih]

/-- With no hyperedges, `capClosure` is the identity:
    no capability emergence is possible without hyperedges. -/
@[simp]
theorem capClosure_empty (S : Finset Cap) : capClosure [] S = S := by
  simp [capClosure, closureAux_empty]

/-! ## Fixed-point theory -/

/-- `closureAux` is non-decreasing in its iteration count:
    one more application of `step` always yields a superset. -/
lemma closureAux_step_subset (n : Nat) (edges : List HyperEdge) (S : Finset Cap) :
    closureAux n edges S ⊆ closureAux (n + 1) edges S := by
  induction n generalizing S with
  | zero =>
    simp only [closureAux]
    exact step_extensive edges S
  | succ n ih =>
    simp only [closureAux]
    exact ih (step edges S)

/-- `capClosure` is the LEAST closed superset of `S`:
    any set T that contains S and is closed under all hyperedges
    must contain the closure.
    This is the minimal fixed-point property — `capClosure` is not merely
    *a* closed superset, but the *smallest possible* one. -/
theorem capClosure_is_least_fixpoint
    (edges : List HyperEdge) (S T : Finset Cap)
    (hS : S ⊆ T)
    (hfix : step edges T ⊆ T) :
    capClosure edges S ⊆ T := by
  suffices h : ∀ n, closureAux n edges S ⊆ T from h (Fintype.card Cap)
  intro n
  induction n generalizing S with
  | zero => simpa [closureAux]
  | succ n ih =>
    simp only [closureAux]
    apply ih
    exact (step_mono edges hS).trans hfix

/-! ## Agents -/

structure Agent where
  name : String
  base : Finset Cap
  forbidden : Finset Cap

def emergent (edges : List HyperEdge) (a : Agent) : Finset Cap :=
  capClosure edges a.base

/-- Boolean safety check: emergent capabilities must not intersect forbidden ones -/
def isCapSafe (edges : List HyperEdge) (a : Agent) : Bool :=
  (emergent edges a ∩ a.forbidden).card == 0

def compose (a b : Agent) : Agent :=
  { name      := s!"{a.name}+{b.name}"
    base      := a.base ∪ b.base
    forbidden := a.forbidden ∪ b.forbidden }

/-! ## The counterexample -/

/-- A single hyperedge: webSearch ∧ codeExec → exfilData -/
def exfilEdge : HyperEdge :=
  { premises   := ({Cap.webSearch, Cap.codeExec} : Finset Cap)
    conclusion := Cap.exfilData }

def demoEdges : List HyperEdge := [exfilEdge]

def webAgent : Agent :=
  { name      := "web-agent"
    base      := ({Cap.webSearch}  : Finset Cap)
    forbidden := ({Cap.exfilData}  : Finset Cap) }

def execAgent : Agent :=
  { name      := "exec-agent"
    base      := ({Cap.codeExec}  : Finset Cap)
    forbidden := ({Cap.exfilData} : Finset Cap) }

/-! ## Machine-checked theorems -/

theorem webAgent_is_safe :
    isCapSafe demoEdges webAgent = true := by decide

theorem execAgent_is_safe :
    isCapSafe demoEdges execAgent = true := by decide

theorem composedTeam_is_unsafe :
    isCapSafe demoEdges (compose webAgent execAgent) = false := by decide

/-- The headline theorem: both agents are individually safe,
    yet their composition is unsafe — safety is non-compositional. -/
theorem nonCompositionalityCounterexample :
    isCapSafe demoEdges webAgent = true ∧
    isCapSafe demoEdges execAgent = true ∧
    isCapSafe demoEdges (compose webAgent execAgent) = false := by
  decide

/-! ## Universal non-compositionality -/

/-- There *exist* agents and hyperedges such that individual safety
    does not imply compositional safety.
    This upgrades our counterexample from a verified instance to an
    existential theorem — the correct research-paper-level statement. -/
theorem nonCompositionality_exists :
    ∃ (edges : List HyperEdge) (a b : Agent),
      isCapSafe edges a = true ∧
      isCapSafe edges b = true ∧
      isCapSafe edges (compose a b) = false :=
  ⟨demoEdges, webAgent, execAgent,
   webAgent_is_safe, execAgent_is_safe, composedTeam_is_unsafe⟩

end FlowGuard
