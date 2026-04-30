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

/-- `step` and `closureAux` commute:
    one more `step` after n iterations equals
    n iterations starting from a pre-stepped seed.
    Equivalently: step^n(step(S)) = step(step^n(S)). -/
private lemma step_closureAux_comm
    (n : Nat) (edges : List HyperEdge) (S : Finset Cap) :
    step edges (closureAux n edges S) =
    closureAux n edges (step edges S) := by
  induction n generalizing S with
  | zero => simp [closureAux]
  | succ n ih =>
    simp only [closureAux]
    exact ih (step edges S)

/-- The cardinality of `closureAux` is non-decreasing in the iteration count. -/
private lemma closureAux_card_mono
    (n : Nat) (edges : List HyperEdge) (S : Finset Cap) :
    (closureAux n edges S).card ≤ (closureAux (n + 1) edges S).card :=
  Finset.card_le_card (closureAux_step_subset n edges S)

/-- Every `closureAux` output fits inside `Finset.univ`,
    so its cardinality is bounded by `Fintype.card Cap`. -/
private lemma closureAux_card_le_univ
    (n : Nat) (edges : List HyperEdge) (S : Finset Cap) :
    (closureAux n edges S).card ≤ Fintype.card Cap := by
  have h := Finset.card_le_card (Finset.subset_univ (closureAux n edges S))
  rwa [Finset.card_univ] at h

/-- Once two consecutive iterations are equal, the sequence has stopped forever. -/
private lemma closureAux_stable_of_eq (n : Nat) (edges : List HyperEdge) (S : Finset Cap)
    (h : closureAux (n + 1) edges S = closureAux n edges S) :
    ∀ m, closureAux (n + m) edges S = closureAux n edges S := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ]
    calc
      closureAux (n + m + 1) edges S
        = closureAux (n + m) edges (step edges S) := rfl
      _ = step edges (closureAux (n + m) edges S) := by rw [← step_closureAux_comm]
      _ = step edges (closureAux n edges S) := by rw [ih]
      _ = closureAux n edges (step edges S) := by rw [step_closureAux_comm]
      _ = closureAux (n + 1) edges S := rfl
      _ = closureAux n edges S := h

/-- Auxiliary lemma to manually teach `omega` the pigeonhole principle:
    Either the set strictly grows at every step, or it stabilized early. -/
private lemma closureAux_card_stabilises_aux (n : Nat) (edges : List HyperEdge) (S : Finset Cap) :
    (closureAux n edges S).card ≥ S.card + n ∨
    ∃ k < n, closureAux k edges S = closureAux (k + 1) edges S := by
  induction n with
  | zero =>
    left
    simp only [closureAux]
    omega
  | succ n ih =>
    rcases ih with h_card | ⟨k, hk_lt, hk_eq⟩
    · by_cases h_eq : closureAux n edges S = closureAux (n + 1) edges S
      · right; use n; exact ⟨Nat.lt_succ_self n, h_eq⟩
      · left
        have h_sub := closureAux_step_subset n edges S
        have h_ssub : closureAux n edges S ⊂ closureAux (n + 1) edges S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, h_eq⟩
        have h_card_lt : (closureAux n edges S).card < (closureAux (n + 1) edges S).card :=
          Finset.card_lt_card h_ssub
        omega
    · right; use k; exact ⟨Nat.lt_succ_of_lt hk_lt, hk_eq⟩

/-- The cardinality pump: the sequence must have stabilized by step `Fintype.card Cap`. -/
private lemma closureAux_card_stabilises (edges : List HyperEdge) (S : Finset Cap) :
    closureAux (Fintype.card Cap) edges S =
    closureAux (Fintype.card Cap + 1) edges S := by
  have h_aux := closureAux_card_stabilises_aux (Fintype.card Cap + 1) edges S
  rcases h_aux with h_card | ⟨k, hk_lt, hk_eq⟩
  · have h_max := closureAux_card_le_univ (Fintype.card Cap + 1) edges S
    omega
  · have eq1 : k + (Fintype.card Cap - k) = Fintype.card Cap := by omega
    have eq2 : k + (Fintype.card Cap + 1 - k) = Fintype.card Cap + 1 := by omega
    have h_stable_1 := closureAux_stable_of_eq k edges S hk_eq.symm (Fintype.card Cap - k)
    have h_stable_2 := closureAux_stable_of_eq k edges S hk_eq.symm (Fintype.card Cap + 1 - k)
    rw [eq1] at h_stable_1
    rw [eq2] at h_stable_2
    rw [h_stable_1, h_stable_2]

/-- `capClosure` is an absolute fixed point under `step`. -/
theorem capClosure_is_fixpoint (edges : List HyperEdge) (S : Finset Cap) :
    step edges (capClosure edges S) = capClosure edges S := by
  unfold capClosure
  calc
    step edges (closureAux (Fintype.card Cap) edges S)
      = closureAux (Fintype.card Cap) edges (step edges S) := by rw [step_closureAux_comm]
    _ = closureAux (Fintype.card Cap + 1) edges S := rfl
    _ = closureAux (Fintype.card Cap) edges S := (closureAux_card_stabilises edges S).symm

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

/-! ## Universal non-compositionality -/

/-- The foldl accumulator in `step` is monotonically growing:
    the initial set S is always a subset of the final result.
    This is needed to prove that once a premise is satisfied,
    it remains satisfied as more elements are added. -/
private lemma foldl_mono_accum (edges : List HyperEdge) (S : Finset Cap) :
    S ⊆ List.foldl
      (fun acc e => if e.premises ⊆ acc then insert e.conclusion acc else acc)
      S edges := by
  induction edges generalizing S with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons]
    split_ifs with h
    · exact (Finset.subset_insert _ _).trans (ih _)
    · exact ih _

/-- If edge `e` is in `edges` and its premises are already satisfied
    by the current set `S`, then `e`'s conclusion appears in `step edges S`.
    This is the key bridge: premise satisfaction → conclusion membership. -/
private lemma step_conclusion_mem (e : HyperEdge) (edges : List HyperEdge)
    (S : Finset Cap) (hmem : e ∈ edges) (hprem : e.premises ⊆ S) :
    e.conclusion ∈ step edges S := by
  unfold step
  induction edges generalizing S with
  | nil => simp at hmem
  | cons e' rest ih =>
    simp only [List.foldl_cons, List.mem_cons] at hmem ⊢
    rcases hmem with rfl | hmem'
    · -- e is the head; its premises are satisfied, so it fires immediately
      simp only [hprem, ite_true]
      exact foldl_mono_accum rest _ (Finset.mem_insert_self e.conclusion S)
    · -- e is deeper in the list; the accumulator can only grow, preserving hprem
      split_ifs with h
      · exact ih (insert e'.conclusion S) hmem' (hprem.trans (Finset.subset_insert _ _))
      · exact ih S hmem' hprem
/-- THE UNIVERSAL NON-COMPOSITIONALITY THEOREM

    For ANY edge set and ANY two agents satisfying the structural premises,
    individual safety does not survive composition.

    The three structural premises on the witness edge `e` are:
      (i)  Neither agent alone has all of e's prerequisites
      (ii) Together their bases cover all of e's prerequisites
      (iii) e's conclusion is forbidden by at least one of them

    Under these premises, the composed agent is provably unsafe.
    The counterexample in `nonCompositionality_exists` is one instance;
    this theorem says the phenomenon is generic — it holds for any
    edges and agents that fit the pattern. -/
theorem nonCompositionality_universal :
    ∀ (edges : List HyperEdge) (a b : Agent),
      isCapSafe edges a = true →
      isCapSafe edges b = true →
      (∃ e ∈ edges,
          ¬ (e.premises ⊆ a.base) ∧
          ¬ (e.premises ⊆ b.base) ∧
          e.premises ⊆ a.base ∪ b.base ∧
          e.conclusion ∈ a.forbidden ∪ b.forbidden) →
      isCapSafe edges (compose a b) = false := by
  intro edges a b _ha _hb ⟨e, he_mem, _hna, _hnb, hprem, hforbid⟩
  -- The joint base is exactly (compose a b).base by definition
  -- Step 1: e's premises are satisfied by the closure of the joint base
  have hprem_in_closure : e.premises ⊆ capClosure edges (a.base ∪ b.base) :=
    hprem.trans (capClosure_extensive edges _)
  -- Step 2: therefore e fires on the closure, putting e.conclusion inside it
  have hconc_in_step : e.conclusion ∈ step edges (capClosure edges (a.base ∪ b.base)) :=
    step_conclusion_mem e edges _ he_mem hprem_in_closure
  -- Step 3: the closure is a fixed point, so step doesn't escape it
  rw [capClosure_is_fixpoint] at hconc_in_step
  -- hconc_in_step : e.conclusion ∈ capClosure edges (a.base ∪ b.base)
  -- Step 4: e.conclusion is also forbidden in the composition
  -- (compose a b).forbidden = a.forbidden ∪ b.forbidden by definition
  have hmem_inter : e.conclusion ∈
      capClosure edges (a.base ∪ b.base) ∩ (a.forbidden ∪ b.forbidden) :=
    Finset.mem_inter.mpr ⟨hconc_in_step, hforbid⟩
  -- Step 5: the intersection is nonempty, so the cardinality is positive
  have hpos : 0 < (capClosure edges (a.base ∪ b.base) ∩
      (a.forbidden ∪ b.forbidden)).card :=
    Finset.card_pos.mpr ⟨e.conclusion, hmem_inter⟩
  -- Step 6: unfold isCapSafe and compose to expose the boolean expression
  simp only [isCapSafe, emergent, compose]
  -- Goal: (capClosure edges (a.base ∪ b.base) ∩ (a.forbidden ∪ b.forbidden)).card == 0 = false
  have hne : (capClosure edges (a.base ∪ b.base) ∩
      (a.forbidden ∪ b.forbidden)).card ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hpos
  simp [hne]

end FlowGuard
