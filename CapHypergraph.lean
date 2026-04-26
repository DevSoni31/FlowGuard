import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice

namespace FlowGuard

/-- Finite set of primitive capabilities. -/
inductive Cap where
  | read  : Cap
  | write : Cap
  | exec  : Cap
  | secret : Cap
  deriving DecidableEq

structure HyperEdge where
  premises : Finset Cap
  conclusion : Cap
  deriving DecidableEq

abbrev CapContract := Finset HyperEdge

inductive Reachable (rules : CapContract) (init : Finset Cap) : Cap → Prop where
  | base {c : Cap} : c ∈ init → Reachable rules init c
  | step {edge : HyperEdge} :
      edge ∈ rules →
      (∀ p ∈ edge.premises, Reachable rules init p) →
      Reachable rules init edge.conclusion

def isSafe (rules : CapContract) (init : Finset Cap) (forbidden : Cap) : Prop :=
  ¬ Reachable rules init forbidden

/--
  THEOREM: Non-Compositionality of Safety
  The crown jewel of the FlowGuard core logic.
-/
theorem nonCompositionality :
  ∃ (contractA contractB : CapContract) (init : Finset Cap) (forbidden : Cap),
    isSafe contractA init forbidden ∧
    isSafe contractB init forbidden ∧
    ¬ isSafe (contractA ∪ contractB) init forbidden := by

  -- 1. Define the Counter-Example
  let edgeA : HyperEdge := ⟨{Cap.read}, Cap.write⟩
  let edgeB : HyperEdge := ⟨{Cap.write}, Cap.secret⟩
  let cA : CapContract := {edgeA}
  let cB : CapContract := {edgeB}
  let i : Finset Cap := {Cap.read}
  let f : Cap := Cap.secret

  use cA, cB, i, f

  -- 2. Prove Safety of Agent A
  constructor
  · intro h
    -- We use 'cases' to decompose the Reachable predicate
    induction h with
    | base h_in =>
      simp [i] at h_in -- Secret is not in {Read}
    | step h_rule _ _ =>
      simp [cA] at h_rule
      subst h_rule
      -- Agent A only concludes 'write', so it can't be 'secret'
      simp at *

  -- 3. Prove Safety of Agent B
  constructor
  · intro h
    induction h with
    | base h_in =>
      simp [i] at h_in -- Secret is not in {Read}
    | step h_rule h_pre _ =>
      simp [cB] at h_rule
      subst h_rule
      -- Agent B concludes 'secret', but it needs 'write' first.
      -- Let's show 'write' is unreachable for Agent B.
      have h_write := h_pre Cap.write (by simp)
      cases h_write with
      | base h_in_init =>
        simp [i] at h_in_init -- 'write' is not in {Read}
      | step h_rule_inner _ =>
        simp [cB] at h_rule_inner -- Agent B doesn't have a rule for 'write'

  -- 4. Prove Unsafe Union
  · intro h_safe
    unfold isSafe at h_safe
    apply h_safe
    -- Path: Read -> (edgeA) -> Write -> (edgeB) -> Secret
    apply Reachable.step (edge := edgeB)
    · simp [cA, cB] -- edgeB is in the union
    · intro p hp; simp at hp; subst hp
      apply Reachable.step (edge := edgeA)
      · simp [cA, cB] -- edgeA is in the union
      · intro p' hp'; simp at hp'; subst hp'
        apply Reachable.base; simp [i]

end FlowGuard
