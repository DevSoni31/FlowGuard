import Mathlib.Order.Basic

namespace FlowGuard

inductive DataLabel where
  | low
  | medium
  | high
  deriving DecidableEq, Repr

def canFlowTo : DataLabel → DataLabel → Bool
  | .low,    _       => true
  | .medium, .medium => true
  | .medium, .high   => true
  | .high,   .high   => true
  | _,       _       => false

instance : LE DataLabel where
  le a b := canFlowTo a b = true

instance (a b : DataLabel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (canFlowTo a b = true))

structure Labelled (α : Type) where
  value : α
  label : DataLabel
  deriving Repr

theorem high_not_low : ¬ (DataLabel.high ≤ DataLabel.low) := by
  decide

end FlowGuard
