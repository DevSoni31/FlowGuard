import FlowGuard.CapHypergraph
import FlowGuard.InfoFlow
import Mathlib.Tactic

namespace FlowGuard

/-! ## Agent Effects

    Primitive operations an AI agent can perform.
    Return type is indexed by the effect kind.
-/

inductive AgentEffect : Type → Type where
  | webSearch : String → AgentEffect String
  | codeExec  : String → AgentEffect String
  | readDB    : String → AgentEffect String
  | sendEmail : String → String → AgentEffect Unit
  | exfilData : String → AgentEffect Unit

/-! ## Agent Program (free monad)

    Mirrors FileM in Gadgil's LeanLangur exactly.
    `pure` wraps a value; `step` sequences an effect with a continuation.
-/

inductive Prog : Type → Type 1 where
  | pure : α → Prog α
  | step : AgentEffect β → (β → Prog α) → Prog α

/-- Monadic bind: sequential composition -/
def Prog.bind (x : Prog α) (f : α → Prog β) : Prog β :=
  match x with
  | .pure a   => f a
  | .step e k => .step e (fun b => (k b).bind f)

instance : Monad Prog where
  pure  := Prog.pure
  bind  := Prog.bind

/-- Smart constructors -/
def Prog.webSearch (q : String) : Prog String :=
  .step (.webSearch q) .pure

def Prog.codeExec (code : String) : Prog String :=
  .step (.codeExec code) .pure

def Prog.readDB (key : String) : Prog String :=
  .step (.readDB key) .pure

def Prog.sendEmail (addr body : String) : Prog Unit :=
  .step (.sendEmail addr body) .pure

def Prog.exfilData (dest : String) : Prog Unit :=
  .step (.exfilData dest) .pure

/-! ## Capability tag for each effect

    Links each effect back to the Cap type from CapHypergraph.
-/

def effectCap : AgentEffect α → Cap
  | .webSearch _    => Cap.webSearch
  | .codeExec  _    => Cap.codeExec
  | .readDB    _    => Cap.readDB
  | .sendEmail _ _  => Cap.sendEmail
  | .exfilData _    => Cap.exfilData

/-! ## Safety predicate

    Mirrors SafeProg in LeanLangur.
    A program is safe for a given agent contract if:
      · Pure values need no capabilities → always safe
      · A step is safe if the required cap is held and not forbidden,
        AND the continuation is safe for every possible return value
-/

inductive SafeProg (contract : Agent) : Prog α → Prop where
  | pureSafe (a : α) :
      SafeProg contract (.pure a)
  | stepSafe (e : AgentEffect β) (k : β → Prog α)
      (hHolds    : effectCap e ∈ contract.base)
      (hNotForbid : effectCap e ∉ contract.forbidden)
      (hCont     : ∀ b, SafeProg contract (k b)) :
      SafeProg contract (.step e k)

/-! ## Composition safety theorem

    If `x` is safe and every continuation `f a` is safe,
    then the sequential composition `x >>= f` is safe.

    This is the monad-level analogue of flatMapSafe in LeanLangur.
-/

theorem bindSafe
    (contract : Agent)
    (x : Prog α) (f : α → Prog β)
    (hx : SafeProg contract x)
    (hf : ∀ a, SafeProg contract (f a)) :
    SafeProg contract (x.bind f) := by
  induction hx with
  | pureSafe a =>
      exact hf a
  | stepSafe e k hHolds hNotForbid hCont ih =>
      exact SafeProg.stepSafe e _ hHolds hNotForbid (fun b => ih b f hf)

/-! ## Concrete programs -/

/-- A safe program: just does a web search -/
def searchProg : Prog String :=
  Prog.webSearch "Lean 4 tactics"

/-- An unsafe program: searches then exfiltrates the result -/
def exfilProg : Prog Unit :=
  Prog.bind (Prog.webSearch "secret") Prog.exfilData

/-! ## Theorems about concrete programs -/

theorem searchProg_safe :
    SafeProg webAgent searchProg := by
  apply SafeProg.stepSafe
  · decide
  · decide
  · intro b; exact SafeProg.pureSafe b

/-- The exfil program is unsafe: exfilData is forbidden for webAgent -/
theorem exfilProg_unsafe :
    ¬ SafeProg webAgent exfilProg := by
  intro h
  simp only [exfilProg] at h
  cases h with
  | stepSafe e k hHolds hNotForbid hCont =>
      have hBad := hCont "secret"
      cases hBad with
      | stepSafe e2 _ _ hNF2 _ =>
          simp [effectCap, webAgent] at hNF2

end FlowGuard
