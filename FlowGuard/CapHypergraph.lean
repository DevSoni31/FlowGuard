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

end FlowGuard
