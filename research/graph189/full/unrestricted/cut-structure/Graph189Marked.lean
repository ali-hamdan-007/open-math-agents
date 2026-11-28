module
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*}
/-- Adjoin a marker of degree one next to c. -/
@[expose] def marked (G : SimpleGraph V) (c : V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some y => y = c
    | some x, none => x = c
    | some x, some y => G.Adj x y
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    intro x
    cases x
    · exact id
    · exact G.loopless.irrefl _

end Graph189SmallRoot
