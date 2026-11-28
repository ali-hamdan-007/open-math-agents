module

public import Graph189SmallRoot
public import Graph189RootedClique

public section

namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite side of order at most 2k has a marked Hamilton path if
every pair off the gate contains a high vertex and all such vertices
have at least two neighbors. -/
theorem marked_trace_at_small_root
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (k : ℕ)
    (hsize : Fintype.card V ≤ 2*k) (hc : ∃ u, G.Adj c u)
    (hpair : ∀ u v, u ≠ c → v ≠ c → u ≠ v → k ≤ G.degree u ∨ k ≤ G.degree v)
    (htwo : ∀ u, u ≠ c → 2 ≤ G.degree u) :
    ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian := by
  apply marked_trace_at_small_root_of_finish _ G c k hsize hc hpair htwo
  intro Q A root out contact shape two
  exact Graph189.rootedGateCliqueList A out contact shape two

#print axioms marked_trace_at_small_root
end Graph189SmallRoot
