module

public import Graph189CutH1Assembly
public import Graph189InducedSide
public import Graph189SmallRootClosed
public import Graph189MarkerEndpoint
import all Graph189CutCore

public section

namespace Graph189CutH1
open SimpleGraph Graph189CutCore Graph189InducedSide Graph189SmallRoot
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Every large-order graph in the cut-vertex branch of WOWII Graph 189
has a Hamiltonian path. This is the complete mathematical statement of R2.H1. -/
theorem cut_vertex_case (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    (hcut : ∃ c : V, ¬ (G.induce {v | v ≠ c}).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  apply Graph189CutH1Assembly.h1_of_small_rooted hc hσ horder hcut
  intro c A hA hsize
  have hp := Finset.card_pos.mpr hA.nonempty
  apply small_side_of_induced (k := G.secondSmallestDegree) hA hc (by omega)
    (Graph189CutCore.degree_pair (G := G)) (Graph189CutBounds.two_le_degree hc hσ horder)
  intro hsz hcontact hpair htwo
  apply rooted_of_marked_traceable
  exact marked_trace_at_small_root (sideGraph G c A) (sideRoot c A)
    G.secondSmallestDegree hsz hcontact hpair htwo

#print axioms cut_vertex_case
end Graph189CutH1
