module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import all Graph189CutCore

public section

namespace Graph189CutInterface
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the large-order cut-vertex branch of WOWII Graph 189, deleting a cut
vertex separates the graph into exactly two connected components. -/
theorem components_after_cut_eq_two (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V) {c : V}
    (hcut : ¬ (G.induce {v | v ≠ c}).Connected) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2 :=
  Graph189CutCore.components_after_cut_eq_two hc hσ horder hcut

#print axioms components_after_cut_eq_two
end Graph189CutInterface
