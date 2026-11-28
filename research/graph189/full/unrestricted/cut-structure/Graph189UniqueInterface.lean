module

public import Graph189CutInterface
public import Graph189CutUnique
import all Graph189CutCore

public section

namespace Graph189UniqueInterface
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A cut vertex is unique under the large-order Graph 189 assumptions. -/
theorem cut_vertices_equal (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    {c d : V} (hcutc : ¬ (G.induce {v | v ≠ c}).Connected)
    (hcutd : ¬ (G.induce {v | v ≠ d}).Connected) : c = d :=
  Graph189CutUnique.cut_vertices_equal hc hσ horder (Graph189CutCore.degree_pair (G := G)) hcutc hcutd

/-- A cut in the R2.H1 branch consists of a unique separating vertex.
Deleting it leaves exactly two connected components. -/
theorem unique_cut_with_two_components (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    (hcut : ∃ c : V, ¬ (G.induce {v | v ≠ c}).Connected) :
    ∃! c : V, ¬ (G.induce {v | v ≠ c}).Connected ∧
      Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2 := by
  obtain ⟨c,hcCut⟩ := hcut
  exact ⟨c,⟨hcCut,Graph189CutInterface.components_after_cut_eq_two hc hσ horder hcCut⟩,
    fun d hd => cut_vertices_equal hc hσ horder hd.1 hcCut⟩

#print axioms unique_cut_with_two_components
end Graph189UniqueInterface
