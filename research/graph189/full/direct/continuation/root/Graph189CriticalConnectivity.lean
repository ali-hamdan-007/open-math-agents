import Graph189Removable
import Graph189CompletionConnectivity

open SimpleGraph Finset
namespace Graph189CriticalConnectivity

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem disconnected {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) :
    ¬(G.induce {v : V | v ∉ S}).Connected := by
  classical
  intro conn
  obtain ⟨x,hx⟩ := sides.left_nonempty
  obtain ⟨y,hy⟩ := sides.right_nonempty
  let T : Set V := {v | v ∉ S}
  have xs : x ∈ T := fun h => Finset.disjoint_left.mp sides.left_cut hx h
  have ys : y ∈ T := fun h => Finset.disjoint_left.mp sides.right_cut hy h
  obtain ⟨p⟩ := conn (⟨x,xs⟩ : T) (⟨y,ys⟩ : T)
  obtain ⟨u,v,hu,hv,step,_⟩ := Graph189CutSides.walk_exits (G := G.induce T)
    (fun z : T => z.val ∈ A) p hx (fun h => Finset.disjoint_left.mp sides.apart h hy)
  rcases sides.cover v.val with ha | hb | hs
  · exact hv ha
  · exact sides.no_cross u.val hu v.val hb step
  · exact v.property hs

/-- Finite critical-connectivity bound, specialized to the pinned graph
invariants. There is a vertex outside every minimum separating deletion. -/
theorem free_vertex (room : G.vertexConnectivity < Fintype.card V - 1)
    (degree : 3*G.vertexConnectivity < 2*(G.minDegree+1)) :
    ∃ z : V, ∀ S : Finset V, S.card = G.vertexConnectivity → z ∈ S →
      (G.induce {v : V | v ∉ S}).Connected := by
  classical
  have parts (S : Finset V) (hs : S.card = G.vertexConnectivity)
      (bad : ¬ (G.induce {v : V | v ∉ S}).Connected) :
      ∃ A B, Graph189CutSides.CutSides G A B S := by
    have survives : ∃ u, u ∉ S := by
      by_contra! full
      have eq := Finset.eq_univ_iff_forall.mpr full
      rw [eq,card_univ] at hs
      omega
    exact Graph189CutSides.exists_cutSides_of_disconnected S survives bad
  have minCut {U W K : Finset V} (cut : Graph189CutSides.CutSides G U W K) :
      G.vertexConnectivity ≤ K.card := by
    by_contra! smaller
    exact disconnected cut (Graph189CutSides.connected_after_smaller_deletion K smaller)
  by_cases existsCut : ∃ A B S : Finset V, S.card = G.vertexConnectivity ∧
      Graph189CutSides.CutSides G A B S
  · obtain ⟨z,free⟩ := Graph189Removable.exists_outside_every_min_cut existsCut minCut degree
    refine ⟨z,?_⟩
    intro S hs hz
    by_contra bad
    obtain ⟨A,B,sides⟩ := parts S hs bad
    exact free sides hs hz
  · refine ⟨Classical.arbitrary V,?_⟩
    intro S hs _
    by_contra bad
    obtain ⟨A,B,sides⟩ := parts S hs bad
    exact existsCut ⟨A,B,S,hs,sides⟩

/-- The critical-vertex step in the order lift. Both connectivities and
the minimum degree are those of the genuine finite graphs. -/
theorem exists_completion (room : G.vertexConnectivity < Fintype.card V - 1)
    (degree : 3*G.vertexConnectivity < 2*(G.minDegree+1)) :
    ∃ z : V, G.vertexConnectivity+1 ≤ (Graph189UniversalCycle.completeAt G z).vertexConnectivity := by
  obtain ⟨z,free⟩ := free_vertex room degree
  exact ⟨z,Graph189UniversalCycle.completeAt_connectivity_add_one z room free⟩

#print axioms free_vertex
#print axioms exists_completion
end Graph189CriticalConnectivity
