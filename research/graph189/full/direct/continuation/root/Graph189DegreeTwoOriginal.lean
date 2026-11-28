import Graph189DegreeTwoDeletion
import Graph189MinimumBondyOrder
import Graph189MinimumCut
import Graph189ConnectivityDegree
import Graph189ModerateConnectivity

open SimpleGraph Finset Graph189UniversalCycle Graph189ExteriorDegreeCycle
namespace Graph189DegreeTwoOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At second-smallest degree at least seven, a two-connected qualifying
graph with a degree-two vertex has a Hamiltonian path at every order. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (conn : 2≤G.vertexConnectivity) (z : V) (degree : G.degree z=2) (large : 7≤G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have upper (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using upper v
  by_cases H : ∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b, p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := H
    exact Graph189DegreeTwoDeletion.traceable hc z degree point large p hp
  by_contra nontrace
  obtain ⟨w,hw⟩ := G.exists_minimal_degree_vertex
  have lm := Graph189CutSides.connectivity_le_degree (G:=G) w
  have zm := G.minDegree_le_degree z
  have zc := Graph189CutSides.connectivity_le_degree (G:=G) z
  have minimum : G.degree z=G.minDegree := by omega
  have maxk := (secondDegree_le_completeAt_minDegree (G:=G) z minimum).trans
    ((completeAt G z).minDegree_le_degree z)
  rw [completeAt_degree_self] at maxk
  have room : G.vertexConnectivity < Fintype.card V-1 := by omega
  have free (T : Finset V) (size : T.card=G.vertexConnectivity) (inside : z∈T) :
      (G.induce {v : V | v∉T}).Connected := by
    by_contra bad
    have survives : ∃ v, v∉T := by
      by_contra! full
      have eq := eq_univ_iff_forall.mpr full
      rw [eq,card_univ] at size
      omega
    obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T survives bad
    have bound := sides.anchor_degree (fun U h => Graph189CutSides.connected_after_smaller_deletion
      (G:=G) U (h.trans_eq size)) upper inside
    omega
  have lift := completeAt_connectivity_add_one z room free
  have lower := minimum_bondy_order z minimum nontrace H point (l:=3) (by decide) (by omega) (by omega)
  change 4*(G.secondSmallestDegree-3+2)-1 ≤ Fintype.card V at lower
  have bound := Graph189LayerCutoff.order_of_small_degree G hc z G.secondSmallestDegree point
    (by rw [degree]; omega)
  rw [degree] at bound
  omega

/-- The moderate two-connected parent case holds for every graph with
second-smallest degree at least twelve, including minimum degree two. -/
theorem traceable_moderate (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (conn : 2≤G.vertexConnectivity)
    (moderate : Fintype.card V ≤ 3*G.secondSmallestDegree+2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases degree : 3≤G.minDegree
  · exact Graph189ModerateConnectivity.traceable hc cap large conn moderate (Or.inl degree)
  obtain ⟨w,hw⟩ := G.exists_minimal_degree_vertex
  have min := Graph189CutSides.connectivity_le_degree (G:=G) w
  exact traceable hc cap conn w (by omega) (by omega)

#print axioms traceable
#print axioms traceable_moderate
end Graph189DegreeTwoOriginal
