import Graph189CriticalBondyOrder
import Graph189HighConnectivityQuarter
import Graph189ModerateDeletion
import Graph189MinimumCut

open Finset SimpleGraph
namespace Graph189ModerateConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the moderate range at connectivity two, a minimum degree greater
than (3k+7)/4 already forces a Hamiltonian path. -/
theorem traceable_two (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (two : G.vertexConnectivity=2) (large : 9 ≤ G.secondSmallestDegree)
    (moderate : Fintype.card V ≤ 3*G.secondSmallestDegree+2)
    (dense : 3*G.secondSmallestDegree+7 < 4*G.minDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra nontrace
  have point (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨z,eq⟩ := G.exists_minimal_degree_vertex
  have bigger := G.degree_lt_card_verts z
  have room : G.vertexConnectivity < Fintype.card V-1 := by omega
  have lower := Graph189ArbitraryHalfExterior.critical_bondy_order nontrace point (by omega)
    (by omega) room (by omega)
  rw [two] at lower
  omega

/-- At k≥12 the whole moderate parent case holds at minimum degree at least
three. At minimum degree two the same argument covers every order below 3k. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (large : 12 ≤ G.secondSmallestDegree) (enough : 2 ≤ G.vertexConnectivity)
    (moderate : Fintype.card V ≤ 3*G.secondSmallestDegree+2)
    (range : 3 ≤ G.minDegree ∨ Fintype.card V < 3*G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases conn : 3 ≤ G.vertexConnectivity
  · exact Graph189HighConnectivityQuarter.traceable_moderate hc cap (by omega) conn moderate
  have two : G.vertexConnectivity=2 := by omega
  by_cases dense : 3*G.secondSmallestDegree+7 < 4*G.minDegree
  · exact traceable_two cap two (by omega) moderate dense
  by_contra nontrace
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have minz : G.degree z=G.minDegree := hz.symm
  have degree := Graph189CutSides.connectivity_le_degree (G:=G) z
  by_cases H : ∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b, p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := H
    exact nontrace (Graph189ModerateDeletion.traceable cap (by omega) moderate z minz
      (by omega) (by rwa [minz]) p hp)
  have upper (v : V) : G.distEven v ≤ 1 + G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have maxk := (Graph189UniversalCycle.secondDegree_le_completeAt_minDegree (G:=G) z minz).trans
    ((Graph189UniversalCycle.completeAt G z).minDegree_le_degree z)
  rw [Graph189UniversalCycle.completeAt_degree_self] at maxk
  have room : G.vertexConnectivity < Fintype.card V-1 := by omega
  have free (T : Finset V) (size : T.card=G.vertexConnectivity) (mem : z∈T) :
      (G.induce {v : V | v∉T}).Connected := by
    by_contra bad
    have survives : ∃ v, v∉T := by
      by_contra! full
      have eq := eq_univ_iff_forall.mpr full
      rw [eq,card_univ] at size
      omega
    obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T survives bad
    have bound := sides.anchor_degree (fun U h => Graph189CutSides.connected_after_smaller_deletion
      (G:=G) U (h.trans_eq size)) upper mem
    omega
  have lift := Graph189UniversalCycle.completeAt_connectivity_add_one z room free
  have order := Graph189ExteriorDegreeCycle.minimum_bondy_order z minz nontrace H
    (fun v => by simpa only [Nat.add_comm] using upper v) (l:=3) (by decide)
    (by omega) (by omega)
  change 4*(G.secondSmallestDegree-3+2)-1 ≤ Fintype.card V at order
  omega

#print axioms traceable
#print axioms traceable_two
end Graph189ModerateConnectivity
