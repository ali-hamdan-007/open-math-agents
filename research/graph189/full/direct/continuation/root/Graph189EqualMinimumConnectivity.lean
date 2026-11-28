import Graph189RotationMinOrder
import Graph189DegreeTwoOriginal
import Graph189LowDeletionTraceable

open SimpleGraph Finset Graph189UniversalCycle
namespace Graph189EqualMinimumConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A qualifying two-connected graph with δ=κ=s and k>3s is traceable
at every order. The deleted-vertex and completed-vertex alternatives
use the same original minimum-degree vertex. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (two : 2≤G.vertexConnectivity) (equal : G.minDegree=G.vertexConnectivity)
    (large : 3*G.vertexConnectivity<G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let s := G.vertexConnectivity
  let k := G.secondSmallestDegree
  change 2≤s at two
  change 3*s<k at large
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have minimum := hz.symm
  have degree : G.degree z=s := minimum.trans equal
  by_cases three : 3≤s
  case neg => exact Graph189DegreeTwoOriginal.traceable hc cap two z (by omega) (by omega)
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v≤k+1 := by simpa only [Nat.add_comm] using upper v
  by_cases H : ∃ x y, ∃ q : (G.induce {v : V | v≠z}).Walk x y, q.IsHamiltonian
  · obtain ⟨x,y,q,hq⟩ := H
    exact Graph189ExteriorGap.traceable_of_low_deletion hc z point q hq (by omega) (by omega)
  by_contra bad
  have maxk := (secondDegree_le_completeAt_minDegree (G:=G) z minimum).trans
    ((completeAt G z).minDegree_le_degree z)
  rw [completeAt_degree_self] at maxk
  change k≤Fintype.card V-1 at maxk
  have room : s<Fintype.card V-1 := by omega
  have free (T : Finset V) (sz : T.card=G.vertexConnectivity) (inside : z∈T) :
      (G.induce {u : V | u∉T}).Connected := by
    by_contra cut
    have rem : ∃ v, v∉T := by
      by_contra! full
      have eq := eq_univ_iff_forall.mpr full
      rw [eq,card_univ] at sz
      change Fintype.card V=s at sz
      omega
    obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T rem cut
    have bound := sides.anchor_degree (fun U h => Graph189CutSides.connected_after_smaller_deletion
      (G:=G) U (h.trans_eq sz)) upper inside
    change k+1≤G.degree z+T.card at bound
    change T.card=s at sz
    omega
  have conn := completeAt_connectivity_add_one z room free
  have lb := Graph189RotationLinked.minimum_order z minimum bad H point (l:=s+1) (by omega)
    conn (by change 2*(s+1)+1≤k; omega)
  have ub := Graph189LayerCutoff.order_of_small_degree G hc z k point (by omega)
  rw [degree] at ub
  change (s+1+1)*(k-(s+1)+2)-1≤Fintype.card V at lb
  have pos : 1≤(s+1+1)*(k-(s+1)+2) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  zify [show s+1≤k by omega,show s≤k+1 by omega,pos] at lb ub large
  nlinarith only [lb,ub,large]

#print axioms traceable
end Graph189EqualMinimumConnectivity
