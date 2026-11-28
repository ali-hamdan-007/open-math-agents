import Graph189LowConnectivityLift
import Graph189MinimumDeletionReplay

open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189MinimumDegreeCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If minimum degree equals vertex connectivity, a minimum-degree vertex
cannot lie on a minimum separator at k>3κ. The lifted completion order
then exceeds the upper order at this low vertex. -/
theorem traceable (connected : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (same : G.minDegree=G.vertexConnectivity) (three : 3≤G.vertexConnectivity)
    (separated : 3*G.vertexConnectivity<G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
  let s := G.vertexConnectivity
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change 3*s<k at separated
  change 3≤s at three
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have least : G.degree z=G.minDegree := hz.symm
  have degz : G.degree z=s := least.trans same
  obtain ⟨u,ne⟩ := exists_ne z
  have size : k<n := by
    rcases degree_pair (G:=G) u z ne with h|h
    · exact lt_of_le_of_lt h (G.degree_lt_card_verts u)
    · exact lt_of_le_of_lt h (G.degree_lt_card_verts z)
  have room : s<n-1 := by omega
  have point (v : V) : G.distEven v≤k+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    change _≤1+k at h
    omega
  by_contra fail
  by_cases near : ∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := near
    exact fail (Graph189RootedSplice.traceable_of_small_degree_hamiltonian_deletion connected z least
      (by omega) (by change 3*G.degree z<k; omega) point p hp)
  have free (T : Finset V) (ts : T.card=s) (zt : z∈T) :
      (G.induce {v : V | v∉T}).Connected := by
    by_contra bad
    have living : ∃ v, v∉T := by
      by_contra! all
      have allT := eq_univ_iff_forall.mpr all
      rw [allT,card_univ] at ts
      change n=s at ts
      omega
    obtain ⟨A,B,cut⟩ := Graph189CutSides.exists_cutSides_of_disconnected T living bad
    have bound := cut.anchor_degree
      (fun U lt => Graph189CutSides.connected_after_smaller_deletion (G:=G) U (lt.trans_eq ts))
      (fun v => by have h := point v; change G.distEven v≤1+k; omega) zt
    change k+1≤G.degree z+T.card at bound
    omega
  have conn := completeAt_connectivity_add_one z room free
  have lower := Graph189ConeLinkedOrder.order (completeAt G z) z (l:=s+1) (d:=k)
    (by omega) (by omega) (secondDegree_le_completeAt_minDegree z least) conn
    (fun _ C hC max => Graph189CompletionLinked.minimum_fixed z least C hC max fail near point
      (by omega) (by change 3*(s+1)≤k+2; omega) (by change 2*(s+1)+2≤k; omega)
      (by change 6≤k; omega))
  have upper := Graph189LayerCutoff.order_of_small_degree G connected z k point (by omega)
  rw [degz] at upper
  change (s+2)*(k-(s+1)+2)-1≤n at lower
  change n≤1+s+k+s*(k+1-s) at upper
  have h : k-(s+1)+2=k+1-s := by omega
  rw [h,add_mul] at lower
  omega

#print axioms traceable
end Graph189MinimumDegreeCut
