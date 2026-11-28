import Graph189ConeLinkedOrder
import Graph189CriticalConnectivity
import Graph189MinimumCutOrder
import Graph189FourCritical

open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
namespace Graph189LowConnectivityLift
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For vertex connectivity three or four and a nontraceable minimum deletion,
an arbitrary minimum cut either avoids the minimum vertex, allowing a
lift at full second degree, or bounds its degree from below within s−1 of k. -/
theorem minimum_deletion (hc : G.Connected) (z : V) (least : G.degree z=G.minDegree)
    (small : 3≤G.vertexConnectivity) (big : G.vertexConnectivity≤4)
    (degree : 20≤G.secondSmallestDegree)
    (threshold : G.vertexConnectivity=3 ∨ 30≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (room : G.vertexConnectivity < Fintype.card V-1)
    (nontrace : ¬∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian)
    (absent : ¬∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian) :
    (G.vertexConnectivity+2)*(G.secondSmallestDegree-(G.vertexConnectivity+1)+2)-1 ≤ Fintype.card V := by
  classical
  let s := G.vertexConnectivity
  let k := G.secondSmallestDegree
  change (s+2)*(k-(s+1)+2)-1≤Fintype.card V
  change 20≤k at degree
  change 3≤s at small
  change s≤4 at big
  change s=3 ∨ 30≤k at threshold
  by_cases free : ∀ T : Finset V, T.card=s → z∈T → (G.induce {v : V | v∉T}).Connected
  · have conn := completeAt_connectivity_add_one z room free
    have bound := Graph189ConeLinkedOrder.order (completeAt G z) z (l:=s+1) (d:=k)
      (by omega) (by omega) (secondDegree_le_completeAt_minDegree z least) conn
      (fun _ C hC max => Graph189CompletionLinked.minimum_fixed z least C hC max nontrace absent cap
        (by omega) (by change 3*(s+1)≤k+2; omega) (by change 2*(s+1)+2≤k; omega)
        (by change 6≤k; omega))
    exact bound
  · push Not at free
    obtain ⟨T,size,zt,bad⟩ := free
    have living : ∃ v, v∉T := by
      by_contra! all
      have allT := eq_univ_iff_forall.mpr all
      rw [allT,card_univ] at size
      change s<Fintype.card V-1 at room
      omega
    obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T living bad
    have bound := sides.anchor_degree
      (fun U lt => Graph189CutSides.connected_after_smaller_deletion (G:=G) U (lt.trans_eq size))
      (fun v => by have h := cap v; omega) zt
    change k+1≤G.degree z+T.card at bound
    rw [least,size] at bound
    have crit : 3*G.vertexConnectivity<2*(G.minDegree+1) := by change 3*s<_; omega
    obtain ⟨w,conn⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) room crit
    have ord := Graph189ConeLinkedOrder.order (completeAt G w) w (l:=s+1) (d:=G.minDegree)
      (by omega) (by omega) (minDegree_le_completeAt w) conn
      (fun _ C hC max => Graph189CompletionLinkedFour.critical_fixed w C hC max nontrace cap
        (by omega) (by change 3*(s+1)≤k+2; omega) (by omega)
        (by change k+6≤2*G.minDegree; omega) (by omega))
    change (s+2)*(G.minDegree-(s+1)+2)-1≤Fintype.card V at ord
    by_cases tied : k≤G.minDegree
    · have cmp := Nat.mul_le_mul_left (s+2)
        (show k-(s+1)+2≤G.minDegree-(s+1)+2 by omega)
      omega
    exfalso
    have low : G.degree z < G.secondSmallestDegree := by rw [least]; change _<k; omega
    obtain ⟨_,_,_,_,_,_,r,_,_,rmax,_,debit⟩ := sides.low_cut_deficit hc
      (fun U lt => Graph189CutSides.connected_after_smaller_deletion (G:=G) U (lt.trans_eq size))
      (fun v => by have h := cap v; omega) zt low
    change Fintype.card V+k*(k-G.degree z)≤2*k+(k+1)*r at debit
    rw [least] at debit
    rw [size] at rmax
    have upper := debit.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (k+1) rmax) (2*k))
    have ds : k-G.minDegree=1 ∨ k-G.minDegree=2 ∨ k-G.minDegree=3 := by omega
    have bys : s=3 ∨ s=4 := by omega
    rcases bys with h|h <;> rw [h] at ord upper <;>
      rcases ds with d|d|d <;> rw [d] at upper <;> omega

#print axioms minimum_deletion
end Graph189LowConnectivityLift
