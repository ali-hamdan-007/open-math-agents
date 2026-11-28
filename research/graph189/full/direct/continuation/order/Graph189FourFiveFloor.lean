import Graph189StrictCutDeficit
import Graph189WeightedCriticalOrder
import Graph189UnrestrictedMinimumDeletion

open Finset SimpleGraph Graph189UniversalCycle
namespace Graph189FourFiveFloor
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Charge a possible low vertex once in the critical order bound and k times
in its strict separator wedge. If no minimum cut contains it, complete there. -/
theorem order (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (bad : ¬∃ a b,∃p : G.Walk a b,p.IsHamiltonian)
    (sector : (G.vertexConnectivity=4 ∧ 13≤G.secondSmallestDegree) ∨
      (G.vertexConnectivity=5 ∧ 15≤G.secondSmallestDegree)) :
    let n := Fintype.card V
    let k := G.secondSmallestDegree
    (G.vertexConnectivity=4 → 6*k≤n+20 ∧ (24≤k → 6*k≤n+19)) ∧
      (G.vertexConnectivity=5 → 7*k≤n+31) := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let s := G.vertexConnectivity
  change (s=4 ∧ 13≤k) ∨ (s=5 ∧ 15≤k) at sector
  change (s=4 → 6*k≤n+20 ∧ (24≤k → 6*k≤n+19)) ∧ (s=5 → 7*k≤n+31)
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm 1] using upper v
  have floor := Graph189RotationLinked.base_order bad point (l:=s) (by rcases sector with h|h <;> omega)
    le_rfl (by change 2*s+1≤k; rcases sector with h|h <;> omega)
  change (s+1)*(k-s+2)≤n+1 at floor
  have room : G.vertexConnectivity<n-1 := by
    change s<n-1
    rcases sector with ⟨hs,hk⟩|⟨hs,hk⟩ <;> rw [hs] at floor ⊢ <;> omega
  obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
  have degree := Graph189CutSides.connectivity_le_degree (G:=G) z
  change s≤G.degree z at degree
  by_cases free : ∀T : Finset V,T.card=s → z∈T → (G.induce {v : V | v∉T}).Connected
  · have conn := completeAt_connectivity_add_one z room free
    have del : ¬∃a b,∃p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian := by
      rintro ⟨a,b,p,hp⟩
      exact bad (Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion_unrestricted
        hc z least.symm (by rcases sector with h|h <;> omega)
        (by change 5≤k; rcases sector with h|h <;> omega) point p hp)
    have bound := Graph189RotationLinked.minimum_order z least.symm bad del point (l:=s+1)
      (by rcases sector with h|h <;> omega) conn (by change 2*(s+1)+1≤k; rcases sector with h|h <;> omega)
    change (s+2)*(k-(s+1)+2)-1≤n at bound
    rcases sector with ⟨hs,hk⟩|⟨hs,hk⟩ <;> rw [hs] at bound ⊢ <;> omega
  push Not at free
  obtain ⟨S,size,inside,cut⟩ := free
  have remain : ∃v,v∉S := by
    by_contra! full
    rw [eq_univ_iff_forall.mpr full,card_univ] at size
    change n=s at size
    change s<n-1 at room
    omega
  obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected S remain cut
  have smaller (T : Finset V) (h : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (h.trans_eq size)
  have near := sides.anchor_degree smaller upper inside
  change k+1≤G.degree z+S.card at near
  have weighted := Graph189WeightedCriticalOrder.order bad point (by change 2≤s; rcases sector with h|h <;> omega)
    (by change 2*s+5≤k; rcases sector with h|h <;> omega) room
    (by change 3*s<2*(G.minDegree+1); rcases sector with h|h <;> omega)
    (by change k+6≤2*G.minDegree; rcases sector with h|h <;> omega)
  change (s+1)*k+G.minDegree<n+(s+1)*s at weighted
  by_cases low : G.degree z<k
  swap
  · rcases sector with ⟨hs,hk⟩|⟨hs,hk⟩ <;> rw [hs] at weighted ⊢ <;> omega
  obtain ⟨r,rs,_,debit⟩ := sides.strict_low_cut hc smaller upper inside low
  change n+k*(k-G.degree z)<2*k+(k+1)*r at debit
  have max := Nat.mul_le_mul_left (k+1) (rs.trans_eq size)
  have ident : k*(k-G.degree z)=(k-1)*(k-G.degree z)+(k-G.degree z) := by
    calc
      _ = (k-1+1)*(k-G.degree z) := by rw [Nat.sub_add_cancel (by omega : 1≤k)]
      _ = _ := by ring
  have prod (t : ℕ) (ht : t≤k-G.degree z) := Nat.mul_le_mul_left (k-1) ht
  rcases sector with ⟨hs,hk⟩|⟨hs,hk⟩ <;> rw [hs] at weighted max ⊢
  · have one : k-G.degree z≤1 := by by_contra! h; have := prod 2 (by omega); omega
    have zero (big : 24≤k) : k-G.degree z=0 := by
      by_contra! nz
      have := prod 1 (by omega)
      omega
    exact ⟨fun _ => ⟨by omega,fun big => by have := zero big; omega⟩,by omega⟩
  · have two : k-G.degree z≤2 := by by_contra! h; have := prod 3 (by omega); omega
    omega

end Graph189FourFiveFloor
#print axioms Graph189FourFiveFloor.order
