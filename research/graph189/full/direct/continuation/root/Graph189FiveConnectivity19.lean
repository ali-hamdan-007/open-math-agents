import Graph189WeightedCriticalOrder
import Graph189FiveConnectivity25
import Graph189UnrestrictedMinimumDeletion

open Finset SimpleGraph Graph189UniversalCycle
namespace Graph189FiveConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem no_width {k n e w : ℤ} (left : 19≤k) (right : k≤24)
    (ord : 7*k-30≤n) (ep : 0≤e) (em : e+3≤2*k)
    (ore : n≤3*k+1+k*e) (width : 2*(n-2*k)+k*e≤(k+1)*w)
    (budget : w*(n-2*k-e-2)≤k*(k+e)) : False := by
  have wp : 0≤w := by
    by_contra! neg
    have := mul_neg_of_pos_of_neg (by omega : 0<k+1) neg
    have := mul_nonneg (by omega : 0≤k) ep
    omega
  let b := 7*k-30
  have reduced := (mul_le_mul_of_nonneg_left (by dsimp [b]; omega : b-2*k-e-2≤n-2*k-e-2) wp).trans budget
  have witness : 2*(b-2*k)+k*e≤(k+1)*w := by dsimp [b]; omega
  have base : b≤3*k+1+k*e := ord.trans ore
  dsimp [b] at reduced witness base
  clear ord width budget ore b n
  have emax : e≤45 := by omega
  interval_cases k <;> norm_num at em reduced witness base <;> interval_cases e <;> omega

private theorem lower_five (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (five : G.vertexConnectivity=5) (range : 19≤G.secondSmallestDegree)
    (bad : ¬∃ x y, ∃p : G.Walk x y,p.IsHamiltonian) :
    7*G.secondSmallestDegree≤Fintype.card V+30 := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change 19≤k at range
  change 7*k≤n+30
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using upper v
  have floor := Graph189RotationLinked.base_order bad point (l:=5) (by decide) five.ge (by change 11≤k; omega)
  change 6*(k-5+2)≤n+1 at floor
  have room : G.vertexConnectivity<Fintype.card V-1 := by change _<n-1; omega
  obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
  have degree := Graph189CutSides.connectivity_le_degree (G:=G) z
  have weighted (gap : k≤G.minDegree+4) : 6*k+G.minDegree<n+30 := by
    have h := Graph189WeightedCriticalOrder.order bad point (by omega)
      (by change 2*G.vertexConnectivity+5≤k; omega) room (by omega)
      (by change k+6≤2*G.minDegree; omega)
    rwa [five] at h
  by_cases high : k≤G.minDegree+1
  · have h := weighted (by omega)
    omega
  by_cases free : ∀T : Finset V,T.card=G.vertexConnectivity → z∈T →
      (G.induce {v : V | v∉T}).Connected
  · have conn := completeAt_connectivity_add_one z room free
    have del : ¬∃ a b, ∃p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian := by
      rintro ⟨a,b,p,hp⟩
      exact bad (Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion_unrestricted
        hc z least.symm (by omega) (by change 5≤k; omega) point p hp)
    have bound := Graph189RotationLinked.minimum_order z least.symm bad del point (l:=6) (by decide)
      (by rwa [five] at conn) (by change 13≤k; omega)
    change 7*(k-6+2)-1≤n at bound
    omega
  push Not at free
  obtain ⟨S,size,inside,cut⟩ := free
  have remain : ∃v,v∉S := by
    by_contra! full
    rw [eq_univ_iff_forall.mpr full,card_univ] at size
    change n=G.vertexConnectivity at size
    omega
  obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected S remain cut
  have smaller (T : Finset V) (h : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (h.trans_eq size)
  obtain ⟨_,_,_,_,_,_,r,_,_,rs,deficit,debit⟩ :=
    sides.low_cut_deficit hc smaller upper inside (by change G.degree z<k; omega)
  change k-G.degree z+1≤r at deficit
  change n+k*(k-G.degree z)≤2*k+(k+1)*r at debit
  have low := weighted (by omega)
  have cost := Nat.mul_le_mul_left k (show 2≤k-G.degree z by omega)
  have maximum := Nat.mul_le_mul_left (k+1) (by omega : r≤5)
  have gap := Nat.mul_le_mul_left (k-1) (show 2≤k-G.degree z by omega)
  have identity : k*(k-G.degree z)=(k-1)*(k-G.degree z)+(k-G.degree z) := by
    calc
      _ = (k-1+1)*(k-G.degree z) := by rw [Nat.sub_add_cancel (by omega : 1≤k)]
      _ = _ := by ring
  omega

/-- A five-cut suffices for the original, all-orders traceability conclusion
throughout the previously open degree interval 19 through 24. -/
theorem traceable_ge19 (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (range : 19≤G.secondSmallestDegree) (conn : 5≤G.vertexConnectivity) :
    ∃a b, ∃p : G.Walk a b,p.IsHamiltonian := by
  by_cases big : 25≤G.secondSmallestDegree
  · exact traceable_ge25 hc cap big conn
  by_cases six : 6≤G.vertexConnectivity
  · exact Graph189HighConnectivityQuarter.traceable_six hc cap range (by omega) six
  by_contra bad
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  have ord := lower_five hc cap (by omega) range bad
  change 7*k≤n+30 at ord
  change 19≤k at range
  change ¬25≤k at big
  have ceiling := Graph189ThirdLayerDegreeCeiling.max_degree hc cap (by change 5*k+2<n; omega)
  change G.maxDegree+3≤3*k at ceiling
  obtain ⟨ep,_,ore,width,budget⟩ := Graph189ActualScalarWidth.bounds hc cap bad (by change 4*k+2≤n; omega)
  exact no_width (k:=(k:ℤ)) (n:=(n:ℤ)) (by exact_mod_cast range) (by omega)
    (by omega) ep (by change ((G.maxDegree-k : ℕ):ℤ)+3≤2*(k:ℤ); omega) ore width budget

#print axioms traceable_ge19
end Graph189FiveConnectivity
