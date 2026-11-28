import Graph189MinimumCutOrder
import Graph189CriticalBondyOrder
import Graph189ConnectivityDegree

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189LowAnchorOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If a minimum separator contains the unique low vertex, its incidence
bound is incompatible with the removable-vertex order bound for
k ≥ s²+3s+2. This includes all orders at a two-cut for k≥12, at a
three-cut for k≥20, and at a four-cut for k≥30. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (two : 2≤G.vertexConnectivity)
    (large : G.vertexConnectivity^2+3*G.vertexConnectivity+2≤G.secondSmallestDegree)
    (S : Finset V) (size : S.card=G.vertexConnectivity)
    (cuts : ¬(G.induce {u : V | u∉S}).Connected)
    {z : V} (inside : z∈S) (low : G.degree z<G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra bad
  let k := G.secondSmallestDegree
  let s := G.vertexConnectivity
  let f := G.degree z
  let n := Fintype.card V
  change 2≤s at two
  change s^2+3*s+2≤k at large
  change S.card=s at size
  change f<k at low
  have big : 4*s+1≤k := by nlinarith only [large,two,Nat.le_mul_self s]
  have upper (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have minimum : G.minDegree=f := by
    obtain ⟨w,hw⟩ := G.exists_minimal_degree_vertex
    by_cases same : z=w
    · subst w
      exact hw
    rcases degree_pair (G:=G) z w same with h|h
    · omega
    have := G.minDegree_le_degree z
    change G.minDegree≤f at this
    omega
  have connect := Graph189CutSides.connectivity_le_degree (G:=G) z
  have card := G.degree_lt_card_verts z
  change s≤f at connect
  change f<n at card
  have remain : ∃ v, v∉S := by
    by_contra! full
    have eq := eq_univ_iff_forall.mpr full
    rw [eq,card_univ] at size
    change n=s at size
    omega
  obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected S remain cuts
  have smaller (T : Finset V) (ht : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (ht.trans_eq size)
  obtain ⟨_,_,_,_,_,_,r,_,_,hs,deficit,debit⟩ := sides.low_cut_deficit hc smaller upper inside low
  change k-f+1≤r at deficit
  change n+k*(k-f)≤2*k+(k+1)*r at debit
  rw [size] at hs
  have widen := Nat.mul_le_mul_left (k+1) hs
  have order := Graph189ArbitraryHalfExterior.critical_bondy_order bad
    (fun v => by simpa only [Nat.add_comm] using upper v) two big
    (by change s<n-1; omega) (by rw [minimum]; change k+2*s+2≤2*f; omega)
  rw [minimum] at order
  change (s+2)*(f-(s+1)+2)-1≤n at order
  have fs : s+1≤f := by omega
  have pos : 1≤(s+2)*(f-(s+1)+2) := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact Nat.mul_ne_zero (by omega) (by omega)
  zify [fs,pos,low.le] at large deficit debit order widen
  have gain := mul_nonneg (show 0≤(k:ℤ)-s-2 by omega) (show 0≤(k:ℤ)-f-1 by omega)
  nlinarith only [large,debit,order,widen,gain]

#print axioms traceable
end Graph189LowAnchorOriginal
