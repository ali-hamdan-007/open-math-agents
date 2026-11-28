import Graph189LowMixedCut
import Graph189RootWidth

namespace Graph189CutSides
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At high degree and the counterexample order lower bound, every genuine
minimum nine-cut consists entirely of high vertices. The rounded width
and both low-cut constraints are supplied by the actual graph. -/
theorem no_low_on_minimum_nine_cut (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree) (S : Finset V)
    (disc : ¬(G.induce {u : V | u ∉ S}).Connected)
    (minimum : S.card = G.vertexConnectivity) (nine : S.card = 9)
    (hk : 163 ≤ G.secondSmallestDegree) (base : 10*G.secondSmallestDegree ≤ Fintype.card V+71) :
    ∀ z ∈ S, G.secondSmallestDegree ≤ G.degree z := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let d := G.maxDegree
  let e := d-k
  let w := Graph189RootWidth.width n k d
  let l := n-d-k-2
  change 163 ≤ k at hk
  change 10*k ≤ n+71 at base
  have har : 4*k+2 ≤ n := by omega
  have dmax : d ≤ 3*k := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc cap
  have dmin : k ≤ d := by
    obtain ⟨a,b,ne⟩ := exists_pair_ne V
    rcases degree_pair (G := G) a b ne with h|h
    · exact h.trans (G.degree_le_maxDegree a)
    · exact h.trans (G.degree_le_maxDegree b)
  have de : k+e=d := by dsimp [e]; omega
  have dl : l+d+k+2=n := by dsimp [l]; omega
  have rootCap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree := by
    apply max'_le
    intro y hy
    obtain ⟨v,_,rfl⟩ := mem_image.mp hy
    exact cap v
  have root := Graph189RootWidth.root_width_bound hc rootCap
  change w*l ≤ k*d at root
  let a := 2*n+k*d-(4*k+k*k)
  have hr := Nat.div_add_mod (a+k) (k+1)
  have hm := Nat.mod_lt (a+k) (by omega : 0 < k+1)
  change (k+1)*w+(a+k)%(k+1)=a+k at hr
  have kh := Nat.mul_le_mul_left k dmin
  have big : 4*k+k*k ≤ 2*n+k*d := by omega
  have round : 2*n+k*d ≤ (k+1)*w+4*k+k*k := by dsimp [a] at hr hm; omega
  rw [← de] at round root dl
  have roundQ : 2*(n:ℚ)+(k:ℚ)*(k+e) ≤ (k+1:ℚ)*w+4*(k:ℚ)+k*k := by exact_mod_cast round
  have rootQ : (w:ℚ)*l ≤ (k:ℚ)*(k+e) := by exact_mod_cast root
  have lq : (l:ℚ)+(k+e:ℚ)+k+2=n := by exact_mod_cast dl
  have survive : ∃ u, u ∉ S := by
    by_contra! full
    have h := Finset.eq_univ_iff_forall.mpr full
    rw [h,card_univ] at nine
    change n=9 at nine
    omega
  obtain ⟨A,B,sides⟩ := exists_cutSides_of_disconnected S survive disc
  have smaller (T : Finset V) (hT : T.card < S.card) :=
    connected_after_smaller_deletion (G := G) T (minimum ▸ hT)
  apply sides.no_low_at_nine_of_width hc smaller cap nine hk base (w:ℚ)
  · change 2*((n:ℚ)-2*k)+(k:ℚ)*e ≤ (k+1:ℚ)*w
    nlinarith only [roundQ]
  · change (w:ℚ)*((n:ℚ)-2*k-e-2) ≤ (k:ℚ)*(k+e)
    have eq : (n:ℚ)-2*k-e-2=l := by linarith only [lq]
    rwa [eq]

#print axioms no_low_on_minimum_nine_cut
end Graph189CutSides
