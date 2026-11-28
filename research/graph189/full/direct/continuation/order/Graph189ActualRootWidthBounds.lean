import Graph189RootWidth
import Graph189MaximumDegree
import Mathlib.Tactic.Linarith

namespace Graph189RootWidth
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Convert the original graph's rounded-width estimate at its actual maximum
degree into the integer polynomial evaluated by the finite cut constraints. -/
theorem continuous_at_actual_degree (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (har : 4*G.secondSmallestDegree+2 ≤ Fintype.card V) :
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    let e : ℤ := (G.maxDegree-G.secondSmallestDegree : ℕ)
    (n-2*k-e-2)*(2*(n-2*k)+k*e) ≤ k*(k+1)*(k+e) := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let d := G.maxDegree
  let e := d-k
  let w := width n k d
  let l := n-d-k-2
  change 4*k+2 ≤ n at har
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
  have root := root_width_bound hc rootCap
  change w*l ≤ k*d at root
  let a := 2*n+k*d-(4*k+k*k)
  have hr := Nat.div_add_mod (a+k) (k+1)
  have hm := Nat.mod_lt (a+k) (by omega : 0 < k+1)
  change (k+1)*w+(a+k)%(k+1)=a+k at hr
  have kh := Nat.mul_le_mul_left k dmin
  have big : 4*k+k*k ≤ 2*n+k*d := by omega
  have round : 2*n+k*d ≤ (k+1)*w+4*k+k*k := by dsimp [a] at hr hm; omega
  rw [← de] at round root dl
  have roundZ : 2*(n:ℤ)+(k:ℤ)*(k+e) ≤ (k+1:ℤ)*w+4*(k:ℤ)+k*k := by exact_mod_cast round
  have rootZ : (w:ℤ)*l ≤ (k:ℤ)*(k+e) := by exact_mod_cast root
  have lz : (l:ℤ)+(k+e:ℤ)+k+2=n := by exact_mod_cast dl
  have left : (n:ℤ)-2*k-e-2=l := by omega
  change ((n:ℤ)-2*k-e-2)*(2*((n:ℤ)-2*k)+(k:ℤ)*e) ≤ (k:ℤ)*(k+1)*(k+e)
  rw [left]
  have mul₁ := mul_le_mul_of_nonneg_left roundZ (show 0 ≤ (l:ℤ) by positivity)
  have mul₂ := mul_le_mul_of_nonneg_left rootZ (show 0 ≤ (k+1:ℤ) by positivity)
  nlinarith only [mul₁,mul₂]

#print axioms continuous_at_actual_degree
end Graph189RootWidth
