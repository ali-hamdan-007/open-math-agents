import Graph189RootWidth
import Graph189RootedTrace
import Graph189MaximumDegree

namespace Graph189WidthInterval
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

def low (k n : ℤ) : ℤ := k + max 0 (-((-(n-3*k-1))/k))
def difference (k n d : ℤ) : ℤ := (n-d-k-2)*(2*(n-2*k)+k*(d-k)) - (k+1)*k*d

private theorem endpoint {k n l d h : ℤ} (hk : 0 ≤ k) (hld : l ≤ d) (hdh : d ≤ h)
    (hf : difference k n d ≤ 0) :
    min (difference k n l) (difference k n h) ≤ 0 := by
  by_cases hl : l = d
  · exact (min_le_left _ _).trans (hl ▸ hf)
  by_cases hh : h = d
  · exact (min_le_right _ _).trans (hh ▸ hf)
  by_contra! hn
  have ha : 0 < difference k n l - difference k n d := by
    have := lt_of_lt_of_le hn (min_le_left _ _)
    omega
  have hb : 0 < difference k n h - difference k n d := by
    have := lt_of_lt_of_le hn (min_le_right _ _)
    omega
  have lhs := mul_pos (show 0 < h-d by omega) ha
  have rhs := mul_pos (show 0 < d-l by omega) hb
  have prod := mul_nonneg (mul_nonneg (mul_nonneg hk (sub_nonneg.mpr hdh))
    (sub_nonneg.mpr hld)) (sub_nonneg.mpr (hld.trans hdh))
  dsimp [difference] at lhs rhs
  nlinarith only [lhs,rhs,prod]

private theorem scalar {k n d : ℕ} (hk : 0 < k) (hkd : k ≤ d) (hd : d ≤ 3*k)
    (hn : 4*k+2 < n) (ore : n ≤ (3+(d-k))*k+1)
    (box : Graph189RootWidth.width n k d * (n-d-k-2) ≤ k*d) :
    low k n ≤ 3*k ∧ min (difference k n (low k n)) (difference k n (3*k)) ≤ 0 := by
  let a := 2*n+k*d-(4*k+k*k)
  have hround : a ≤ (k+1)*Graph189RootWidth.width n k d := by
    have hr := Nat.div_add_mod (a+k) (k+1)
    have hm := Nat.mod_lt (a+k) (by omega : 0 < k+1)
    change (k+1)*Graph189RootWidth.width n k d + (a+k)%(k+1) = a+k at hr
    omega
  have h0 := Nat.mul_le_mul_right (n-d-k-2) hround
  have h1 := Nat.mul_le_mul_left (k+1) box
  have h2 : a*(n-d-k-2) ≤ (k+1)*(k*d) := by nlinarith only [h0,h1]
  have hc : 4*k+k*k ≤ 2*n+k*d := by
    have h3 := Nat.mul_le_mul_left k hkd
    omega
  have hdn : d ≤ n := by omega
  have hkn : k ≤ n-d := by omega
  have h2n : 2 ≤ n-d-k := by omega
  have zz : (a : ℤ)*((n-d-k-2 : ℕ) : ℤ) ≤ ((k+1 : ℕ) : ℤ)*((k*d : ℕ) : ℤ) := by
    exact_mod_cast h2
  dsimp [a] at zz
  push_cast [Nat.cast_sub hc, Nat.cast_sub hdn, Nat.cast_sub hkn, Nat.cast_sub h2n] at zz
  have hf : difference k n d ≤ 0 := by
    dsimp [difference]
    nlinarith only [zz]
  have ho : (n : ℤ) ≤ ((3+(d-k) : ℕ) : ℤ) * (k : ℤ)+1 := by exact_mod_cast ore
  push_cast [Nat.cast_sub hkd] at ho
  have hkz : 0 < (k : ℤ) := by exact_mod_cast hk
  have hdz : (d : ℤ) ≤ 3*(k : ℤ) := by exact_mod_cast hd
  have hkd' : (k : ℤ) ≤ (d : ℤ) := by exact_mod_cast hkd
  have hdiv : -((d : ℤ)-k) ≤ (-((n : ℤ)-3*k-1))/(k : ℤ) := by
    apply (Int.le_ediv_iff_mul_le hkz).mpr
    nlinarith only [ho]
  have hl : low k n ≤ d := by
    unfold low
    have hm : max 0 (-((-((n : ℤ)-3*k-1))/(k : ℤ))) ≤ (d : ℤ)-k :=
      max_le (by omega) (by omega)
    omega
  exact ⟨hl.trans hdz, endpoint hkz.le hl hdz hf⟩

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A nontraceable original Graph 189 input passes the continuous degree-width
test at the two exact endpoints used in the integer projection. -/
theorem necessary_interval (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hn : ¬ ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) :
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    n ≤ 4*k+2 ∨ (low k n ≤ 3*k ∧
      min (difference k n (low k n)) (difference k n (3*k)) ≤ 0) := by
  classical
  dsimp only
  by_cases small : Fintype.card V ≤ 4*G.secondSmallestDegree+2
  · left
    exact_mod_cast small
  right
  obtain ⟨p,q,hpq⟩ := exists_pair_ne V
  have kd : G.secondSmallestDegree ≤ G.maxDegree := by
    rcases degree_pair (G := G) p q hpq with hp | hq
    · exact hp.trans (G.degree_le_maxDegree p)
    · exact hq.trans (G.degree_le_maxDegree q)
  have ore : Fintype.card V ≤ (3+(G.maxDegree-G.secondSmallestDegree))*G.secondSmallestDegree+1 := by
    by_contra! bad
    obtain ⟨z,_,v,path,hp⟩ := Graph189RootedTrace.of_order hc hcap bad
    exact hn ⟨z,v,path,hp⟩
  have cap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hcap
  have hd := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc cap
  have hp := hc.preconnected.degree_pos_of_nontrivial p
  have dp := G.degree_le_maxDegree p
  exact scalar (by omega) kd hd (by omega) ore (Graph189RootWidth.root_width_bound hc hcap)

#print axioms necessary_interval
end Graph189WidthInterval
