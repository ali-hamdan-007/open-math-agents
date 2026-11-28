import Mathlib.Tactic.Linarith

namespace Graph189InfiniteTail

/-- A fully cancelled width at a maximum-degree root gives a square bound on
the order divided by the second degree. All variables are rational, so that a
graph can supply x = n/k without rounding. -/
theorem square_order_bound {n k e x : ℚ}
    (hk : 1 ≤ k) (he : 0 ≤ e) (hemax : e ≤ 2*k) (hn : n=k*x)
    (hroot : n ≤ 3*k+1+k*e)
    (hwidth : (n-2*k-e-2)*(2*(n-2*k)+k*e) ≤ k*(k+1)*(k+e))
    (hx : 9 ≤ x) : 3*(x-9)^2 ≤ k+1 := by
  subst n
  have hk0 : 0 < k := by linarith
  have hemin : x-4 ≤ e := (mul_le_mul_iff_right₀ hk0).mp (by nlinarith only [hroot, hk])
  have hfirst : k*(x-7) ≤ k*x-2*k-e-2 := by nlinarith only [hemax, hk]
  have hw : 0 ≤ 2*x-4+e := by linarith
  have hprod : (k*x-2*k-e-2)*(2*x-4+e) ≤ (k+1)*(k+e) := by
    apply (mul_le_mul_iff_right₀ hk0).mp
    nlinarith only [hwidth]
  have hrhs := mul_nonneg (sub_nonneg.mpr hk) he
  have hleft := mul_le_mul_of_nonneg_right hfirst hw
  have hbase : (x-7)*(2*x-4+e) ≤ k+1+2*e := by
    apply (mul_le_mul_iff_right₀ hk0).mp
    nlinarith only [hleft, hprod, hrhs]
  have hmore := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hemin)
  nlinarith only [hbase, hmore, hx]

/-- The graph inequalities rule out the infinite connectivity tail. The last
two premises are conditional so that the high-order and removable-vertex
bounds are only used in their proven degree and order ranges. -/
theorem connectivity_lt_100 {s k n : ℚ}
    (hk : 3*s < k)
    (horder : (s+1)*(k-s+2)-1 ≤ n)
    (hside : (n-2*k-1)*(k-s) ≤ s*k*k)
    (hsquare : 9 ≤ n/k → 3*(n/k-9)^2 ≤ k+1)
    (hbridge : 4*s ≤ k → 4*n < k*(k-1) →
      (s+2)*(k-2*s+2)-1 ≤ n)
    (hcut : 6*(s-1)<k →
      (s-2)*(n-2*s-3) < ((s+1)*(s-2)+3)*k) :
    s < 100 := by
  by_contra! hs
  have hs0 : 0 ≤ s := by linarith
  have hk0 : 0 < k := by linarith
  have hsquare100 := mul_nonneg hs0 (sub_nonneg.mpr hs)
  let x := n/k
  have hnx : n=x*k := (div_mul_cancel₀ n hk0.ne').symm
  have htwo : 2*s/3 ≤ x := by
    apply (mul_le_mul_iff_left₀ hk0).mp
    have hd := mul_nonneg hs0 (sub_nonneg.mpr hk.le)
    nlinarith only [horder, hnx, hd, hk0, hs0]
  have hx9 : 9 ≤ x := by linarith
  have hsq : 3*(x-9)^2 ≤ k+1 := hsquare hx9
  by_cases hdeg : k < 25*s
  · have hasq := mul_self_le_mul_self
        (by linarith : (0:ℚ) ≤ s/2) (by linarith : s/2 ≤ x-9)
    nlinarith only [hsquare100, hasq, hsq, hdeg, hs]
  · have h25 : 25*s ≤ k := le_of_not_gt hdeg
    have h24 : 24*s/25 ≤ x := by
      apply (mul_le_mul_iff_left₀ hk0).mp
      have hd := mul_nonneg hs0 (sub_nonneg.mpr h25)
      nlinarith only [horder, hnx, hd, hk0, hs0]
    have hup : n ≤ (2*s+3)*k := by
      by_contra! hn
      have hroot : 2*s*k < n-2*k-1 := by nlinarith only [hn, hk, hs]
      have hm := mul_lt_mul_of_pos_right hroot (by linarith : 0 < k-s)
      have hx := mul_nonneg (mul_nonneg hs0 hk0.le) (by linarith : 0 ≤ k-2*s)
      nlinarith only [hm, hx, hside]
    have hgap := mul_lt_mul_of_pos_right (by linarith : 4*(2*s+3) < k-1) hk0
    have hsmall : 4*n < k*(k-1) := by nlinarith only [hgap, hup]
    have hlow := hbridge (by linarith) hsmall
    have hhigh := hcut (by linarith)
    have hm := mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ s-2)
    have hfold : (s-5)*k < (2*s^2+4*s)*(s-2) := by nlinarith only [hm, hhigh]
    have hpoly : (2*s^2+4*s)*(s-2) < (s-5)*(2*s^2+11*s) := by
      nlinarith only [mul_pos (by linarith : 0 < s) (by linarith : 0<s-47)]
    have hkmax := (mul_lt_mul_iff_right₀ (by linarith : 0 < s-5)).mp (hfold.trans hpoly)
    have hasq := mul_self_le_mul_self
        (by linarith : (0:ℚ) ≤ 6*s/7) (by linarith : 6*s/7 ≤ x-9)
    nlinarith only [hsquare100, hasq, hsq, hkmax, hs]

/-- The other unbounded coordinate of the finite search has a uniform open
upper bound at each remaining connectivity. -/
theorem degree_lt_cutoff {s k n : ℚ} (hs : 5 ≤ s)
    (hbridge : 4*s ≤ k → 4*n < k*(k-1) →
      (s+2)*(k-2*s+2)-1 ≤ n)
    (hcut : 6*(s-1)<k → 2*n < (2*s+3)*k+4*s+4) :
    k < 4*s^2+8*s-2 := by
  by_contra! hk
  have hkbound : 4*s+11 ≤ k := by nlinarith [sq_nonneg s]
  have hhigh := hcut (by nlinarith [sq_nonneg s])
  have hmul := mul_nonneg (by linarith : (0:ℚ) ≤ k) (sub_nonneg.mpr hkbound)
  have hsmall : 4*n < k*(k-1) := by nlinarith only [hhigh, hmul, hkbound, hs]
  have hlow := hbridge (by linarith) hsmall
  nlinarith only [hhigh, hlow, hk]

/-- The unbounded parameters of a counterexample lie inside the exact open
rectangle used by the finite replay. The width hypotheses refer directly to
the actual width w at a maximum-degree root. -/
theorem finite_rectangle_of_width {s k n e w : ℚ}
    (hs : 5 ≤ s) (hk : 3*s < k) (he : 0 ≤ e) (hemax : e ≤ 2*k)
    (hroot : n ≤ 3*k+1+k*e)
    (hwlo : 2*(n-2*k)+k*e ≤ (k+1)*w)
    (hwhi : w*(n-2*k-e-2) ≤ k*(k+e))
    (horder : (s+1)*(k-s+2)-1 ≤ n)
    (hside : (n-2*k-1)*(k-s) ≤ s*k*k)
    (hbridge : 4*s ≤ k → 4*n < k*(k-1) →
      (s+2)*(k-2*s+2)-1 ≤ n)
    (hcut1 : 6*(s-1)<k → 2*n < (2*s+3)*k+4*s+4)
    (hcut2 : 6*(s-1)<k →
      (s-2)*(n-2*s-3) < ((s+1)*(s-2)+3)*k) :
    s < 100 ∧ k < 4*s^2+8*s-2 := by
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hfactor : 0 ≤ n-2*k-e-2 := by
    have hleft := mul_nonneg (by linarith : 0 ≤ s-3) (sub_nonneg.mpr hk.le)
    have hsquare := mul_nonneg (by linarith : 0 ≤ s) (sub_nonneg.mpr hs)
    nlinarith only [horder, hemax, hleft, hsquare, hs]
  have h₁ := mul_le_mul_of_nonneg_left hwlo hfactor
  have h₂ := mul_le_mul_of_nonneg_left hwhi (by linarith : 0 ≤ k+1)
  have hwidth : (n-2*k-e-2)*(2*(n-2*k)+k*e) ≤ k*(k+1)*(k+e) := by
    nlinarith only [h₁,h₂]
  have hnx : n=k*(n/k) := by rw [mul_comm, div_mul_cancel₀ n hk0.ne']
  exact ⟨connectivity_lt_100 hk horder hside
    (square_order_bound hk1 he hemax hnx hroot hwidth) hbridge hcut2,
    degree_lt_cutoff hs hbridge hcut1⟩

end Graph189InfiniteTail

#print axioms Graph189InfiniteTail.square_order_bound
#print axioms Graph189InfiniteTail.connectivity_lt_100
#print axioms Graph189InfiniteTail.degree_lt_cutoff

#print axioms Graph189InfiniteTail.finite_rectangle_of_width
