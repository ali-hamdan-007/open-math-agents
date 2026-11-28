import Mathlib.Tactic.Linarith

namespace Graph189NineCutDebit

private theorem three_excess {n k e w : ℚ}
    (kp : 0 < k) (nk : 8*k+2 ≤ n) (he : 0 ≤ e) (emax : e ≤ 2*k)
    (width : 2*(n-2*k)+k*e ≤ (k+1)*w)
    (budget : w*(n-2*k-e-2) ≤ k*(k+e)) : 3*e ≤ k := by
  have ew : e ≤ w := by
    apply (le_of_mul_le_mul_left ?_ (by linarith : 0 < k+1))
    nlinarith
  have ww : 0 ≤ w := he.trans ew
  have a := mul_le_mul_of_nonneg_right ew (by linarith : 0 ≤ 4*k)
  have b := mul_le_mul_of_nonneg_left (by linarith : 4*k ≤ n-2*k-e-2) ww
  have e3 : 3*e ≤ k := by
    apply (le_of_mul_le_mul_left ?_ kp)
    nlinarith only [a,b,budget]
  exact e3

/-- At connectivity nine above degree 162, a minimum cut cannot contain the
unique low vertex. Inputs are the unconditional order estimate, the original
root width, opposite-side product, and the two low-on-cut inequalities. -/
theorem no_low_at_nine {n k e w x y d r : ℚ}
    (hk : 163 ≤ k) (base : 10*k-71 ≤ n)
    (he : 0 ≤ e) (emax : e ≤ 2*k)
    (width : 2*(n-2*k)+k*e ≤ (k+1)*w)
    (budget : w*(n-2*k-e-2) ≤ k*(k+e))
    (hx : 0 ≤ x) (side : x ≤ y) (cross : x*(y-k) ≤ 9*k*k)
    (hd : 1 ≤ d) (nine : r = 9 ∨ r ≤ 8)
    (low : k*d ≤ 2*k+(k+1)*r-n)
    (mixed : (r-1)*(k-8) ≤ 10*k-n+x+9+r*(e+8)) : False := by
  have kp : 0 < k := by linarith
  have nk : 8*k+2 ≤ n := by linarith
  have r9 : r = 9 := by
    rcases nine with h | h
    · exact h
    · have kd := mul_le_mul_of_nonneg_left hd kp.le
      have cap := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ k+1)
      nlinarith
  subst r
  have e3 := three_excess kp nk he emax width budget
  have x3 : 3*x ≤ 11*k := by
    by_contra! bigger
    have xx := mul_nonneg hx (sub_nonneg.mpr side)
    have product := mul_nonneg (sub_nonneg.mpr bigger.le)
      (by linarith : 0 ≤ 3*x+8*k)
    nlinarith only [product,xx,cross,sq_pos_of_pos kp]
  linarith

/-- The lifted lower order at nine connectivity contradicts the width for
the entire middle range of degrees. The only discreteness input splits the
integer degree excess between at most seven and at least eight. -/
theorem no_lifted_nine_middle {n k e w : ℚ}
    (hk : 163 ≤ k) (ku : k ≤ 192) (lift : 11*k-89 ≤ n)
    (rooted : n ≤ 3*k+1+k*e) (gap : e ≤ 7 ∨ 8 ≤ e)
    (he : 0 ≤ e) (emax : e ≤ 2*k)
    (width : 2*(n-2*k)+k*e ≤ (k+1)*w)
    (budget : w*(n-2*k-e-2) ≤ k*(k+e)) : False := by
  have kp : 0 < k := by linarith
  have kp1 : 0 < k+1 := by linarith
  have pos := sq_pos_of_pos kp
  have e8 : 8 ≤ e := by
    rcases gap with h | h
    · have t := mul_le_mul_of_nonneg_left h kp.le
      nlinarith
    · exact h
  have e3 := three_excess kp (by linarith) he emax width budget
  have lowA : 81*k/10 ≤ n-2*k-e-2 := by linarith
  have lowB : 169*k/10 ≤ 2*(n-2*k) := by linarith
  have a0 : 0 ≤ n-2*k-e-2 := by linarith
  have ke := mul_nonneg kp.le he
  have b0 : 0 ≤ 169*k/10+k*e := by linarith
  have h1 := mul_le_mul_of_nonneg_right width a0
  have h2 := mul_le_mul_of_nonneg_left budget kp1.le
  have h3 := mul_le_mul_of_nonneg_right lowA b0
  have h4 := mul_le_mul_of_nonneg_left (add_le_add_right lowB (k*e)) a0
  have h5 := mul_le_mul_of_nonneg_right (by linarith : k+1 ≤ 193) pos.le
  have h6 := mul_le_mul_of_nonneg_right (by linarith : k+1 ≤ 101*k/100) ke
  have win := mul_pos (by linarith : 0 < 709*e-5611) pos
  nlinarith only [h1,h2,h3,h4,h5,h6,win]

#print axioms no_low_at_nine
#print axioms no_lifted_nine_middle
end Graph189NineCutDebit
