import Mathlib.Tactic.Linarith

namespace Graph189ThirdWidth

/-- A linked-order lower bound at the integer ceiling k/3 forces a quadratic
lower order. All variables here denote mathematical integers. -/
theorem quadratic {k l n : ℤ} (degree : 26≤k)
    (lower : k≤3*l) (upper : 3*l≤k+2) (order : (l+1)*(k-l+2)-1≤n) :
    k*k+5*k≤5*n := by
  let r := 3*l-k
  have small : 0≤r ∧ r≤2 := by dsimp [r]; omega
  have l0 : 0≤l := by omega
  have budget := mul_nonneg l0 small.1
  have rr := mul_nonneg small.1 (sub_nonneg.mpr small.2)
  dsimp [r] at budget rr
  nlinarith only [order,budget,rr,sq_nonneg l,lower,upper,l0]

/-- The genuine signed width constraints cannot coexist with that lower order.
The excess-degree contribution is nonnegative throughout 0≤e≤2k. -/
theorem incompatible {k n e w : ℤ} (degree : 26≤k) (quad : k*k+5*k≤5*n)
    (e0 : 0≤e) (e2 : e≤2*k)
    (lower : 2*(n-2*k)+k*e≤(k+1)*w)
    (upper : w*(n-2*k-e-2)≤k*(k+e)) : False := by
  have k0 : 0<k := by omega
  have six : 6*k≤n := by
    nlinarith only [quad,mul_nonneg (show 0≤k-25 by omega) k0.le]
  have first : 0≤n-2*k-e-2 := by omega
  have W1 := mul_le_mul_of_nonneg_right lower first
  have W2 := mul_le_mul_of_nonneg_left upper (show 0≤k+1 by omega)
  have slope : 0≤(k-2)*n-5*k*k+k := by
    have slope₁ := mul_nonneg (show 0≤k-2 by omega) (sub_nonneg.mpr six)
    have slope₂ := mul_nonneg k0.le (show 0≤k-11 by omega)
    nlinarith only [slope₁,slope₂]
  have monotone := mul_nonneg e0 slope
  have curvature := mul_nonneg (mul_nonneg k0.le e0) (sub_nonneg.mpr e2)
  have base : 2*(n-2*k-2)*(n-2*k)≤k*k*(k+1) := by
    nlinarith only [W1,W2,monotone,curvature]
  have a : k*(k-6)≤5*(n-2*k-2) := by nlinarith only [quad,degree]
  have b : k*(k-6)≤5*(n-2*k) := by nlinarith only [quad,degree]
  have c := mul_le_mul a b (mul_nonneg k0.le (show 0≤k-6 by omega))
    (show 0≤5*(n-2*k-2) by omega)
  have reduced : 2*(k-6)*(k-6)≤25*(k+1) := by
    apply (mul_le_mul_iff_right₀ (mul_pos k0 k0)).mp
    nlinarith only [base,c]
  have growth := mul_nonneg (show 0≤k-26 by omega) (show 0≤2*k+3 by omega)
  nlinarith only [reduced,growth]

#print axioms quadratic
#print axioms incompatible
end Graph189ThirdWidth
