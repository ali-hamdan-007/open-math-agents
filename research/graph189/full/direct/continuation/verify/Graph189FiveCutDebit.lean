import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Graph189FiveCutDebit

/-- Twenty-five times the continuous width residual at minimum order 7k−57;
the third argument of the unscaled residual is the degree excess z/5. -/
private def gap (k z : ℤ) :=
  (25*k-295-z)*(50*k-570+k*z)-5*k*(k+1)*(5*k+z)

private theorem endpoints {k : ℤ} (hk : 46 ≤ k) (ku : k ≤ 58) :
    0 < gap k k ∧ 0 < gap k (10*k) := by
  let t := k-46
  have t0 : 0 ≤ t := by dsimp [t]; omega
  have t12 : 0 ≤ 12-t := by dsimp [t]; omega
  have tt := sq_nonneg t
  have c := mul_nonneg t0 tt
  have u := mul_nonneg t12 tt
  have v := mul_nonneg t12 t0
  constructor
  · have eq : gap k k = -6*t^3+47*t^2+13982*t+127854 := by dsimp [gap,t]; ring
    rw [eq]
    nlinarith only [u,v,t0]
  · have eq : gap k (10*k) = 25*(3*t^3+323*t^2+9740*t+63306) := by dsimp [gap,t]; ring
    rw [eq]
    nlinarith only [c,tt,t0]

private theorem small_excess {k n e : ℤ} (hk : 46 ≤ k) (ku : k ≤ 58)
    (hn : 7*k-57 ≤ n) (he : 0 ≤ e) (h2 : e ≤ 2*k)
    (width : (n-2*k-e-2)*(2*(n-2*k)+k*e) ≤ k*(k+1)*(k+e)) : 5*e < k := by
  have ke := mul_nonneg (show 0 ≤ k by omega) he
  have m := mul_le_mul (show 5*k-59-e ≤ n-2*k-e-2 by omega)
    (show 10*k-114+k*e ≤ 2*(n-2*k)+k*e by omega)
    (show 0 ≤ 10*k-114+k*e by omega) (show 0 ≤ n-2*k-e-2 by omega)
  have g : gap k (5*e) ≤ 0 := by
    dsimp [gap]
    nlinarith only [m,width]
  obtain ⟨gl,gr⟩ := endpoints hk ku
  by_contra! h
  have eqLeft : k ≠ 5*e := by rintro eq; rw [← eq] at g; omega
  have eqRight : 5*e ≠ 10*k := by rintro eq; rw [eq] at g; omega
  have p := mul_pos (show 0 < 10*k-5*e by omega) (show 0 < gap k k-gap k (5*e) by omega)
  have q := mul_pos (show 0 < 5*e-k by omega) (show 0 < gap k (10*k)-gap k (5*e) by omega)
  have c := mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ k by omega)
    (show 0 ≤ 10*k-5*e by omega)) (show 0 ≤ 5*e-k by omega))
    (show 0 ≤ 10*k-k by omega)
  dsimp [gap] at p q
  nlinarith only [p,q,c]

/-- Scalar contradiction for a genuine low vertex on a minimum cut of size five.
The inputs are the lower order, unrounded root width, cross-side product and two
mixed low-cut debits. All variables are integers and the conclusion is uniform. -/
theorem no_low {k n e x y d r : ℤ} (hk : 46 ≤ k) (ku : k ≤ 58)
    (hn : 7*k-57 ≤ n) (he : 0 ≤ e) (h2 : e ≤ 2*k)
    (width : (n-2*k-e-2)*(2*(n-2*k)+k*e) ≤ k*(k+1)*(k+e))
    (hx : 0 ≤ x) (hxy : x ≤ y) (hsum : x+y = n-5) (cross : x*(y-k) ≤ 5*k*k)
    (hd : 1 ≤ d) (hr : r ≤ 5) (low : n+k*d ≤ 2*k+(k+1)*r)
    (mixed : n+(r-1)*(k-4) ≤ 6*k+x+5+r*(e+4)) : False := by
  have kp : 0 < k := by omega
  have se := small_excess hk ku hn he h2 width
  have r5 : r = 5 := by
    by_contra! ne
    have kd := mul_le_mul_of_nonneg_left hd kp.le
    have rc := mul_le_mul_of_nonneg_left (show r ≤ 4 by omega) (show 0 ≤ k+1 by omega)
    nlinarith only [kd,rc,low,hn,hk]
  subst r
  have sq := sq_pos_of_pos kp
  have yy := mul_nonneg hx (sub_nonneg.mpr hxy)
  have x14 : 5*x < 14*k := by
    by_contra! big
    have t := mul_nonneg (show 0 ≤ 5*x-14*k by omega) (show 0 ≤ 5*x+9*k by omega)
    nlinarith only [t,yy,cross,sq]
  have x9 : 5*x ≤ 9*k := by
    by_contra! big
    have t := mul_nonneg (show 0 ≤ 5*x-9*k by omega) (show 0 ≤ 14*k-5*x by omega)
    have t' := mul_nonneg hx (show 0 ≤ 5*(x+y)-28*k by omega)
    nlinarith only [t,t',cross,sq]
  linarith

#print axioms no_low
end Graph189FiveCutDebit
