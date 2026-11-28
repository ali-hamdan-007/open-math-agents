import Mathlib.Tactic.Linarith

namespace Graph189WidthWindows

def first (m q e : ℤ) : ℤ := q-2*m-4*(e+2)
def second (m q e : ℤ) : ℤ := 2*q-4*m+m*e
def debit (m q H e : ℤ) : ℤ :=
  first m q e * second m q e - (m*m*(H+1+e)+4*m*e)

/-- Strict positivity at each endpoint of the concave width difference is
enough at every intermediate degree excess. -/
private theorem concave {m q H L U E : ℤ} (hm : 0 ≤ m) (hL : L ≤ E) (hU : E ≤ U)
    (hl : 0 < debit m q H L) (hu : 0 < debit m q H U) : 0 < debit m q H E := by
  rcases eq_or_lt_of_le hL with he|hle
  · simpa [← he] using hl
  rcases eq_or_lt_of_le hU with he|hue
  · simpa [he] using hu
  by_contra! hn
  have ha := mul_pos (sub_pos.mpr hue) (sub_pos.mpr (hn.trans_lt hl))
  have hb := mul_pos (sub_pos.mpr hle) (sub_pos.mpr (hn.trans_lt hu))
  have hc := mul_nonneg (mul_nonneg (mul_nonneg hm (sub_nonneg.mpr hU))
    (sub_nonneg.mpr hL)) (sub_nonneg.mpr (hL.trans hU))
  dsimp [debit, first, second] at ha hb
  nlinarith only [ha,hb,hc]

/-- Certify one complete window of degrees, with L≤k≤H and q/(4L) as
the uniform lower order ratio. E₀ is an integer lower bound for the actual
excess obtained by retaining the strict last unit of the rooted wedge. -/
theorem window_impossible {k n e L H q E₀ : ℤ}
    (hL : 0 < L) (hlk : L ≤ k) (hkH : k ≤ H)
    (he : 0 ≤ e) (heu : e ≤ 2*k)
    (horder : q*k ≤ (4*L)*n)
    (hore : n ≤ 3*k+1+k*e)
    (hwidth : (n-2*k-e-2)*(2*(n-2*k)+k*e) ≤ k*(k+1)*(k+e))
    (hefloor : (4*L)*(E₀-1) < q-3*(4*L)-4)
    (hfirst : 0 ≤ first (4*L) q (2*H))
    (hsecond : 0 ≤ second (4*L) q E₀)
    (hgoodL : 0 < debit (4*L) q H E₀)
    (hgoodH : 0 < debit (4*L) q H (2*H)) : False := by
  let m := 4*L
  change q*k ≤ m*n at horder
  have hm : 0 < m := by dsimp [m]; omega
  have hk : 0 < k := hL.trans_le hlk
  have hmk : m ≤ 4*k := by dsimp [m]; omega
  have hscale := mul_le_mul_of_nonneg_left hore hm.le
  have hround : q-3*m-4 ≤ m*e := by
    apply (mul_le_mul_iff_right₀ hk).mp
    nlinarith only [horder,hscale,hmk]
  have hlo : E₀ ≤ e := by
    by_contra! hh
    have hh1 : e ≤ E₀-1 := by omega
    have hh2 := mul_le_mul_of_nonneg_left hh1 hm.le
    change m*(E₀-1) < q-3*m-4 at hefloor
    omega
  have hupper : e ≤ 2*H := by omega
  have hpos := concave hm.le hlo hupper hgoodL hgoodH
  have ha : 0 ≤ first m q e := by
    change 0 ≤ q-2*m-4*(2*H+2) at hfirst
    dsimp [first]; omega
  have hb : 0 ≤ second m q e := by
    change 0 ≤ 2*q-4*m+m*E₀ at hsecond
    have hsub := mul_le_mul_of_nonneg_left hlo hm.le
    dsimp [second]; omega
  have hfactor := mul_nonneg (sub_nonneg.mpr hmk) (by omega : 0 ≤ e+2)
  have hA : k*first m q e ≤ m*(n-2*k-e-2) := by
    dsimp [first]; nlinarith only [horder,hfactor]
  have hB : k*second m q e ≤ m*(2*(n-2*k)+k*e) := by
    dsimp [second]; nlinarith only [horder]
  have hAB := mul_le_mul hA hB (mul_nonneg hk.le hb) ((mul_nonneg hk.le ha).trans hA)
  have hw := mul_le_mul_of_nonneg_left hwidth (sq_nonneg m)
  have hdiff₁ := mul_nonneg (mul_nonneg (sq_nonneg k) (sq_nonneg m)) (sub_nonneg.mpr hkH)
  have hdiff₂ := mul_nonneg (mul_nonneg (mul_nonneg hk.le hm.le) he) (sub_nonneg.mpr hmk)
  have hneg : first m q e*second m q e ≤ m*m*(H+1+e)+4*m*e := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hk)).mp
    nlinarith only [hAB,hw,hdiff₁,hdiff₂]
  dsimp [debit] at hpos
  omega

end Graph189WidthWindows

#print axioms Graph189WidthWindows.window_impossible
