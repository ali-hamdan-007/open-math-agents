import PellSeedCertificates
import TupleLogReduction
import TupleLogBridge

namespace TupleBDCertificates

open PellLogCertificates PellSeedCertificates

private def Enclosed (x : ℝ) (lo hi : ℚ) : Prop := (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)

private theorem Enclosed.sub {x y : ℝ} {xl xh yl yh : ℚ}
    (hx : Enclosed x xl xh) (hy : Enclosed y yl yh) :
    Enclosed (x - y) (xl - yh) (xh - yl) := by
  unfold Enclosed at *
  push_cast
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

private theorem Enclosed.div {x y : ℝ} {xl xh yl yh lo hi : ℚ}
    (hx : Enclosed x xl xh) (hy : Enclosed y yl yh) (hy₀ : 0 < yl)
    (hl₁ : lo * yl ≤ xl) (hl₂ : lo * yh ≤ xl)
    (hh₁ : xh ≤ hi * yl) (hh₂ : xh ≤ hi * yh) :
    Enclosed (x / y) lo hi := by
  unfold Enclosed at *
  have hy₀' : (0 : ℝ) < (yl : ℝ) := by exact_mod_cast hy₀
  have hypos : 0 < y := hy₀'.trans_le hy.1
  have hl₁' : (lo : ℝ) * (yl : ℝ) ≤ (xl : ℝ) := by exact_mod_cast hl₁
  have hl₂' : (lo : ℝ) * (yh : ℝ) ≤ (xl : ℝ) := by exact_mod_cast hl₂
  have hh₁' : (xh : ℝ) ≤ (hi : ℝ) * (yl : ℝ) := by exact_mod_cast hh₁
  have hh₂' : (xh : ℝ) ≤ (hi : ℝ) * (yh : ℝ) := by exact_mod_cast hh₂
  constructor
  · apply (le_div_iff₀ hypos).mpr
    by_cases h : 0 ≤ (lo : ℝ)
    · exact (mul_le_mul_of_nonneg_left hy.2 h).trans (hl₂'.trans hx.1)
    · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge h)).trans (hl₁'.trans hx.1)
  · apply (div_le_iff₀ hypos).mpr
    by_cases h : 0 ≤ (hi : ℝ)
    · exact hx.2.trans (hh₁'.trans (mul_le_mul_of_nonneg_left hy.1 h))
    · exact hx.2.trans (hh₂'.trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge h)))

private def endpoint (p : ℕ) : ℚ := 2 * ((p : ℚ) / denominator)

private theorem endpoint_cast (p : ℕ) :
    (endpoint p : ℝ) = 2 * ((p : ℝ) / denominator) := by
  simp only [endpoint, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_natCast]

/-- Coefficient of the first Pell index after normalization. -/
noncomputable def theta : ℝ := Real.log (2 + Real.sqrt 3) / Real.log (3 + Real.sqrt 8)

/-- The normalized shift in the chosen second Pell orbit. -/
noncomputable def phi (second : Bool) : ℝ :=
  Real.log ((1 + 1 / Real.sqrt 3) / TupleLogBridge.eightSeed second) /
    Real.log (3 + Real.sqrt 8)

private theorem vLog : Enclosed (Real.log (3 + Real.sqrt 8))
    (endpoint threeSqrtEightLogLower) (endpoint threeSqrtEightLogUpper) := by
  simpa only [Enclosed, endpoint_cast] using threeSqrtEight

private theorem vLogPositive : 0 < endpoint threeSqrtEightLogLower := by decide +kernel

private theorem theta_of_bounds {lo hi : ℚ}
    (hl₁ : lo * endpoint threeSqrtEightLogLower ≤ endpoint twoSqrtThreeLogLower)
    (hl₂ : lo * endpoint threeSqrtEightLogUpper ≤ endpoint twoSqrtThreeLogLower)
    (hh₁ : endpoint twoSqrtThreeLogUpper ≤ hi * endpoint threeSqrtEightLogLower)
    (hh₂ : endpoint twoSqrtThreeLogUpper ≤ hi * endpoint threeSqrtEightLogUpper) :
    Enclosed theta lo hi := by
  have hu : Enclosed (Real.log (2 + Real.sqrt 3))
      (endpoint twoSqrtThreeLogLower) (endpoint twoSqrtThreeLogUpper) := by
    simpa only [Enclosed, endpoint_cast] using twoSqrtThree
  exact hu.div vLog vLogPositive hl₁ hl₂ hh₁ hh₂

private def seedLower (second : Bool) :=
  if second then endpoint seedSecondLogLower else endpoint seedFirstLogLower

private def seedUpper (second : Bool) :=
  if second then endpoint seedSecondLogUpper else endpoint seedFirstLogUpper

private theorem phi_of_bounds (second : Bool) {lo hi : ℚ}
    (hl₁ : lo * endpoint threeSqrtEightLogLower ≤ endpoint seedThreeLogLower - seedUpper second)
    (hl₂ : lo * endpoint threeSqrtEightLogUpper ≤ endpoint seedThreeLogLower - seedUpper second)
    (hh₁ : endpoint seedThreeLogUpper - seedLower second ≤ hi * endpoint threeSqrtEightLogLower)
    (hh₂ : endpoint seedThreeLogUpper - seedLower second ≤ hi * endpoint threeSqrtEightLogUpper) :
    Enclosed (phi second) lo hi := by
  have hs : Enclosed (Real.log (1 + 1 / Real.sqrt 3))
      (endpoint seedThreeLogLower) (endpoint seedThreeLogUpper) := by
    simpa only [Enclosed, endpoint_cast] using seedThree
  have ht : Enclosed (Real.log (TupleLogBridge.eightSeed second)) (seedLower second) (seedUpper second) := by
    cases second
    · simpa only [Enclosed, seedLower, seedUpper, endpoint_cast, TupleLogBridge.eightSeed, Bool.false_eq_true,
        if_false] using seedFirst
    · simpa only [Enclosed, seedLower, seedUpper, endpoint_cast, TupleLogBridge.eightSeed, if_true]
        using seedSecond
  unfold phi
  rw [Real.log_div (by positivity) (by cases second <;> simp [TupleLogBridge.eightSeed] <;> positivity)]
  exact (hs.sub ht).div vLog vLogPositive hl₁ hl₂ hh₁ hh₂

private def p : ℤ := 7245041563609868334833820391875168989578564317470721843498170419102306819217367843645485060260418960340694639539967684362309607357765886753846030563788562222875165250967289894091451575822073487670636229942775743226920070958850422148162463068660291479025987084679360231106118413816778206731344762573909080743825413934358520641212959054404828758783673814235477516644684261304369885998417953500499714581090550933427466466780623212367887246258103569833767790227757841084910380127911218370110395449329

private def q : ℤ := 9697482791113181183351168070062864624206116716373983651239952879446907919124157440615711268884404420409319799554116569892542858842434674147032803321553920578188452638324295803149192159354688171237877531198779015651398361053180437060319012486026442686071979851989082691730437678128908350043631597056798018069687033598055419759676350974773281581720007354905560232507596871194268723465293098546498911559295174996009755535623794323571819401691674612439130556943135611560118008634257133618397391274026

private def k (second : Bool) : ℤ :=
  if second then -4790220957485762181949065450229877562360644854779226602996178248072438109518731351039638371870686541952982902119426900346234684094260789122545445412864626325543069672901911112283293893842671865296594311464475255734756239689033146455677485506229790135021747626619307775879900269458982115412178597035937597147182623480833523635148997342364344239957996433518150952345241893134817960511498898907771831232076794121556066904590950426331139398436158706450620449749789943868745146349878132491064399856895 else 841778167725733336885639249104602189039503458198760491966821489437154453598272375092538921351769044520289040925672457737078409923512856184344461749960623321576180921306796862121282774488022590743540921571890470851710532326380542589025980715208358868942507311903102641118548647096576622971928292153238201839917984835771534836849343674353274483803821134285262105740571495440193634593040684313534884758036870757597655432863295058557262252690981123887521107641147605253051986194450041454821811847514

private theorem q_pos : 0 < q := by decide +kernel

private theorem q_pos_real : (0 : ℝ) < q := by exact_mod_cast q_pos

private theorem q_le : q ≤ 10 ^ 496 := by decide +kernel

private def tolerance : ℚ := 1 / 10 ^ 488

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 1000 in
private theorem thetaLarge : |(q : ℝ) * theta - p| ≤ 1 / 10 ^ 488 := by
  have h : Enclosed theta (((p : ℚ) - tolerance) / q) (((p : ℚ) + tolerance) / q) :=
    theta_of_bounds (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rcases h with ⟨hl, hu⟩
  simp only [tolerance, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_intCast] at hl hu
  have hl' := (div_le_iff₀ q_pos_real).mp hl
  have hu' := (le_div_iff₀ q_pos_real).mp hu
  rw [abs_le]
  constructor <;> linarith only [hl', hu']

set_option maxRecDepth 10000 in
private theorem phiLarge (second : Bool) :
    (k second : ℝ) + 1 / 4 < (q : ℝ) * phi second ∧
    (q : ℝ) * phi second < (k second : ℝ) + 1 - 1 / 4 := by
  have h : Enclosed (phi second) (((k second : ℚ) + 1 / 3) / q)
      (((k second : ℚ) + 2 / 3) / q) := by
    cases second
    · exact phi_of_bounds false (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel)
    · exact phi_of_bounds true (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel)
  rcases h with ⟨hl, hu⟩
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat, Rat.cast_intCast] at hl hu
  have hl' := (div_le_iff₀ q_pos_real).mp hl
  have hu' := (le_div_iff₀ q_pos_real).mp hu
  constructor <;> linarith only [hl', hu']

set_option maxRecDepth 10000 in
private theorem thetaSmall :
    (747105379 : ℝ) / 1000000000 ≤ theta ∧ theta ≤ 747105381 / 1000000000 := by
  have h : Enclosed theta ((747105379 : ℚ) / 1000000000) (747105381 / 1000000000) :=
    theta_of_bounds (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [Enclosed, Rat.cast_div, Rat.cast_ofNat] using h

set_option maxRecDepth 10000 in
private theorem phiSmall (second : Bool) :
    ((86803 : ℝ) / 1000000 ≤ phi second ∧ phi second ≤ 86805 / 1000000) ∨
    ((-493966 : ℝ) / 1000000 ≤ phi second ∧ phi second ≤ -493965 / 1000000) := by
  cases second
  · left
    have h : Enclosed (phi false) ((86803 : ℚ) / 1000000) (86805 / 1000000) :=
      phi_of_bounds false (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simpa only [Enclosed, Rat.cast_div, Rat.cast_ofNat] using h
  · right
    have h : Enclosed (phi true) ((-493966 : ℚ) / 1000000) (-493965 / 1000000) :=
      phi_of_bounds true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simpa only [Enclosed, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h

/-- The two certified denominator steps reduce the normalized Pell index to at most five. -/
theorem index_le_five (n : ℕ) (m : ℤ) (second : Bool) (hn : n < 10 ^ 487)
    (hdecay : |(n : ℝ) * theta - m + phi second| ≤ (5 : ℝ) / (24 * 4 ^ n)) :
    n ≤ 5 :=
  TupleLogReduction.two_stage_index_bound theta (phi second) n m p q (k second) hn hdecay
    q_pos q_le thetaLarge (phiLarge second).1 (phiLarge second).2 thetaSmall (phiSmall second)

end TupleBDCertificates

#print axioms TupleBDCertificates.index_le_five
