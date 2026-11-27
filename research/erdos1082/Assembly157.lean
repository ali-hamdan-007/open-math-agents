import Checked157_0
import Checked157_1
import Checked157_2
import Checked157_3
import Checked157_4
import Checked157_5
import Checked157_6
import Checked157_7
import Mathlib.Tactic.IntervalCases

namespace Erdos1082

theorem verified157 (n : ℕ) (hn : n < 1024) :
    allowed157 n = true ∨ check form157 small157 n = some .impossible := by
  let b := n / 32
  have hb : b < 32 := by dsimp [b]; omega
  have table (j : ℕ) (hj : j < 32) : checkBlock157 (32*j) 32 = true := by
    interval_cases j
    · exact checked157_0
    · exact checked157_1
    · exact checked157_2
    · exact checked157_3
    · exact checked157_4
    · exact checked157_5
    · exact checked157_6
    · exact checked157_7
    · exact checked157_8
    · exact checked157_9
    · exact checked157_10
    · exact checked157_11
    · exact checked157_12
    · exact checked157_13
    · exact checked157_14
    · exact checked157_15
    · exact checked157_16
    · exact checked157_17
    · exact checked157_18
    · exact checked157_19
    · exact checked157_20
    · exact checked157_21
    · exact checked157_22
    · exact checked157_23
    · exact checked157_24
    · exact checked157_25
    · exact checked157_26
    · exact checked157_27
    · exact checked157_28
    · exact checked157_29
    · exact checked157_30
    · exact checked157_31
  have hh : checkBlock157 (32*b) 32 = true := table b hb
  have eq : 32*b + n%32 = n := by dsimp [b]; omega
  simpa only [eq] using checkedBlock157 hh (show n%32 < 32 by omega)

theorem normalized157_bound (s z t : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3*z+1)
    (points : Finset (ℝ × ℝ))
    (hpoint : ∀ p ∈ points, ∀ q ∈ base form157,
      distanceSq p (Point.eval q s z) = t ∨
        ∃ v ∈ small157, distanceSq p (Point.eval q s z) = v.eval s z)
    (hbase : ∀ p ∈ points, ∀ q ∈ base form157, p ≠ Point.eval q s z)
    (hsmall : ∀ q ∈ small157, t ≠ q.eval s z) : points.card ≤ 3 :=
  bound_actual157 verified157 s z t hs hz points hpoint hbase hsmall

end Erdos1082

#print axioms Erdos1082.normalized157_bound
