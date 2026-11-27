import NormalForms
import Mathlib.Tactic.Linarith

namespace Erdos1082

def frame (a b p : ℝ × ℝ) : ℝ × ℝ :=
  let vx := b.1-a.1
  let vy := b.2-a.2
  (vy*p.1-vx*p.2, vx*p.1+vy*p.2)

theorem frame_dist (a b p q : ℝ × ℝ) (hab : distanceSq a b = 1) :
    distanceSq (frame a b p) (frame a b q) = distanceSq p q := by
  unfold distanceSq frame at *
  linear_combination ((p.1-q.1)^2+(p.2-q.2)^2)*hab

theorem frame_equilateral (a b : ℝ × ℝ) (ha : distanceSq a (0,0) = 1)
    (hb : distanceSq b (0,0) = 1) (hab : distanceSq a b = 1) :
    ∃ s : ℝ, s^2 = 3 ∧ frame a b a = (s/2,-1/2) ∧ frame a b b = (s/2,1/2) := by
  have hay : (frame a b a).2 = -1/2 := by
    unfold frame distanceSq at *
    linear_combination (hb-ha-hab)/2
  have hby : (frame a b b).2 = 1/2 := by
    unfold frame distanceSq at *
    linear_combination (hb-ha+hab)/2
  have hx : (frame a b b).1 = (frame a b a).1 := by
    unfold frame
    ring
  have hnorm : (frame a b a).1^2 + (frame a b a).2^2 = 1 := by
    have h := frame_dist a b a (0,0) hab
    have h0 : frame a b (0,0) = (0,0) := by simp [frame]
    rw [h0, ha] at h
    simpa [distanceSq] using h
  refine ⟨2*(frame a b a).1, ?_, ?_, ?_⟩
  · rw [hay] at hnorm
    linear_combination 4*hnorm
  · exact Prod.ext (by dsimp; ring) hay
  · exact Prod.ext (by rw [hx]; dsimp; ring) hby

theorem frame_injective (a b : ℝ × ℝ) (hab : distanceSq a b = 1) :
    Function.Injective (frame a b) := by
  intro p q h
  have he : distanceSq p q = 0 := by
    rw [← frame_dist a b p q hab, h]
    simp [distanceSq]
  apply Prod.ext
  · unfold distanceSq at he
    have hzero : (p.1-q.1)^2 = 0 := by nlinarith [sq_nonneg (p.1-q.1), sq_nonneg (p.2-q.2)]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp (by simpa [pow_two] using hzero))
  · unfold distanceSq at he
    have hzero : (p.2-q.2)^2 = 0 := by nlinarith [sq_nonneg (p.1-q.1), sq_nonneg (p.2-q.2)]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp (by simpa [pow_two] using hzero))

/-- Translate the first point to the origin and divide all coordinates by the
common side length. -/
noncomputable def unitScale (o : ℝ × ℝ) (r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1-o.1)/r, (p.2-o.2)/r)

theorem unitScale_dist (o p q : ℝ × ℝ) (r : ℝ) :
    distanceSq (unitScale o r p) (unitScale o r q) = distanceSq p q / r^2 := by
  unfold unitScale distanceSq
  simp only [← sub_div, div_pow, ← add_div]
  ring

theorem unitScale_injective (o : ℝ × ℝ) (r : ℝ) (hr : r ≠ 0) :
    Function.Injective (unitScale o r) := by
  intro p q hp
  exact Prod.ext
    (sub_left_inj.mp ((div_left_inj' hr).mp (congrArg Prod.fst hp)))
    (sub_left_inj.mp ((div_left_inj' hr).mp (congrArg Prod.snd hp)))

end Erdos1082

#print axioms Erdos1082.frame_equilateral
