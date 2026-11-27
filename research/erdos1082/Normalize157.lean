import NormalForms
import Mathlib.Tactic.Linarith

namespace Erdos1082
open Radical

/-- Once the first three base points have been normalized to the equilateral
triangle, the remaining two points of code 157 have the cubic coordinates. -/
theorem normalize157 (s x y u v : ℝ) (hs : s^2 = 3)
    (hxy : x^2 + y^2 = 1) (huv : u^2 + v^2 = 1)
    (ha : (x-s/2)^2+(y+1/2)^2 = (u-s/2)^2+(v-1/2)^2)
    (hb : (x-s/2)^2+(y-1/2)^2 = (u-s/2)^2+(v+1/2)^2)
    (hc : (x-s/2)^2+(y+1/2)^2 = (x-u)^2+(y-v)^2)
    (hne : (x,y) ≠ (s/2,1/2)) :
    ∃ z : ℝ, z^3 = 3*z+1 ∧
      Point.eval form157.1 s z = (x,y) ∧ Point.eval form157.2 s z = (u,v) := by
  have hsu : s * (x-u) = 0 := by
    linear_combination hxy - huv - (ha + hb)/2
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have he : x = u := sub_eq_zero.mp ((mul_eq_zero.mp hsu).resolve_left hs0)
  subst u
  have hv : v = -y := by
    linear_combination (ha-hb)/2
  subst v
  have hx : s*x = 2+y-4*y^2 := by
    linear_combination hxy + hs/4 - hc
  have hxf : x = (2+y-4*y^2)*s/3 := by
    linear_combination (s/3)*hx - (x/3)*hs
  have hfac : (2*y-1)*(8*y^3-6*y-1) = 0 := by
    linear_combination 3*hxy + x^2*hs - (s*x + (2+y-4*y^2))*hx
  have hy : 2*y-1 ≠ 0 := by
    intro h
    have hh : y = 1/2 := by linarith
    apply hne
    refine Prod.ext ?_ hh
    rw [hh] at hxf
    linear_combination hxf
  have hz0 := (mul_eq_zero.mp hfac).resolve_left hy
  have hz : (2*y)^3 = 3*(2*y)+1 := by linear_combination hz0
  refine ⟨2*y, hz, ?_⟩
  have hS : sqrtThree.eval s (2*y) = s := by simp [sqrtThree, Radical.eval]
  have hZ : cubicRoot.eval s (2*y) = 2*y := by
    simp [cubicRoot, Radical.eval, Cubic.eval, Cubic.constant]
  constructor <;> apply Prod.ext <;>
    simp only [Point.eval, form157, Radical.eval_mul _ _ _ _ hs hz, Radical.eval_add,
      Radical.eval_sub, Radical.eval_neg, rc, Radical.eval_constant, hS, hZ] <;>
    push_cast
  · linear_combination -hxf
  · ring
  · linear_combination -hxf
  · ring

end Erdos1082

#print axioms Erdos1082.normalize157
