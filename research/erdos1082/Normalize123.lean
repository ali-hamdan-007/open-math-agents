import NormalForms

namespace Erdos1082
open Radical

/-- Code 123 has two signed normal forms once its first three points are
in the equilateral frame. -/
theorem normalize123 (s x y u v : ℝ) (hs : s^2 = 3)
    (hxy : x^2 + y^2 = 1) (huv : u^2 + v^2 = 1)
    (ha : (x-s/2)^2+(y+1/2)^2 = (x-s/2)^2+(y-1/2)^2)
    (hb : (x-s/2)^2+(y+1/2)^2 = (u-s/2)^2+(v+1/2)^2)
    (hc : (x-u)^2+(y-v)^2 = 1) :
    ∃ positive : Bool, ∀ z : ℝ, z^3 = 3*z+1 →
      Point.eval (form123 positive).1 s z = (x,y) ∧
      Point.eval (form123 positive).2 s z = (u,v) := by
  have hy : y = 0 := by linear_combination ha/2
  subst y
  have hx : x^2 = 1 := by simpa using hxy
  have heu : 2*x*u = 1 := by linear_combination hx + huv - hc
  have hu : u = x/2 := by linear_combination (x/2)*heu - u*hx
  have hv : v = -s*x/2 := by
    linear_combination hx - huv - hb + s*hu
  have hx' : (x-1)*(x+1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp hx' with hx' | hx'
  · have hpos : x = 1 := sub_eq_zero.mp hx'
    refine ⟨true, ?_⟩
    intro z hz
    have hS : sqrtThree.eval s z = s := by simp [sqrtThree, Radical.eval]
    subst x
    rw [hu, hv]
    simp [form123, Point.eval, Radical.eval_mul, hs, hz, hS, rc, neg_div, div_eq_mul_inv]
  · have hneg : x = -1 := eq_neg_of_add_eq_zero_left hx'
    refine ⟨false, ?_⟩
    intro z hz
    have hS : sqrtThree.eval s z = s := by simp [sqrtThree, Radical.eval]
    subst x
    rw [hu, hv]
    simp [form123, Point.eval, Radical.eval_mul, hs, hz, hS, rc, neg_div, div_eq_mul_inv]

end Erdos1082

#print axioms Erdos1082.normalize123
