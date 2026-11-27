import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace Erdos1082

/-- A polynomial representative in the basis (1,z,z²), evaluated at a
root of (z³-3z-1). -/
structure Cubic where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq, Repr

namespace Cubic

def eval (p : Cubic) (z : ℝ) : ℝ := p.a + p.b * z + p.c * z ^ 2

def constant (q : ℚ) : Cubic := ⟨q, 0, 0⟩

def add (p q : Cubic) : Cubic := ⟨p.a + q.a, p.b + q.b, p.c + q.c⟩

def neg (p : Cubic) : Cubic := ⟨-p.a, -p.b, -p.c⟩

def mul (p q : Cubic) : Cubic :=
  let c₃ := p.b * q.c + p.c * q.b
  let c₄ := p.c * q.c
  ⟨p.a * q.a + c₃,
    p.a * q.b + p.b * q.a + 3 * c₃ + c₄,
    p.a * q.c + p.b * q.b + p.c * q.a + 3 * c₄⟩

/-- The adjugate formula applied to multiplication by a cubic representative. -/
def inverseCandidate (p : Cubic) : Cubic :=
  let d := p.a + 3 * p.c
  let e := 3 * p.b + p.c
  let x := d * d - e * p.b
  let y := e * p.c - p.b * d
  let z := p.b * p.b - d * p.c
  let det := p.a * x + p.c * y + p.b * z
  ⟨x / det, y / det, z / det⟩

@[simp] theorem eval_constant (q : ℚ) (z : ℝ) : (constant q).eval z = q := by
  simp [constant, eval]

@[simp] theorem eval_add (p q : Cubic) (z : ℝ) : (p.add q).eval z = p.eval z + q.eval z := by
  push_cast [add, eval]
  ring

@[simp] theorem eval_neg (p : Cubic) (z : ℝ) : p.neg.eval z = -p.eval z := by
  push_cast [neg, eval]
  ring

theorem eval_mul (p q : Cubic) (z : ℝ) (hz : z ^ 3 = 3 * z + 1) :
    (p.mul q).eval z = p.eval z * q.eval z := by
  push_cast [mul, eval]
  linear_combination -((p.b : ℝ) * q.c + p.c * q.b + p.c * q.c * z) * hz

end Cubic

/-- Rational coordinates in the basis (1,z,z²,s,sz,sz²) with (s²=3). -/
structure Radical where
  a : Cubic
  b : Cubic
  deriving DecidableEq, Repr

namespace Radical

def eval (p : Radical) (s z : ℝ) : ℝ := p.a.eval z + s * p.b.eval z

def constant (q : ℚ) : Radical := ⟨Cubic.constant q, Cubic.constant 0⟩

def add (p q : Radical) : Radical := ⟨p.a.add q.a, p.b.add q.b⟩

def neg (p : Radical) : Radical := ⟨p.a.neg, p.b.neg⟩

def mul (p q : Radical) : Radical :=
  ⟨(p.a.mul q.a).add ((Cubic.constant 3).mul (p.b.mul q.b)),
    (p.a.mul q.b).add (p.b.mul q.a)⟩

def sub (p q : Radical) : Radical := p.add q.neg

/-- Multiply the quadratic conjugate by the candidate inverse of its norm. -/
def inverseCandidate (p : Radical) : Radical :=
  let norm := (p.a.mul p.a).add (((Cubic.constant 3).mul (p.b.mul p.b)).neg)
  let inverseNorm := norm.inverseCandidate
  ⟨p.a.mul inverseNorm, (p.b.mul inverseNorm).neg⟩

@[simp] theorem eval_constant (q : ℚ) (s z : ℝ) :
    (constant q).eval s z = q := by simp [constant, eval]

@[simp] theorem eval_add (p q : Radical) (s z : ℝ) :
    (p.add q).eval s z = p.eval s z + q.eval s z := by
  simp [add, eval]
  ring

@[simp] theorem eval_neg (p : Radical) (s z : ℝ) :
    p.neg.eval s z = -p.eval s z := by
  simp [neg, eval, add_comm]

@[simp] theorem eval_sub (p q : Radical) (s z : ℝ) :
    (p.sub q).eval s z = p.eval s z - q.eval s z := by
  simp [sub, sub_eq_add_neg]

theorem eval_mul (p q : Radical) (s z : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1) :
    (p.mul q).eval s z = p.eval s z * q.eval s z := by
  simp [mul, eval, Cubic.eval_mul, hz]
  linear_combination -(p.b.eval z * q.b.eval z) * hs

/-- Checking a supplied polynomial inverse proves nonvanishing at every
real embedding, without computing an inverse in Lean. -/
theorem eval_ne_zero_of_inverse (p q : Radical) (s z : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1)
    (h : p.mul q = constant 1) : p.eval s z ≠ 0 := by
  have hh := congrArg (fun w : Radical => w.eval s z) h
  rw [eval_mul p q s z hs hz, eval_constant] at hh
  intro he
  simp [he] at hh

end Radical
end Erdos1082

#print axioms Erdos1082.Radical.eval_ne_zero_of_inverse
