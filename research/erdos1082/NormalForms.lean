import ExtensionCertificate

namespace Erdos1082
open Radical

def rc := Radical.constant

def sqrtThree : Radical := ⟨Cubic.constant 0, Cubic.constant 1⟩

def cubicRoot : Radical := ⟨⟨0, 1, 0⟩, Cubic.constant 0⟩

def origin : Point := (rc 0, rc 0)
def left : Point := (sqrtThree.mul (rc (1 / 2)), rc (-1 / 2))
def right : Point := (sqrtThree.mul (rc (1 / 2)), rc (1 / 2))

def form123 (positive : Bool) : Point × Point :=
  let e := rc (if positive then 1 else -1)
  ((e, rc 0), (e.mul (rc (1 / 2)), e.mul (sqrtThree.mul (rc (-1 / 2)))))

def form157 : Point × Point :=
  let y := cubicRoot.mul (rc (1 / 2))
  let x := ((rc 2).add y |>.sub ((rc 4).mul (y.mul y))).mul (sqrtThree.mul (rc (1 / 3)))
  ((x, y), (x, y.neg))

def base (tail : Point × Point) : List Point :=
  [origin, left, right, tail.1, tail.2]

def sqDist (a b : Point) : Radical :=
  sqNorm (a.1.sub b.1, a.2.sub b.2)

def small123 (positive : Bool) : List Radical :=
  let tail := form123 positive
  [rc 1, sqDist left tail.1, sqDist right tail.2]

def small157 : List Radical :=
  [rc 1, sqDist left form157.1, sqDist left form157.2]

namespace Affine

def add (p q : Affine) : Affine := ⟨p.constant.add q.constant, p.slope.add q.slope⟩
def sub (p q : Affine) : Affine := ⟨p.constant.sub q.constant, p.slope.sub q.slope⟩
def scale (v : Radical) (p : Affine) : Affine := ⟨v.mul p.constant, v.mul p.slope⟩
def fixed (v : Radical) : Affine := ⟨v, rc 0⟩
def parameter : Affine := ⟨rc 0, rc 1⟩

@[simp] theorem eval_add (p q : Affine) (s z t : ℝ) :
    (p.add q).eval s z t = p.eval s z t + q.eval s z t := by
  simp [add, eval]
  ring

@[simp] theorem eval_sub (p q : Affine) (s z t : ℝ) :
    (p.sub q).eval s z t = p.eval s z t - q.eval s z t := by
  simp [sub, eval]
  ring

theorem eval_scale (p : Affine) (v : Radical) (s z t : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1) :
    (scale v p).eval s z t = v.eval s z * p.eval s z t := by
  simp [scale, eval, Radical.eval_mul, hs, hz]
  ring

@[simp] theorem eval_fixed (v : Radical) (s z t : ℝ) :
    (fixed v).eval s z t = v.eval s z := by simp [fixed, eval, rc]

@[simp] theorem eval_parameter (s z t : ℝ) : parameter.eval s z t = t := by
  simp [parameter, eval, rc]

end Affine

def label (small : List Radical) (i : ℕ) : Affine :=
  match small[i]? with
  | some v => Affine.fixed v
  | none => Affine.parameter

def system (tail : Point × Point) (small : List Radical) (d : ℕ → ℕ) : System :=
  let D := label small ∘ d
  let rhs (i : ℕ) := Affine.scale (rc (1 / 2)) ((Affine.fixed (rc 1)).add (D 0) |>.sub (D i))
  let X := Affine.scale (sqrtThree.mul (rc (1 / 3))) ((rhs 1).add (rhs 2))
  let Y := (rhs 2).sub (rhs 1)
  let err (p : Point) (i : ℕ) := ((Affine.scale p.1 X).add (Affine.scale p.2 Y)).sub (rhs i)
  ⟨X, Y, D 0, err tail.1 3, err tail.2 4⟩

def decode (n i : ℕ) := n / 4 ^ i % 4

def check (tail : Point × Point) (small : List Radical) (n : ℕ) : Option Class :=
  classify (system tail small (decode n)) (base tail) small

def live (tail : Point × Point) (small : List Radical) : List (ℕ × Option Class) :=
  (List.range 1024).filterMap fun n =>
    let r := check tail small n
    if r = some .impossible then none else some (n, r)

def Point.eval (p : Point) (s z : ℝ) : ℝ × ℝ := (p.1.eval s z, p.2.eval s z)

def distanceSq (p q : ℝ × ℝ) : ℝ := (p.1 - q.1)^2 + (p.2 - q.2)^2

/-- Any real point with the indicated five distances is covered by the
normalized linear system; its two coordinate forms recover the point. -/
theorem system_sound (tail : Point × Point) (small : List Radical) (d : ℕ → ℕ)
    (s z t a b : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1)
    (h0 : a^2 + b^2 = (label small (d 0)).eval s z t)
    (h1 : (a - s / 2)^2 + (b + 1 / 2)^2 = (label small (d 1)).eval s z t)
    (h2 : (a - s / 2)^2 + (b - 1 / 2)^2 = (label small (d 2)).eval s z t)
    (h3 : distanceSq (a,b) (Point.eval tail.1 s z) = (label small (d 3)).eval s z t)
    (h4 : distanceSq (a,b) (Point.eval tail.2 s z) = (label small (d 4)).eval s z t)
    (hu3 : (tail.1.1.eval s z)^2 + (tail.1.2.eval s z)^2 = 1)
    (hu4 : (tail.2.1.eval s z)^2 + (tail.2.2.eval s z)^2 = 1) :
    let P := system tail small d
    P.x.eval s z t = a ∧ P.y.eval s z t = b ∧ P.Satisfies s z t := by
  have hS : sqrtThree.eval s z = s := by
    simp [sqrtThree, Radical.eval]
  let D := fun i => (label small (d i)).eval s z t
  have hA : s * a = 1 + D 0 - (D 1 + D 2) / 2 := by
    dsimp [D]
    linear_combination h0 - (h1 + h2) / 2 + hs / 4
  have hx : s / 3 * (1 + D 0 - (D 1 + D 2) / 2) = a := by
    rw [← hA]
    linear_combination (a / 3) * hs
  have hy : (D 1 - D 2) / 2 = b := by
    dsimp [D]
    linear_combination (h2 - h1) / 2
  simp only [system, System.Satisfies, Affine.eval_add, Affine.eval_sub,
    Affine.eval_scale _ _ _ _ _ hs hz, Radical.eval_mul _ _ _ _ hs hz,
    Affine.eval_fixed, rc, Radical.eval_constant, hS, Function.comp_apply]
  push_cast
  have hx' : s * (1 / 3) * (1 / 2 * (1 + D 0 - D 1) + 1 / 2 * (1 + D 0 - D 2)) = a := by
    linear_combination hx
  have hy' : 1 / 2 * (1 + D 0 - D 2) - 1 / 2 * (1 + D 0 - D 1) = b := by
    linear_combination hy
  rw [hx', hy']
  refine ⟨rfl, rfl, ?_, ?_, h0⟩
  · simp only [distanceSq, Point.eval] at h3
    linear_combination (h0 + hu3 - h3) / 2
  · simp only [distanceSq, Point.eval] at h4
    linear_combination (h0 + hu4 - h4) / 2

end Erdos1082

#print axioms Erdos1082.system_sound
