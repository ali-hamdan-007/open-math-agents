import RadicalAlgebra

namespace Erdos1082
open Radical

structure Affine where
  constant : Radical
  slope : Radical
  deriving DecidableEq, Repr

namespace Affine

def eval (p : Affine) (s z t : ℝ) : ℝ :=
  p.constant.eval s z + p.slope.eval s z * t

def atValue (p : Affine) (t : Radical) : Radical := p.constant.add (p.slope.mul t)

theorem eval_atValue (p : Affine) (t : Radical) (s z : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1) :
    (p.atValue t).eval s z = p.eval s z (t.eval s z) := by
  simp [atValue, eval, Radical.eval_mul, hs, hz]

end Affine

abbrev Point := Radical × Radical

def sqNorm (p : Point) : Radical := (p.1.mul p.1).add (p.2.mul p.2)

theorem eval_sqNorm (p : Point) (s z : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1) :
    (sqNorm p).eval s z = (p.1.eval s z) ^ 2 + (p.2.eval s z) ^ 2 := by
  simp [sqNorm, Radical.eval_mul, hs, hz, pow_two]

inductive Class where
  | impossible
  | free (point : Point)
  | forced (parameter : Radical) (point : Point)
  deriving DecidableEq, Repr

/-- The first two peripheral equations express the coordinates as affine
functions of the parameter. The remaining equations constrain it. -/
structure System where
  x : Affine
  y : Affine
  d : Affine
  e₁ : Affine
  e₂ : Affine
  deriving Repr

def System.Satisfies (P : System) (s z t : ℝ) : Prop :=
  P.e₁.eval s z t = 0 ∧ P.e₂.eval s z t = 0 ∧
    (P.x.eval s z t) ^ 2 + (P.y.eval s z t) ^ 2 = P.d.eval s z t

def Class.Covers (C : Class) (P : System) (s z t : ℝ) : Prop :=
  match C with
  | .impossible => False
  | .free p => P.x.eval s z t = p.1.eval s z ∧ P.y.eval s z t = p.2.eval s z
  | .forced u p => t = u.eval s z ∧ P.x.eval s z t = p.1.eval s z ∧
      P.y.eval s z t = p.2.eval s z

def verifiesNonzero (r : Radical) : Bool :=
  decide (r.mul r.inverseCandidate = Radical.constant 1)

theorem nonzero_sound (r : Radical) (s z : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1) (h : verifiesNonzero r) :
    r.eval s z ≠ 0 :=
  Radical.eval_ne_zero_of_inverse _ _ s z hs hz (of_decide_eq_true h)

def zeroRadical : Radical := Radical.constant 0

def fixesParameter (e : Affine) (u : Radical) : Bool :=
  verifiesNonzero e.slope && decide (e.atValue u = zeroRadical)

theorem fixesParameter_sound (e : Affine) (u : Radical) (s z t : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1) (h : fixesParameter e u)
    (he : e.eval s z t = 0) : t = u.eval s z := by
  obtain ⟨hn, hu⟩ := Bool.and_eq_true_iff.mp h
  have hnz := nonzero_sound e.slope s z hs hz hn
  have hknown : e.eval s z (u.eval s z) = 0 := by
    rw [← Affine.eval_atValue _ _ _ _ hs hz, of_decide_eq_true hu]
    simp [zeroRadical]
  unfold Affine.eval at he hknown
  apply (mul_right_inj' hnz).mp
  linear_combination he - hknown

def contradictsAt (P : System) (u : Radical) : Bool :=
  verifiesNonzero (P.e₁.atValue u) || verifiesNonzero (P.e₂.atValue u) ||
    verifiesNonzero ((sqNorm (P.x.atValue u, P.y.atValue u)).sub (P.d.atValue u))

theorem contradictsAt_sound (P : System) (u : Radical) (s z : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1) (h : contradictsAt P u) :
    ¬ P.Satisfies s z (u.eval s z) := by
  intro hp
  simp only [contradictsAt, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · apply nonzero_sound _ s z hs hz h
    rw [Affine.eval_atValue _ _ _ _ hs hz, hp.1]
  · apply nonzero_sound _ s z hs hz h
    rw [Affine.eval_atValue _ _ _ _ hs hz, hp.2.1]
  · apply nonzero_sound _ s z hs hz h
    simp only [Radical.eval_sub, eval_sqNorm _ s z hs hz,
      Affine.eval_atValue _ _ _ _ hs hz, hp.2.2, sub_self]

def classifyAt (P : System) (u : Radical) (base : List Point) (small : List Radical) : Class :=
  let p := (P.x.atValue u, P.y.atValue u)
  if u ∈ small ∨ p ∈ base ∨ contradictsAt P u then .impossible else .forced u p

theorem classifyAt_sound (P : System) (u : Radical) (base : List Point)
    (small : List Radical) (s z t : ℝ)
    (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1)
    (ht : t = u.eval s z) (hp : P.Satisfies s z t)
    (hbase : ∀ p ∈ base, P.x.eval s z t ≠ p.1.eval s z ∨ P.y.eval s z t ≠ p.2.eval s z)
    (hsmall : ∀ q ∈ small, t ≠ q.eval s z) :
    (classifyAt P u base small).Covers P s z t := by
  subst t
  simp only [classifyAt]
  split
  · rename_i h
    rcases h with hu | hbp | he
    · exact (hsmall u hu rfl).elim
    · rcases hbase _ hbp with hx | hy
      · exact (hx (Affine.eval_atValue _ _ _ _ hs hz).symm).elim
      · exact (hy (Affine.eval_atValue _ _ _ _ hs hz).symm).elim
    · exact contradictsAt_sound P u s z hs hz he hp
  · exact ⟨rfl, (Affine.eval_atValue _ _ _ _ hs hz).symm,
      (Affine.eval_atValue _ _ _ _ hs hz).symm⟩

/-- The checker rejects any assignment it cannot cover by a finite candidate. -/
def classify (P : System) (base : List Point) (small : List Radical) : Option Class :=
  let u₁ := P.e₁.constant.neg.mul P.e₁.slope.inverseCandidate
  let u₂ := P.e₂.constant.neg.mul P.e₂.slope.inverseCandidate
  let p := (P.x.constant, P.y.constant)
  if fixesParameter P.e₁ u₁ then some (classifyAt P u₁ base small)
  else if fixesParameter P.e₂ u₂ then some (classifyAt P u₂ base small)
  else if (P.e₁.slope = zeroRadical ∧ verifiesNonzero P.e₁.constant) ∨
      (P.e₂.slope = zeroRadical ∧ verifiesNonzero P.e₂.constant) then some .impossible
  else if P.x.slope = zeroRadical ∧ P.y.slope = zeroRadical then
    if p ∈ base ∨ (P.d.slope = zeroRadical ∧
      verifiesNonzero ((sqNorm p).sub P.d.constant)) then some .impossible else some (.free p)
  else none

theorem classify_sound (P : System) (base : List Point) (small : List Radical)
    (s z t : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3 * z + 1)
    (hp : P.Satisfies s z t)
    (hbase : ∀ p ∈ base, P.x.eval s z t ≠ p.1.eval s z ∨ P.y.eval s z t ≠ p.2.eval s z)
    (hsmall : ∀ q ∈ small, t ≠ q.eval s z)
    (C : Class) (hc : classify P base small = some C) : C.Covers P s z t := by
  simp only [classify] at hc
  split at hc
  · rename_i h
    cases hc
    exact classifyAt_sound P _ base small s z t hs hz
      (fixesParameter_sound _ _ s z t hs hz h hp.1) hp hbase hsmall
  split at hc
  · rename_i h
    cases hc
    exact classifyAt_sound P _ base small s z t hs hz
      (fixesParameter_sound _ _ s z t hs hz h hp.2.1) hp hbase hsmall
  split at hc
  · rename_i h
    rcases h with ⟨hslope, hn⟩ | ⟨hslope, hn⟩
    · exact (nonzero_sound _ s z hs hz hn (by
        simpa [Affine.eval, hslope, zeroRadical] using hp.1)).elim
    · exact (nonzero_sound _ s z hs hz hn (by
        simpa [Affine.eval, hslope, zeroRadical] using hp.2.1)).elim
  split at hc
  · rename_i hxy
    have hx : P.x.eval s z t = P.x.constant.eval s z := by
      simp [Affine.eval, hxy.1, zeroRadical]
    have hy : P.y.eval s z t = P.y.constant.eval s z := by
      simp [Affine.eval, hxy.2, zeroRadical]
    split at hc
    · rename_i h
      rcases h with h | ⟨hd, hn⟩
      · rcases hbase _ h with he | he
        · exact (he hx).elim
        · exact (he hy).elim
      · apply (nonzero_sound _ s z hs hz hn ?_).elim
        simpa [eval_sqNorm _ s z hs hz, sub_eq_zero, Affine.eval, hd, zeroRadical] using
          (by rw [← hx, ← hy]; exact hp.2.2 :
            P.x.constant.eval s z ^ 2 + P.y.constant.eval s z ^ 2 = P.d.eval s z t)
    · cases hc
      exact ⟨hx, hy⟩
  · contradiction

end Erdos1082

#print axioms Erdos1082.classify_sound
