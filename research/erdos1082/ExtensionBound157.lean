import Transport157
import Bounds

namespace Erdos1082
open Finset

theorem eval_sqDist (p q : Point) (s z : ℝ) (hs : s^2 = 3) (hz : z^3 = 3*z+1) :
    (sqDist p q).eval s z = distanceSq (Point.eval p s z) (Point.eval q s z) := by
  simp [sqDist, eval_sqNorm, hs, hz, distanceSq, Point.eval]

/-- The code-157 distance pattern allows at most three extra points, once the
finite kernel table is supplied. The distance symbols here are squared. -/
theorem excludeExtensions157 (verified : ∀ n < 1024, allowed157 n = true ∨
      check form157 small157 n = some .impossible)
    (p₀ p₁ p₂ p₃ p₄ : ℝ × ℝ) (r M : ℝ) (hr : r ≠ 0)
    (h1 : distanceSq p₁ p₀ = r^2) (h2 : distanceSq p₂ p₀ = r^2)
    (h3 : distanceSq p₃ p₀ = r^2) (h4 : distanceSq p₄ p₀ = r^2)
    (h12 : distanceSq p₁ p₂ = r^2)
    (ha : distanceSq p₃ p₁ = distanceSq p₄ p₂)
    (hb : distanceSq p₃ p₂ = distanceSq p₄ p₁)
    (hc : distanceSq p₃ p₁ = distanceSq p₃ p₄) (hne : p₃ ≠ p₂)
    (hM : M ∉ [r^2, distanceSq p₃ p₁, distanceSq p₄ p₁])
    (X : Finset (ℝ × ℝ))
    (hx : ∀ p ∈ X, ∀ q ∈ [p₀,p₁,p₂,p₃,p₄], p ≠ q ∧
      distanceSq p q ∈ [r^2, distanceSq p₃ p₁, distanceSq p₄ p₁, M]) :
    X.card ≤ 3 := by
  classical
  obtain ⟨f, s, z, hfi, hfd, hs, hz, hf0, hf1, hf2, hf3, hf4⟩ :=
    transport157 p₀ p₁ p₂ p₃ p₄ r hr h1 h2 h3 h4 h12 ha hb hc hne
  have hf0' : f p₀ = Point.eval origin s z := by simpa [origin, Point.eval, rc] using hf0
  have hS : sqrtThree.eval s z = s := by simp [sqrtThree, Radical.eval]
  have hf1' : f p₁ = Point.eval left s z := by
    simpa [left, Point.eval, rc, Radical.eval_mul, hs, hz, hS, div_eq_mul_inv, neg_div] using hf1
  have hf2' : f p₂ = Point.eval right s z := by
    simpa [right, Point.eval, rc, Radical.eval_mul, hs, hz, hS, div_eq_mul_inv] using hf2
  have hbases : ([p₀,p₁,p₂,p₃,p₄].map f) = (base form157).map (Point.eval · s z) := by
    simp [base, hf0', hf1', hf2', hf3, hf4]
  have hsym (a b : ℝ × ℝ) : distanceSq a b = distanceSq b a := by
    unfold distanceSq
    ring
  have hD1 : (sqDist left form157.1).eval s z = distanceSq p₃ p₁ / r^2 := by
    rw [eval_sqDist _ _ _ _ hs hz, ← hf1', ← hf3, hfd, hsym]
  have hD2 : (sqDist left form157.2).eval s z = distanceSq p₄ p₁ / r^2 := by
    rw [eval_sqDist _ _ _ _ hs hz, ← hf1', ← hf4, hfd, hsym]
  have hvals : (([r^2, distanceSq p₃ p₁, distanceSq p₄ p₁] : List ℝ).map (· / r^2)) =
      small157.map (Radical.eval · s z) := by
    simp [small157, hD1, hD2, rc, div_self (pow_ne_zero 2 hr)]
  have hbaseQ (q : Point) (hq : q ∈ base form157) :
      ∃ q₀ ∈ [p₀,p₁,p₂,p₃,p₄], f q₀ = Point.eval q s z := by
    apply List.mem_map.mp
    rw [hbases]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [← card_image_of_injective X hfi]
  apply bound_actual157 verified s z (M / r^2) hs hz
  · intro p hp q hq
    obtain ⟨p', hp', rfl⟩ := mem_image.mp hp
    obtain ⟨q', hq', he⟩ := hbaseQ q hq
    rw [← he, hfd]
    have h := (hx p' hp' q' hq').2
    by_cases hMax : distanceSq p' q' = M
    · exact Or.inl (by rw [hMax])
    · right
      have hmem : distanceSq p' q' / r^2 ∈ small157.map (Radical.eval · s z) := by
        rw [← hvals]
        apply List.mem_map.mpr
        refine ⟨_, ?_, rfl⟩
        simpa [hMax] using h
      obtain ⟨v, hv, heq⟩ := List.mem_map.mp hmem
      exact ⟨v, hv, heq.symm⟩
  · intro p hp q hq
    obtain ⟨p', hp', rfl⟩ := mem_image.mp hp
    obtain ⟨q', hq', he⟩ := hbaseQ q hq
    rw [← he]
    exact hfi.ne (hx p' hp' q' hq').1
  · intro q hq hEq
    have h := (List.mem_map (f := (Radical.eval · s z))).mpr ⟨q, hq, hEq.symm⟩
    rw [← hvals] at h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    exact hM (((div_left_inj' (pow_ne_zero 2 hr)).mp he) ▸ hw)

end Erdos1082

#print axioms Erdos1082.excludeExtensions157
