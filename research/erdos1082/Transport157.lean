import Frame
import Normalize157

namespace Erdos1082

/-! Code 157 describes a unit-radius center and the ordered side pattern
0,1,2,2,1,1 on the six peripheral edges. -/

theorem transport157 (p₀ p₁ p₂ p₃ p₄ : ℝ × ℝ) (r : ℝ) (hr : r ≠ 0)
    (h1 : distanceSq p₁ p₀ = r^2) (h2 : distanceSq p₂ p₀ = r^2)
    (h3 : distanceSq p₃ p₀ = r^2) (h4 : distanceSq p₄ p₀ = r^2)
    (h12 : distanceSq p₁ p₂ = r^2)
    (ha : distanceSq p₃ p₁ = distanceSq p₄ p₂)
    (hb : distanceSq p₃ p₂ = distanceSq p₄ p₁)
    (hc : distanceSq p₃ p₁ = distanceSq p₃ p₄)
    (hne : p₃ ≠ p₂) :
    ∃ (f : (ℝ × ℝ) → ℝ × ℝ) (s z : ℝ), Function.Injective f ∧
      (∀ p q, distanceSq (f p) (f q) = distanceSq p q / r^2) ∧
      s^2 = 3 ∧ z^3 = 3*z+1 ∧
      f p₀ = (0,0) ∧ f p₁ = (s/2,-1/2) ∧ f p₂ = (s/2,1/2) ∧
      f p₃ = Point.eval form157.1 s z ∧ f p₄ = Point.eval form157.2 s z := by
  let g := unitScale p₀ r
  let a := g p₁
  let b := g p₂
  let f := frame a b ∘ g
  have hg0 : g p₀ = (0,0) := by simp [g, unitScale]
  have hgd (p q : ℝ × ℝ) : distanceSq (g p) (g q) = distanceSq p q / r^2 :=
    unitScale_dist p₀ p q r
  have h12' : distanceSq a b = 1 := by
    change distanceSq (g p₁) (g p₂) = 1
    rw [hgd, h12, div_self (pow_ne_zero 2 hr)]
  have ha' : distanceSq a (0,0) = 1 := by
    rw [← hg0]
    change distanceSq (g p₁) (g p₀) = 1
    rw [hgd, h1, div_self (pow_ne_zero 2 hr)]
  have hb' : distanceSq b (0,0) = 1 := by
    rw [← hg0]
    change distanceSq (g p₂) (g p₀) = 1
    rw [hgd, h2, div_self (pow_ne_zero 2 hr)]
  obtain ⟨s, hs, hf1, hf2⟩ := frame_equilateral a b ha' hb' h12'
  change f p₁ = (s/2,-1/2) at hf1
  change f p₂ = (s/2,1/2) at hf2
  have hf0 : f p₀ = (0,0) := by simp [f, hg0, frame]
  have hfd (p q : ℝ × ℝ) : distanceSq (f p) (f q) = distanceSq p q / r^2 := by
    exact (frame_dist a b (g p) (g q) h12').trans (hgd p q)
  have hfi : Function.Injective f := (frame_injective a b h12').comp (unitScale_injective _ _ hr)
  have n3 : (f p₃).1^2 + (f p₃).2^2 = 1 := by
    have h := hfd p₃ p₀
    rw [hf0, h3, div_self (pow_ne_zero 2 hr)] at h
    simpa [distanceSq] using h
  have n4 : (f p₄).1^2 + (f p₄).2^2 = 1 := by
    have h := hfd p₄ p₀
    rw [hf0, h4, div_self (pow_ne_zero 2 hr)] at h
    simpa [distanceSq] using h
  have hfa : distanceSq (f p₃) (f p₁) = distanceSq (f p₄) (f p₂) := by
    rw [hfd, hfd, ha]
  have hfb : distanceSq (f p₃) (f p₂) = distanceSq (f p₄) (f p₁) := by
    rw [hfd, hfd, hb]
  have hfc : distanceSq (f p₃) (f p₁) = distanceSq (f p₃) (f p₄) := by
    rw [hfd, hfd, hc]
  have hfne : f p₃ ≠ (s/2,1/2) := by rw [← hf2]; exact hfi.ne hne
  obtain ⟨z, hz, hn3, hn4⟩ := normalize157 s (f p₃).1 (f p₃).2 (f p₄).1 (f p₄).2
    hs n3 n4 (by simpa [distanceSq, hf1, hf2, neg_div, sub_neg_eq_add] using hfa)
    (by simpa [distanceSq, hf1, hf2, neg_div, sub_neg_eq_add] using hfb)
    (by simpa [distanceSq, hf1, neg_div, sub_neg_eq_add] using hfc) hfne
  exact ⟨f, s, z, hfi, hfd, hs, hz, hf0, hf1, hf2, hn3.symm, hn4.symm⟩

end Erdos1082

#print axioms Erdos1082.transport157
