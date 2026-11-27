import ExtensionBound157
import Assembly157

namespace Erdos1082

/-- Any geometric realization of base code 157 has at most three extra points
using only the three base lengths and any one common fourth length. -/
theorem code157_bound
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
    X.card ≤ 3 :=
  excludeExtensions157 verified157 p₀ p₁ p₂ p₃ p₄ r M hr h1 h2 h3 h4 h12 ha hb hc hne hM X hx

end Erdos1082

#print axioms Erdos1082.code157_bound
