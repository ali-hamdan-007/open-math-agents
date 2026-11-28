import Mathlib.Tactic.Linarith

namespace Graph189LargeDegree

/-- Above this threshold, the robust lower order already excludes a genuine
low on a minimum cut by the wedge alone. The stronger lower order then
contradicts the upper order from the common-label theorem. -/
theorem no_high_degree {s k n : ℤ}
    (hs : 10 ≤ s) (hk : 2*s^2+3*s-2 ≤ k)
    (hhalf : 6*(s-1)<k → 2*n < (2*s+3)*k+4*s+4)
    (hthree : 6*(s-1)<k → (s-2)*(n-2*s-3) < ((s+1)*(s-2)+3)*k)
    (hrob : 4*s≤k → 4*n<k*(k-1) → (s+2)*(k-2*s+2)-1 ≤ n)
    (halt : 4*s≤k → 4*n<k*(k-1) →
      (∃ r d : ℤ, 1≤d ∧ r≤s ∧ k*d≤2*k+(k+1)*r-n) ∨
      (s+2)*(k-s+1)-1 ≤ n) : False := by
  have hss := mul_nonneg (by omega : 0≤s) (sub_nonneg.mpr hs)
  have hkbound : 4*s+11 ≤ k := by nlinarith only [hs,hk,hss]
  have hdeg : 6*(s-1) < k := by nlinarith only [hs,hss,hk]
  have hk0 : 0≤k := by omega
  have small := hhalf hdeg
  have hp := mul_nonneg hk0 (sub_nonneg.mpr hkbound)
  have hn : 4*n<k*(k-1) := by nlinarith only [small,hp,hkbound,hs]
  have big := hrob (by omega) hn
  have horder : (s+1)*k+s < n := by nlinarith only [big,hk]
  rcases halt (by omega) hn with ⟨r,d,hd,hr,hwed⟩|hfull
  · have h₁ := mul_le_mul_of_nonneg_left hd hk0
    have h₂ := mul_le_mul_of_nonneg_left hr (show 0≤k+1 by omega)
    nlinarith only [h₁,h₂,hwed,horder]
  · have h₁ := mul_le_mul_of_nonneg_left hfull (show 0≤s-2 by omega)
    have h₂ := hthree hdeg
    have h₃ := mul_le_mul_of_nonneg_left hk (show 0≤s-5 by omega)
    have h₄ := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs)
    have h₅ := mul_nonneg (show 0≤s by omega) (show 0≤2*s-13 by omega)
    nlinarith only [h₁,h₂,h₃,h₄,h₅]

end Graph189LargeDegree

#print axioms Graph189LargeDegree.no_high_degree
