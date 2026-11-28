import Graph189FiniteDomain

namespace Graph189FiniteDomain

/-- The private-support alternative is arithmetically impossible at every
order in every certified band, using only its cross-population consequence. -/
theorem private_quota_impossible {r : Band} (hm : r ∈ terminalBands)
    {x y : Int} (hcap : x ≤ r.cap) (hsize : r.low-r.s-1 ≤ x+y)
    (hprivate : (x+y)*r.s ≤
      (r.s*r.k-r.s*(r.s-1)+x+1)*r.s+x) : False := by
  have h := List.all_eq_true.mp terminal_bands_checked r hm
  simp only [valid, decide_eq_true_eq] at h
  obtain ⟨hs, _, _, _, _, _, _, _, _, hq, _, _, _⟩ := h
  have hs0 : 0 ≤ r.s := by omega
  have h₁ := mul_le_mul_of_nonneg_right hsize hs0
  have h₂ := mul_le_mul_of_nonneg_right hcap hs0
  nlinarith

/-- The residual-singleton alternatives at one and two common labels both
contradict the quota at the order lower bound of their row. -/
theorem small_common_quota_impossible {r : Band} (hm : r ∈ terminalBands)
    {c x y : Int} (hc : c=1 ∨ c=2)
    (hcap : x ≤ r.k) (hsize : r.low-r.s-1 ≤ x+y)
    (hquota : (x+y)*(r.s-c) ≤
      (r.s*r.k+x-(r.s-c)*(r.s-c-1)+c+1)*(r.s-c)+x) : False := by
  have h := List.all_eq_true.mp terminal_bands_checked r hm
  simp only [valid, decide_eq_true_eq] at h
  obtain ⟨hs, _, _, _, _, _, _, _, _, _, _, h1, h2⟩ := h
  have hq : quotaPass r c = true := by rcases hc with rfl|rfl <;> assumption
  simp only [quotaPass, decide_eq_true_eq] at hq
  have hd : 0 ≤ r.s-c := by omega
  have h₁ := mul_le_mul_of_nonneg_right hsize hd
  have h₂ := mul_le_mul_of_nonneg_right hcap hd
  nlinarith

end Graph189FiniteDomain

#print axioms Graph189FiniteDomain.private_quota_impossible
#print axioms Graph189FiniteDomain.small_common_quota_impossible
