import Graph189FiniteDomain

namespace Graph189ValidBand
open Graph189FiniteDomain

/-- The geometric consequences of a checked band hold for all cut
populations, independently of how the band was obtained. The last two
strict inequalities contradict the private and singleton support budgets. -/
theorem consequences {r : Band} (hv : valid r=true) {x y : ℤ}
    (hx : 0≤x) (hxy : x≤y) (hsum : r.low-r.s-1≤x+y)
    (hp : x*y≤r.k*x+r.s*r.k*r.k) :
    x≤r.cap ∧ r.s*r.k<y ∧ r.cap<2*r.k-r.s ∧
    (r.s*r.k-r.s*(r.s-1)+x+1)*r.s+x < (x+y)*r.s ∧
    ∀ c : ℤ, c=1 ∨ c=2 → x≤r.k →
      (r.s*r.k+x-(r.s-c)*(r.s-c-1)+c+1)*(r.s-c)+x < (x+y)*(r.s-c) := by
  simp only [valid,decide_eq_true_eq] at hv
  obtain ⟨hs,_,_,hb,_,hl,hr,_,hy,hq,hcap,h1,h2⟩ := hv
  have hsmall := population_bound hx hxy hsum hp hb hl hr
  have hs0 : 0≤r.s := by omega
  refine ⟨hsmall, by omega, hcap, ?_, ?_⟩
  · have ha := mul_le_mul_of_nonneg_right hsum hs0
    have hb := mul_le_mul_of_nonneg_right hsmall hs0
    nlinarith
  · intro c hc hxk
    have hsingle : quotaPass r c=true := by rcases hc with rfl|rfl <;> assumption
    simp only [quotaPass,decide_eq_true_eq] at hsingle
    have hd : 0≤r.s-c := by omega
    have ha := mul_le_mul_of_nonneg_right hsum hd
    have hb := mul_le_mul_of_nonneg_right hxk hd
    nlinarith

end Graph189ValidBand

#print axioms Graph189ValidBand.consequences
