import Graph189EightCutoff
import Graph189SmallWindowCover
import Graph189ValidBand
import Graph189FiveCutDebit

namespace Graph189ScalarConclusion
open Graph189FiniteDomain Graph189SmallWindowCover

/-- The full unbounded scalar reduction. The effective deficit d is zero if
the strong order lift is available, and otherwise comes from a low vertex
on a minimum cut. Every positive d carries the actual low-cut witnesses.
The output holds for every graph order permitted by the input inequalities. -/
theorem terminal_band {s k n e w d : ℤ} (hs : 5≤s) (hk26 : 26≤k) (hk : 3*s<k)
    (he : 0≤e) (hemax : e≤2*k) (hore : n≤3*k+1+k*e)
    (hwlo : 2*(n-2*k)+k*e≤(k+1)*w)
    (hwhi : w*(n-2*k-e-2)≤k*(k+e))
    (hbase : (s+1)*(k-s+2)-1≤n)
    (hside : (n-2*k-1)*(k-s)≤s*k*k)
    (hhalf : 6*(s-1)<k → 2*n<(2*s+3)*k+4*s+4)
    (hthree : 6*(s-1)<k → (s-2)*(n-2*s-3)<((s+1)*(s-2)+3)*k)
    (hd : 0≤d)
    (hlow : 0<d → ∃ r x y : ℤ, r≤s ∧ d≤r-1 ∧ 0≤x ∧ x≤y ∧ x+y=n-s ∧
      x*(y-k)≤s*k*k ∧ k*d≤2*k+(k+1)*r-n ∧
      (r-1)*(k-s+1)≤(s+1)*k-n+x+s+r*(e+s-1))
    (hlift : 3*s<2*(k-d-1) → 2*s≤k-2*d-2 → 4*n<k*(k-1) →
      (s+2)*(k-d-s+1)-1≤n) :
    s≤8 ∧ valid (band s k)=true ∧ (band s k).low≤n := by
  have hk0 : 0≤k := by omega
  have hdmax : d≤s-1 := by
    by_cases hp : 0<d
    · obtain ⟨r,_,_,hr,hh,_⟩ := hlow hp
      omega
    · omega
  have hbridge : 4*s≤k → 4*n<k*(k-1) → (s+2)*(k-2*s+2)-1≤n := by
    intro h₁ h₂
    have hh := hlift (by omega) (by omega) h₂
    have hm := mul_nonneg (show 0≤s+2 by omega) (sub_nonneg.mpr hdmax)
    nlinarith only [hm,hh]
  have hAlt : 4*s≤k → 4*n<k*(k-1) →
      (∃ r d x y : ℤ, 1≤d ∧ r≤s ∧ 0≤x ∧ x≤y ∧ x*(y-k)≤s*k*k ∧
        k*d≤2*k+(k+1)*r-n ∧ (r-1)*(k-s+1)≤(s+1)*k-n+x+s+r*(e+s-1)) ∨
      (s+2)*(k-s+1)-1≤n := by
    intro ha hb
    by_cases hp : 0<d
    · obtain ⟨r,x,y,hr,_,hx,hxy,_,hc,hw,hm⟩ := hlow hp
      exact Or.inl ⟨r,d,x,y,by omega,hr,hx,hxy,hc,hw,hm⟩
    · have hzero : d=0 := by omega
      have hh := hlift (by omega) (by omega) hb
      exact Or.inr (by simpa only [hzero,sub_zero] using hh)
  have hs8 := Graph189EightCutoff.connectivity_le_eight hs hk he hemax hore hwlo hwhi
    hbase hside hbridge hhalf hthree hAlt
  have hkc := Graph189InfiniteTail.degree_lt_cutoff (s:=(s:ℚ)) (k:=(k:ℚ))
    (n:=(n:ℚ)) (by exact_mod_cast hs)
    (by intro h₁ h₂; exact_mod_cast hbridge (by exact_mod_cast h₁) (by exact_mod_cast h₂))
    (by intro h; exact_mod_cast hhalf (by exact_mod_cast h))
  have hkmax : k<4*s^2+8*s-2 := by exact_mod_cast hkc
  have hf : 0≤n-2*k-e-2 := by
    have h₁ := mul_nonneg (show 0≤s-3 by omega) (sub_nonneg.mpr hk.le)
    have h₂ := mul_nonneg (show 0≤s by omega) (sub_nonneg.mpr hs)
    nlinarith only [h₁,h₂,hbase,hemax,hs]
  have hw₁ := mul_le_mul_of_nonneg_left hwlo hf
  have hw₂ := mul_le_mul_of_nonneg_left hwhi (show 0≤k+1 by omega)
  have hwidth : (n-2*k-e-2)*(2*(n-2*k)+k*e)≤k*(k+1)*(k+e) :=
    by nlinarith only [hw₁,hw₂]
  have hedge : 0<d → k*d≤2*k+(k+1)*s-n := by
    intro hp
    obtain ⟨r,_,_,hr,_,_,_,_,_,hw,_⟩ := hlow hp
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤k+1 by omega)
    omega
  have hfiv : s=5 → 46≤k → k≤58 → d=0 := by
    intro hs5 h46 h58
    subst s
    by_contra! hn
    obtain ⟨r,x,y,hr,_,hx,hxy,hsum,hp,hw,hm⟩ := hlow (by omega)
    have hn7 : 7*k-57≤n := by
      by_cases hq : 4*n<k*(k-1)
      · have hh := hbridge (by omega) hq
        nlinarith only [hh]
      · have hh := mul_nonneg hk0 (show 0≤k-46 by omega)
        nlinarith only [hh,hq,h46]
    exact Graph189FiveCutDebit.no_low (d:=d) (r:=r) h46 h58 hn7 he hemax hwidth hx hxy hsum hp
      (by omega) hr (by nlinarith only [hw]) (by nlinarith only [hm])
  have hl := lower_le hs hk hbase hbridge hd hdmax hedge hfiv hlift
  exact ⟨hs8,terminal_quotas hs hs8 hk26 hk hkmax he hemax hore hwidth hl hside hhalf hthree,hl⟩

end Graph189ScalarConclusion

#print axioms Graph189ScalarConclusion.terminal_band
