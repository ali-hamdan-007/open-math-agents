import Graph189WindowCover
import Graph189LargeDegree
import Graph189InfiniteTail
import Graph189NineCutDebit

namespace Graph189EightCutoff

/-- A common set of integer necessary conditions forces connectivity at most
eight. The genuine-low branch includes the cut population and mixed debit
only for the use of the connectivity-nine theorem. -/
theorem connectivity_le_eight {s k n e w : ℤ} (hs : 5≤s) (hk : 3*s<k)
    (he : 0≤e) (hemax : e≤2*k) (hore : n≤3*k+1+k*e)
    (hwlo : 2*(n-2*k)+k*e≤(k+1)*w)
    (hwhi : w*(n-2*k-e-2)≤k*(k+e))
    (hbase : (s+1)*(k-s+2)-1≤n)
    (hside : (n-2*k-1)*(k-s)≤s*k*k)
    (hbridge : 4*s≤k → 4*n<k*(k-1) → (s+2)*(k-2*s+2)-1≤n)
    (hhalf : 6*(s-1)<k → 2*n<(2*s+3)*k+4*s+4)
    (hthree : 6*(s-1)<k → (s-2)*(n-2*s-3)<((s+1)*(s-2)+3)*k)
    (halt : 4*s≤k → 4*n<k*(k-1) →
      (∃ r d x y : ℤ, 1≤d ∧ r≤s ∧ 0≤x ∧ x≤y ∧ x*(y-k)≤s*k*k ∧
        k*d≤2*k+(k+1)*r-n ∧ (r-1)*(k-s+1)≤(s+1)*k-n+x+s+r*(e+s-1)) ∨
      (s+2)*(k-s+1)-1≤n) :
    s≤8 := by
  by_contra! hlarge
  have h9 : 9≤s := by omega
  have htail := Graph189InfiniteTail.finite_rectangle_of_width
    (s := (s:ℚ)) (k := (k:ℚ)) (n := (n:ℚ)) (e := (e:ℚ)) (w := (w:ℚ))
    (by exact_mod_cast hs) (by exact_mod_cast hk) (by exact_mod_cast he)
    (by exact_mod_cast hemax) (by exact_mod_cast hore) (by exact_mod_cast hwlo)
    (by exact_mod_cast hwhi) (by exact_mod_cast hbase) (by exact_mod_cast hside)
    (by intro h₁ h₂; exact_mod_cast hbridge (by exact_mod_cast h₁) (by exact_mod_cast h₂))
    (by intro h; exact_mod_cast hhalf (by exact_mod_cast h))
    (by intro h; exact_mod_cast hthree (by exact_mod_cast h))
  have h100 : s<100 := by exact_mod_cast htail.1
  have hk0 : 0≤k := by omega
  have hf : 0≤n-2*k-e-2 := by
    have h₁ := mul_nonneg (show 0≤s-3 by omega) (sub_nonneg.mpr hk.le)
    have h₂ := mul_nonneg (show 0≤s by omega) (sub_nonneg.mpr hs)
    nlinarith only [h₁,h₂,hbase,hemax,hs]
  have hw₁ := mul_le_mul_of_nonneg_left hwlo hf
  have hw₂ := mul_le_mul_of_nonneg_left hwhi (show 0≤k+1 by omega)
  have hw : (n-2*k-e-2)*(2*(n-2*k)+k*e)≤k*(k+1)*(k+e) := by nlinarith only [hw₁,hw₂]
  by_cases hsmall : k≤Graph189WindowCover.lastDegree s
  · let t : Fin 100 := ⟨s.toNat, by omega⟩
    have ht : (t.val:ℤ)=s := by dsimp [t]; omega
    exact Graph189WindowCover.no_lower_range t (by omega)
      (by simpa only [ht] using hk) (by simpa only [ht] using hsmall)
      he hemax hore hw (by simpa only [ht] using hbase) (by simpa only [ht] using hbridge)
  by_cases heq : s=9
  · subst s
    change ¬ k≤162 at hsmall
    have kk : 163≤k := by omega
    have hu := hhalf (by omega)
    have hm := mul_nonneg hk0 (show 0≤k-50 by omega)
    have hcut : 4*n < k*(k-1) := by nlinarith only [hu,hm,kk]
    rcases halt (by omega) hcut with ⟨r,d,x,y,hd,hr,hx,hxy,hp,hl,hdebit⟩|hlift
    · apply Graph189NineCutDebit.no_low_at_nine (n:=(n:ℚ)) (k:=(k:ℚ)) (e:=(e:ℚ))
        (w:=(w:ℚ)) (x:=(x:ℚ)) (y:=(y:ℚ)) (d:=(d:ℚ)) (r:=(r:ℚ))
      · exact_mod_cast kk
      · exact_mod_cast (show 10*k-71≤n by nlinarith only [hbase])
      · exact_mod_cast he
      · exact_mod_cast hemax
      · exact_mod_cast hwlo
      · exact_mod_cast hwhi
      · exact_mod_cast hx
      · exact_mod_cast hxy
      · exact_mod_cast hp
      · exact_mod_cast hd
      · rcases (show r=9 ∨ r≤8 by omega) with h|h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
      · exact_mod_cast hl
      · exact_mod_cast (show (r-1)*(k-8)≤10*k-n+x+9+r*(e+8) by nlinarith only [hdebit])
    · have hf9 : 11*k-89≤n := by nlinarith only [hlift]
      by_cases h192 : k≤192
      · apply Graph189NineCutDebit.no_lifted_nine_middle
            (n:=(n:ℚ)) (k:=(k:ℚ)) (e:=(e:ℚ)) (w:=(w:ℚ))
        · exact_mod_cast kk
        · exact_mod_cast h192
        · exact_mod_cast hf9
        · exact_mod_cast hore
        · rcases (show e≤7 ∨ 8≤e by omega) with h|h
          · left; exact_mod_cast h
          · right; exact_mod_cast h
        · exact_mod_cast he
        · exact_mod_cast hemax
        · exact_mod_cast hwlo
        · exact_mod_cast hwhi
      · have upper := hthree (by omega)
        nlinarith only [upper,hf9,h192]
  · simp only [Graph189WindowCover.lastDegree,if_neg heq] at hsmall
    apply Graph189LargeDegree.no_high_degree (s:=s) (k:=k) (n:=n) (by omega)
      (by nlinarith only [hsmall]) hhalf hthree hbridge
    intro h₁ h₂
    rcases halt h₁ h₂ with ⟨r,d,x,y,hd,hr,_,_,_,hl,_⟩|h
    · exact Or.inl ⟨r,d,hd,hr,hl⟩
    · exact Or.inr h

end Graph189EightCutoff

#print axioms Graph189EightCutoff.connectivity_le_eight
