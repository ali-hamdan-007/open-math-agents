import Graph189FiniteDomain

namespace Graph189SyntheticBand
open Graph189FiniteDomain

/-- A single integral smaller-side cap works for both high-order exclusions
at every connectivity s≥5. The lower and upper band endpoints equal n. -/
def row (s k n : ℤ) : Band := ⟨s,k,n,n,k+k/(s-1)⟩

private theorem build {s k n R z : ℤ} (hs : 5 ≤ s) (degree : 6*(s-1)<k)
    (eqR : R = n-s-1-(s+1)*k) (room : s≤R) (enough : 2*k≤(s-1)*R)
    (z0 : 0≤z) (floor₁ : (s-1)*z≤k) (floor₂ : k<(s-1)*(z+1)) :
    valid ⟨s,k,n,n,k+z⟩ = true := by
  have k0 : 0<k := by omega
  have r0 : 0<R := by omega
  have st : 0<s-1 := by omega
  have doubleZ : 2*z ≤ R := by
    apply (mul_le_mul_iff_right₀ st).mp
    nlinarith only [floor₁,enough]
  have zlt : z<R := by omega
  have zHalf : 2*z ≤ k := by
    have h := mul_nonneg (show 0≤s-3 by omega) z0
    nlinarith only [floor₁,h]
  let h := n-s-1
  let a := k+z+1
  let b := h-k-a
  have hb : (s-1)*k ≤ b := by dsimp [b,h,a]; nlinarith only [eqR,zlt]
  have bk : k ≤ b := by
    have h := mul_nonneg (show 0≤s-2 by omega) k0.le
    nlinarith only [hb,h]
  have apos : 0≤a := by dsimp [a]; omega
  have ab : s*k*k < a*b := by
    have x := mul_nonneg apos (sub_nonneg.mpr hb)
    have y := mul_pos k0 (sub_pos.mpr floor₂)
    dsimp [a] at *
    nlinarith only [x,y]
  have bbw : s*k*k < b*(b-k) := by
    have y := mul_nonneg (show 0≤s-4 by omega) k0.le
    have bb : 2*k ≤ b-k := by nlinarith only [hb,y]
    have b0 : 0 ≤ b := by omega
    have x := mul_nonneg b0 (sub_nonneg.mpr bb)
    have q := mul_nonneg (by omega : 0≤2*k) (sub_nonneg.mpr hb)
    have p := mul_pos (by omega : 0<s-2) (mul_pos k0 k0)
    nlinarith only [x,q,p]
  have spare : s < s*(s-1)*s := by
    have u := mul_nonneg (show 0≤s-2 by omega) (show 0≤s by omega)
    have v := mul_nonneg (show 0≤s*(s-1)-1 by nlinarith only [u,hs]) (show 0≤s-1 by omega)
    nlinarith only [u,v,hs]
  have privateBound : (s*k-s*(s-1)+(k+z)+1)*s+(k+z) < h*s := by
    dsimp [h]
    have identity : (n-s-1)*s = ((s+1)*k+R)*s := by rw [show n-s-1 = (s+1)*k+R by omega]
    nlinarith only [identity,enough,doubleZ,floor₁,spare]
  have factor : k ≤ (s-2)*R := by
    have h := mul_nonneg (show 0≤s-3 by omega) r0.le
    nlinarith only [enough,h]
  have quotas (c : ℤ) (hc : c=1 ∨ c=2) :
      (s*k+k-(s-c)*(s-c-1)+c+1)*(s-c)+k < h*(s-c) := by
    have hd : 3 ≤ s-c := by omega
    have room' : k ≤ (s-c)*R := by
      have t := mul_nonneg (by omega : 0≤2-c) r0.le
      nlinarith only [factor,t]
    have positive : 0 < (s-c)*(s-c-1)-c-1 := by
      have u := mul_nonneg (by omega : 0≤s-c-3) (by omega : 0≤s-c+2)
      nlinarith only [u,hd,show c≤2 by omega]
    have prod := mul_pos positive (show 0<s-c by omega)
    have form : h = (s+1)*k+R := by dsimp [h]; linarith only [eqR]
    rw [form]
    nlinarith only [prod,room']
  simp only [valid,decide_eq_true_eq]
  change 5≤s ∧ _ ∧ n≤n ∧ k≤b ∧ 0≤b ∧ s*k*k<a*b ∧ s*k*k<b*(b-k) ∧
    (s+1)*k+2*s<n ∧ s*k+(k+z)<h ∧ _ ∧ k+z<2*k-s ∧ _ ∧ _
  refine ⟨hs,degree,le_rfl,bk,by omega,ab,bbw,?_,?_,privateBound,by omega,?_,?_⟩
  · nlinarith only [eqR,room]
  · dsimp [h]; nlinarith only [eqR,zlt]
  · simpa [quotaPass,h] using quotas 1 (Or.inl rfl)
  · simpa [quotaPass,h] using quotas 2 (Or.inr rfl)

/-- Either published order bound fails only at an order admitting a valid
separator certificate, uniformly over all k and s in this branch. -/
theorem high_order {s k n : ℤ} (hs : 5 ≤ s) (degree : 6*(s-1)<k)
    (high : (2*s+3)*k+4*s+4 ≤ 2*n ∨
      ((s+1)*(s-2)+3)*k ≤ (s-2)*(n-2*s-3)) : valid (row s k n) = true := by
  let R := n-s-1-(s+1)*k
  have hR : s≤R ∧ 2*k≤(s-1)*R := by
    rcases high with h | h
    · have hr : k+2*s+2 ≤ 2*R := by dsimp [R]; nlinarith only [h]
      have rs : s≤R := by omega
      have diff := mul_nonneg (by omega : 0≤s-5) (show 0≤R by omega)
      exact ⟨rs,by nlinarith only [hr,diff,hs]⟩
    · have hh : 3*k ≤ (s-2)*(R-s-2) := by dsimp [R]; nlinarith only [h]
      have rs : s+2≤R := by
        by_contra! bad
        have neg := mul_neg_of_pos_of_neg (by omega : 0<s-2) (by omega : R-s-2<0)
        linarith
      have lift := mul_nonneg (by omega : 0≤s-2) (by omega : 0≤s+2)
      exact ⟨by omega,by nlinarith only [hh,lift,rs,hs,degree]⟩
  have st : 0<s-1 := by omega
  apply build (R:=R) hs degree rfl hR.1 hR.2
  · exact Int.ediv_nonneg (by omega) st.le
  · simpa only [mul_comm] using (Int.ediv_mul_le k st.ne')
  · nlinarith only [Int.mul_ediv_add_emod k (s-1),Int.emod_lt_of_pos k st]

#print axioms high_order
end Graph189SyntheticBand
