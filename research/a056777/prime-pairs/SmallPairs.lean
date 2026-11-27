import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith

namespace A056777.SmallPairs

def pairExpr (a b : ℕ) : ℕ := a*(a-1)*b*(b-1)+12*(a+b-1)

theorem moment_pair_dvd (p q a b c : ℤ)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    p^3 ∣ a*(a-1)*b*(b-1)+12*(a+b-1) := by
  refine ⟨a*b*(p+q-1)-p*q*(a+b-1),?_⟩
  linear_combination a*b*hM-(a+b-1)*hZ

theorem moment_pair_dvd_nat (p q a b c : ℕ) (ha : 0<a) (hb : 0<b)
    (hpq : 0<p+q)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) : p^3 ∣ pairExpr a b := by
  have hM' := hM
  have hZ' := hZ
  have hpq' : 1 ≤ p+q := hpq
  have ha' : 1 ≤ a := ha
  have hb' : 1 ≤ b := hb
  have hab : 1 ≤ a+b := by omega
  zify [hpq'] at hM' hZ'
  unfold pairExpr
  zify [ha',hb',hab]
  exact moment_pair_dvd _ _ _ _ _ hM' hZ'

theorem pair_unique (p a b₁ b₂ : ℕ) (hp : p.Prime) (hpOdd : Odd p)
    (hp5 : 5 ≤ p) (ha : 3 ≤ a) (hap : a < p)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hpb₁ : b₁ < p) (hpb₂ : b₂ < p)
    (hd₁ : p^3 ∣ pairExpr a b₁) (hd₂ : p^3 ∣ pairExpr a b₂) :
    b₁=b₂ := by
  suffices strict : ∀ (x y : ℕ), 0<x → x<y → y<p →
      p^3 ∣ pairExpr a x → p^3 ∣ pairExpr a y → False by
    rcases lt_trichotomy b₁ b₂ with h|h|h
    · exact (strict b₁ b₂ hb₁ h hpb₂ hd₁ hd₂).elim
    · exact h
    · exact (strict b₂ b₁ hb₂ h hpb₁ hd₂ hd₁).elim
  intro x y hx hxy hyp hdx hdy
  let A := a*(a-1)
  let B := A*(x+y-1)+12
  have he : pairExpr a y = pairExpr a x + (y-x)*B := by
    have ha1 : 1≤a := by omega
    have hx1 : 1≤x := hx
    have hy1 : 1≤y := by omega
    have hax : 1≤a+x := by omega
    have hay : 1≤a+y := by omega
    have hsum : 1≤x+y := by omega
    unfold pairExpr B A
    zify [ha1,hx1,hy1,hax,hay,hsum,hxy.le]
    ring
  have hf : p^3 ∣ (y-x)*B := by
    rw [he] at hdy
    exact (Nat.dvd_add_iff_right (m:=pairExpr a x) (n:=(y-x)*B) hdx).mpr hdy
  have hcp : p.Coprime (y-x) := hp.coprime_iff_not_dvd.mpr fun hh => by
    have hh' := Nat.le_of_dvd (show 0<y-x by omega) hh
    omega
  have hgood := (hcp.pow_left 3).dvd_of_dvd_mul_left hf
  have hB0 : 0 < B := by dsimp [B]; omega
  have hBlt : B < 2*p^3 := by
    have hA : A ≤ (p-1)*(p-2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have ht : x+y-1 ≤ 2*p-3 := by omega
    have hprod := Nat.mul_le_mul hA ht
    have hp1 : 1≤p := by omega
    have hp2 : 2≤p := by omega
    have hp3 : 3≤2*p := by omega
    have hE : (p-1)*(p-2)*(2*p-3)+12 < 2*p^3 := by
      zify [hp1,hp2,hp3]
      have hpn : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      nlinarith [sq_nonneg ((p:ℤ)-5)]
    exact (Nat.add_le_add_right hprod 12).trans_lt hE
  obtain ⟨t,ht⟩ := hgood
  have hppos : 0<p^3 := by positivity
  have ht1 : t=1 := by
    have ht0 : t ≠ 0 := by intro hz; simp [hz] at ht
    by_contra ht'
    have ht2 : 2≤t := by omega
    have hh := Nat.mul_le_mul_left (p^3) ht2
    rw [Nat.mul_comm (p^3) 2, ← ht] at hh
    omega
  have hp3odd := Nat.odd_iff.mp (hpOdd.pow (n:=3))
  have hB2 : B%2=0 := by
    dsimp [B,A]
    have hA : (a*(a-1))%2=0 := by
      rw [Nat.mul_mod]
      have hn : a%2=0 ∨ (a-1)%2=0 := by omega
      rcases hn with hn|hn <;> simp [hn]
    rw [Nat.add_mod, Nat.mul_mod, hA]
    simp
  rw [ht1, mul_one] at ht
  omega

theorem two_small_one_large (p q a b c : ℤ)
    (hp : 5 ≤ p) (hq : 11 ≤ q) (hqp : 2*q<p)
    (ha : 0<a) (hab : a≤b) (hbc : b≤c)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    a<p ∧ b<p ∧ p^3<c ∧ a*b < p*q := by
  have hp0 : 0 < p := by omega
  have hp2 : 0 < p^2 := by positivity
  have hp3 : 0 < p^3 := by positivity
  have hq1 : 0 ≤ q-1 := by omega
  have hq2 : 0 < q+1 := by omega
  have hsum : p^3 ≤ a+b+c := by
    have hs : 0 ≤ (p^2+p+1)*(q+1) := by positivity
    linarith
  have hc : p<c := by
    have hs := mul_pos hp2 (show 0<p-3 by omega)
    nlinarith only [hab,hbc,hsum,hs,hp2,hp]
  have has : a<p := by
    by_contra! h
    have habp := mul_nonneg (show 0≤a-p by omega) (show 0≤b-p by omega)
    have hacp := mul_nonneg (show 0≤a-p by omega) (show 0≤c-p by omega)
    have hbcp := mul_nonneg (show 0≤b-p by omega) (show 0≤c-p by omega)
    have hS := mul_le_mul_of_nonneg_left hsum (show 0≤2*p-1 by omega)
    have hpq : 0 ≤ (p-q-1)*p^3 := mul_nonneg (by omega) hp3.le
    have hp3' : 0 ≤ (p-3)*p^2 := mul_nonneg (by omega) hp2.le
    nlinarith only [habp,hacp,hbcp,hS,hpq,hp3',hM]
  let f (x : ℤ) := 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2)*x-2*(p^4*q+12)
  have hfac (x : ℤ) : f x = 2*(x-a)*(x-b)*(x-c) := by
    dsimp [f]
    rw [← hL,← hZ]
    linear_combination -2*x*hM
  have hfp : f p < 0 := by
    have he : f p = -p*(q-1)*(p^3-1)-2*p^3*(p-1)-24 := by dsimp [f];ring
    rw [he]
    have h₁ : 0≤p*(q-1)*(p^3-1) :=
      mul_nonneg (mul_nonneg hp0.le hq1) (by omega)
    have h₂ : 0≤2*p^3*(p-1) := by
      exact mul_nonneg (by positivity) (by omega)
    linarith
  have hbs : b<p := by
    by_contra! hb
    rw [hfac] at hfp
    have h₁ := mul_nonneg (show 0≤b-p by omega) (show 0≤c-p by omega)
    have h₂ := mul_nonneg (show 0≤2*(p-a) by omega) h₁
    nlinarith only [hfp,h₂]
  have hf3 : f (p^3) < 0 := by
    have he : f (p^3) =
        -(q+1)*p^5*(p^3-1)-(q-1)*p^6*(p-1)-(q-1)*p^3*(p-1)-24 := by
      dsimp [f];ring
    rw [he]
    have h₁ : 0≤(q+1)*p^5*(p^3-1) :=
      mul_nonneg (by positivity) (by omega)
    have h₂ : 0≤(q-1)*p^6*(p-1) :=
      mul_nonneg (mul_nonneg hq1 (by positivity)) (by omega)
    have h₃ : 0≤(q-1)*p^3*(p-1) :=
      mul_nonneg (mul_nonneg hq1 (by positivity)) (by omega)
    linarith
  have hcs : p^3<c := by
    by_contra! hc'
    have h₀ : 0≤p^3-p := by
      have he := mul_nonneg hp0.le (show 0≤p^2-1 by omega)
      nlinarith only [he]
    have h₁ : 0≤2*(p^3-a)*(p^3-b) := by
      exact mul_nonneg (show 0≤2*(p^3-a) by omega) (by omega)
    rw [hfac] at hf3
    exact (not_lt_of_ge (mul_nonneg h₁ (by omega))) hf3
  refine ⟨has,hbs,hcs,?_⟩
  by_contra! h
  have hh := mul_le_mul h (show p^3+1≤c by omega)
    (show 0≤p^3+1 by omega) (mul_nonneg ha.le (ha.le.trans hab))
  have hpq12 : 12 < p*q := by
    have hh' := mul_le_mul hp hq (by decide : (0:ℤ) ≤ 11) hp0.le
    omega
  nlinarith only [hh,hpq12,hZ]

/-- Reconstruct q from the two small roots by division of bounded quantities. -/
theorem pair_recovers_q (p q a b c : ℤ)
    (hp : 0<p) (ha : 0<a) (hb : 0<b) (hap : a<p)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    let G := a*(a-1)*b*(b-1)+12*(a+b-1)
    let B := p*(a+b-1)-a*b
    0<B ∧ q=(a*b*(p-1)-G/p^3)/B := by
  dsimp
  let G := a*(a-1)*b*(b-1)+12*(a+b-1)
  let B := p*(a+b-1)-a*b
  have hB : 0<B := by
    have h₁ := mul_nonneg hp.le (show 0≤a-1 by omega)
    have h₂ := mul_pos hb (sub_pos.mpr hap)
    dsimp [B]
    nlinarith only [h₁,h₂]
  have hp3 : p^3 ≠ 0 := by positivity
  have he : G = p^3*(a*b*(p-1)-q*B) := by
    dsimp [G,B]
    linear_combination a*b*hM-(a+b-1)*hZ
  refine ⟨hB,?_⟩
  change q=(a*b*(p-1)-G/p^3)/B
  rw [he,Int.mul_ediv_cancel_left _ hp3]
  have hnum : a*b*(p-1)-(a*b*(p-1)-q*B)=q*B := by ring
  rw [hnum,mul_comm q B,Int.mul_ediv_cancel_left _ hB.ne']

end A056777.SmallPairs

#print axioms A056777.SmallPairs.moment_pair_dvd_nat
#print axioms A056777.SmallPairs.pair_unique

#print axioms A056777.SmallPairs.two_small_one_large

#print axioms A056777.SmallPairs.pair_recovers_q
