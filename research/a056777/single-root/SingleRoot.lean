import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace A056777.SingleRoot

def F {R : Type*} [CommRing R] (p q x : R) : R :=
  2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)

theorem discriminant_pos (p q x : ℤ) (hq : 0 ≤ q) (hgap : q+4 ≤ x)
    (hxp : x<p) (hroot : F p q x=0) : 2*p*q+q^2 < p^2 := by
  let G := -(2*p+q)*x^2+2*p*(p+q)*x-2*p^2*q
  let E := p^2*(x-q-1)+(p+1)*(q+1)*(x-1)-2*x^2+2
  have hp : 0 < p := by omega
  have hx : 0 < x := by omega
  have hF : F p q x = p^2*G-x*E-24 := by dsimp [F,G,E]; ring
  have hE : 0 < E := by
    have h₁ := mul_nonneg (sq_nonneg p) (show 0 ≤ x-q-4 by omega)
    have h₂ := mul_nonneg (show 0 ≤ p-x by omega) (show 0 ≤ p+x by omega)
    have h₃ : 0 ≤ (p+1)*(q+1)*(x-1) := by
      have : 0 ≤ x-1 := by omega
      positivity
    dsimp [E]
    nlinarith only [h₁,h₂,h₃,sq_nonneg p]
  have hg : 0 < G := by
    have : 0 < p^2*G := by nlinarith only [hF,hroot,mul_pos hx hE]
    exact pos_of_mul_pos_right this (sq_nonneg p)
  have hsq : (2*p+q)*G=p^2*(p^2-2*p*q-q^2)-((2*p+q)*x-p*(p+q))^2 := by
    dsimp [G]
    ring
  have hprod : 0 < p^2*(p^2-2*p*q-q^2) := by
    nlinarith only [hsq, sq_nonneg ((2*p+q)*x-p*(p+q)),
      mul_pos (show 0<2*p+q by omega) hg]
  have hdisc := pos_of_mul_pos_right hprod (sq_nonneg p)
  linarith

private theorem cast_F {n : ℕ} (p q x : ℕ) (h : F (p:ℤ) q x=0) :
    F (p:ZMod n) q x=0 := by
  simpa [F] using congrArg (fun t : ℤ => (t:ZMod n)) h

private theorem prime_mod3_ne_zero {x : ℕ} (hx : x.Prime) (hx3 : 3 < x) : x%3 ≠ 0 := by
  intro h
  have hd : 3 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr h
  rcases (Nat.dvd_prime hx).mp hd with h|h <;> omega

theorem gap_mod3 {p q x : ℕ} (hpq : p%3 ≠ q%3)
    (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (hp3 : 3<p) (hq3 : 3<q) (hx3 : 3<x)
    (hroot : F (p:ℤ) q x=0) : (x-q)%3 ≠ 1 ∨ x<q := by
  by_cases hxq : x<q
  · exact Or.inr hxq
  left
  intro h
  have hpn := prime_mod3_ne_zero hp hp3
  have hqn := prime_mod3_ne_zero hq hq3
  have hxn := prime_mod3_ne_zero hx hx3
  have hp2 : p%3=2 := by omega
  have hq1 : q%3=1 := by omega
  have hx2 : x%3=2 := by omega
  have h3 := cast_F (n:=3) p q x hroot
  have hp' : (p:ZMod 3)=2 := calc
    (p:ZMod 3) = (p%3:ℕ) := by simp
    _ = 2 := by rw [hp2]; rfl
  have hq' : (q:ZMod 3)=1 := calc
    (q:ZMod 3) = (q%3:ℕ) := by simp
    _ = 1 := by rw [hq1]; rfl
  have hx' : (x:ZMod 3)=2 := calc
    (x:ZMod 3) = (x%3:ℕ) := by simp
    _ = 2 := by rw [hx2]; rfl
  rw [hp',hq',hx'] at h3
  exact (by decide : F (2:ZMod 3) 1 2 ≠ 0) h3

theorem gap_ge_six {p q x : ℕ} (hpq : p%3 ≠ q%3)
    (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (hp3 : 3<p) (hq3 : 3<q) (hgap : q+4≤x)
    (hroot : F (p:ℤ) q x=0) : q+6≤x := by
  have hx3 : 3<x := by omega
  have hxodd := hx.eq_two_or_odd.resolve_left (by omega)
  have hqodd := hq.eq_two_or_odd.resolve_left (by omega)
  rcases gap_mod3 hpq hp hq hx hp3 hq3 hx3 hroot with h|h <;> omega

theorem gap_ge_twelve_of_mod_five {p q x : ℕ} (hpq : p%3 ≠ q%3)
    (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (hp3 : 3<p) (hq3 : 3<q) (hgap : q+4≤x)
    (hp5 : p%5=2) (hq5 : q%5=2)
    (hroot : F (p:ℤ) q x=0) : q+12≤x := by
  have hx3 : 3<x := by omega
  have hxodd := hx.eq_two_or_odd.resolve_left (by omega)
  have hqodd := hq.eq_two_or_odd.resolve_left (by omega)
  have hgap6 := gap_ge_six hpq hp hq hx hp3 hq3 hgap hroot
  have h6 : x ≠ q+6 := by
    intro hx6
    have h5 := cast_F (n:=5) p q x hroot
    have hp' : (p:ZMod 5)=2 := calc
      (p:ZMod 5) = (p%5:ℕ) := by simp
      _ = 2 := by rw [hp5]; rfl
    have hq' : (q:ZMod 5)=2 := calc
      (q:ZMod 5) = (q%5:ℕ) := by simp
      _ = 2 := by rw [hq5]; rfl
    rw [hx6, Nat.cast_add, Nat.cast_ofNat, hp', hq'] at h5
    exact (by decide : F (2:ZMod 5) 2 (2+6) ≠ 0) h5
  have h8 : x ≠ q+8 := by
    intro h
    have hd : 5 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    rcases (Nat.dvd_prime hx).mp hd with hh|hh <;> omega
  rcases gap_mod3 hpq hp hq hx hp3 hq3 hx3 hroot with h|h <;> omega

theorem bound_of_twelve_offset (p q : ℤ) (hq : 4000 ≤ q) (hp : 0 < p)
    (hF : F p q (q+12) ≤ 0) : 22*p^2<q^3 := by
  by_contra! hpow
  have hratio : 40*q ≤ 3*p := by
    by_contra! habs
    have h₁ := mul_pos (show 0<40*q-3*p by omega) (show 0<40*q+3*p by omega)
    have h₂ := mul_nonneg (sq_nonneg q) (show 0≤q-4000 by omega)
    nlinarith only [h₁,h₂,hpow]
  let A := q^3+24*q^2+155*q+132
  let C := q^3+48*q^2+707*q+3276
  have hformula : F p q (q+12)=24*p^3*(p-q-12)-(p^2+p)*A+C := by
    dsimp [F,A,C]
    ring
  have hA : 150*A ≤ 151*q^3 := by
    have h₁ := mul_nonneg (sq_nonneg q) (show 0 ≤ q-4000 by omega)
    have h₂ := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ q-4000 by omega)
    dsimp [A]
    nlinarith only [h₁,h₂,hq,sq_nonneg q]
  have hC : 0≤C := by
    have : 0≤q := by omega
    dsimp [C]
    positivity
  have hfirst := mul_le_mul_of_nonneg_left (show 12*p≤13*(p-q-12) by omega)
    (show 0≤24*p^3 by positivity)
  have hmid := mul_le_mul_of_nonneg_left (hA.trans
    (mul_le_mul_of_nonneg_left hpow (by decide))) (show 0≤p^2+p by positivity)
  have hmid' := mul_le_mul_of_nonneg_right
    (show 10000*(p^2+p)≤10001*p^2 by
      nlinarith only [mul_nonneg hp.le (show 0≤p-10000 by omega)])
    (show 0≤151*22*p^2 by positivity)
  have hpp : 0 < p^4 := by positivity
  rw [hformula] at hF
  nlinarith only [hF,hfirst,hmid,hmid',hC,hpp]

theorem bound_of_three_twelve_spaced_roots (p q a b c : ℤ)
    (hq : 4000 ≤ q) (hp : 0 < p)
    (ha : q+12 ≤ a) (hb : q+12 ≤ b) (hc : q+12 ≤ c)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) : 22*p^2<q^3 := by
  apply bound_of_twelve_offset p q hq hp
  let y := q+12
  change F p q y ≤ 0
  have hf : F p q y = 2*(y-a)*(y-b)*(y-c) := by
    have hsum : 2*(a*b+a*c+b*c)=
        2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2 := by
      nlinarith only [hL,hM]
    dsimp [F]
    rw [←hL,←hsum,←hZ]
    ring
  rw [hf]
  have h1 : y-a≤0 := by dsimp [y]; omega
  have h2 : y-b≤0 := by dsimp [y]; omega
  have h3 : y-c≤0 := by dsimp [y]; omega
  have h12 := mul_nonneg_of_nonpos_of_nonpos h1 h2
  have h123 := mul_nonpos_of_nonneg_of_nonpos h12 h3
  nlinarith only [h123]

#print axioms discriminant_pos
#print axioms gap_ge_six
#print axioms gap_ge_twelve_of_mod_five
#print axioms bound_of_three_twelve_spaced_roots

end A056777.SingleRoot
