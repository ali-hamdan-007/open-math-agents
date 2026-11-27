import Erdos307CrossCoprime
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

namespace Erdos307Structure

/-- With a first left closing member absorbed into A,U, integrality of the
opposite two symmetric functions is equivalent to one modulus-N² condition
on the last left member b, plus the sign of the recovered sum. -/
theorem two_pair_integral_iff {A U N V b : ℕ}
    (hdet : U * V ≤ A * N) (hN : 0 < N) (hNV : N.Coprime V) :
    let K := A * N - U * V
    (∃ q r : ℕ, N * q = U * b + A ∧ A * b = V * q + N * r) ↔
      V * A ≤ K * b ∧ K * b ≡ V * A [MOD N ^ 2] := by
  let K := A * N - U * V
  change (∃ q r : ℕ, N * q = U * b + A ∧ A * b = V * q + N * r) ↔
    V * A ≤ K * b ∧ K * b ≡ V * A [MOD N ^ 2]
  have hK : K + U * V = A * N := Nat.sub_add_cancel hdet
  constructor
  · rintro ⟨q, r, hl, hr⟩
    have he : K * b = V * A + N ^ 2 * r := by
      nlinarith [congrArg (· * b) hK, congrArg (V * ·) hl, congrArg (N * ·) hr]
    have hle : V * A ≤ K * b := by omega
    refine ⟨hle, ((Nat.modEq_iff_dvd' hle).mpr ?_).symm⟩
    exact ⟨r, by omega⟩
  · rintro ⟨hs, hmod⟩
    obtain ⟨r, hr⟩ := (Nat.modEq_iff_dvd' hs).mp hmod.symm
    have he : K * b = V * A + N ^ 2 * r := by omega
    have hsum : A * N * b = V * (U * b + A) + N ^ 2 * r := by
      nlinarith [congrArg (· * b) hK]
    have hdivN : N ∣ A * N * b :=
      dvd_mul_of_dvd_left (dvd_mul_left N A) b
    have hrdiv : N ∣ N ^ 2 * r := dvd_mul_of_dvd_left
      (by rw [pow_two]; exact dvd_mul_right N N) r
    have hp : N ∣ V * (U * b + A) :=
      (Nat.dvd_add_iff_left hrdiv).mpr (hsum ▸ hdivN)
    obtain ⟨q, hq⟩ := hNV.dvd_of_dvd_mul_left hp
    have hleft : N * q = U * b + A := hq.symm
    have hright : A * b = V * q + N * r := by
      apply Nat.eq_of_mul_eq_mul_left hN
      nlinarith [congrArg (V * ·) hleft]
    exact ⟨q, r, hleft, hright⟩

/-- If any integral two-pair completion exists, the coefficient K is a unit
modulo N². This uses only reduced right cofactors and coprimality of A and N. -/
theorem two_pair_coprime_coefficient {A U N V b q : ℕ}
    (hdet : U * V ≤ A * N) (hNA : N.Coprime A) (hNV : N.Coprime V)
    (hl : N * q = U * b + A) :
    (N ^ 2).Coprime (A * N - U * V) := by
  have hNU : N.Coprime U := by
    unfold Nat.Coprime
    let g := N.gcd U
    have hgN : g ∣ N := Nat.gcd_dvd_left _ _
    have hgU : g ∣ U := Nat.gcd_dvd_right _ _
    have hgA : g ∣ A := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left hgU b)).mpr
      (hl ▸ dvd_mul_of_dvd_left hgN q)
    exact Nat.eq_one_of_dvd_coprimes hNA hgN hgA
  let K := A * N - U * V
  have hK : K + U * V = A * N := Nat.sub_add_cancel hdet
  have hc : N.Coprime K := by
    unfold Nat.Coprime
    let g := N.gcd K
    have hgN : g ∣ N := Nat.gcd_dvd_left _ _
    have hgK : g ∣ K := Nat.gcd_dvd_right _ _
    have hgUV : g ∣ U * V := (Nat.dvd_add_iff_right hgK).mpr
      (hK.symm ▸ dvd_mul_of_dvd_right hgN A)
    exact Nat.eq_one_of_dvd_coprimes (hNU.mul_right hNV) hgN hgUV
  exact hc.pow_left 2

/-- Any two integral candidate closing members b for fixed A,U,N,V agree
modulo N². In every interval of length N² there is therefore at most one. -/
theorem two_pair_b_modEq {A U N V b₁ b₂ q₁ q₂ r₁ r₂ : ℕ}
    (hdet : U * V ≤ A * N) (hN : 0 < N) (hNA : N.Coprime A) (hNV : N.Coprime V)
    (hL₁ : N * q₁ = U * b₁ + A) (hR₁ : A * b₁ = V * q₁ + N * r₁)
    (hL₂ : N * q₂ = U * b₂ + A) (hR₂ : A * b₂ = V * q₂ + N * r₂) :
    b₁ ≡ b₂ [MOD N ^ 2] := by
  have hc := two_pair_coprime_coefficient hdet hNA hNV hL₁
  have h₁ := ((two_pair_integral_iff hdet hN hNV).mp ⟨q₁,r₁,hL₁,hR₁⟩).2
  have h₂ := ((two_pair_integral_iff hdet hN hNV).mp ⟨q₂,r₂,hL₂,hR₂⟩).2
  exact Nat.ModEq.cancel_left_of_coprime hc (h₁.trans h₂.symm)

#print axioms two_pair_integral_iff
#print axioms two_pair_coprime_coefficient
#print axioms two_pair_b_modEq

end Erdos307Structure
