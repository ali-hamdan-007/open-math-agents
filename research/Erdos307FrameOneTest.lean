import Erdos307CrossCoprime
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

open Finset

namespace Erdos307Structure

private theorem frame_divisibility_forward {M M' N N' : ℕ}
    (hlt : M' * N' ≤ M * N) (hMN : M.Coprime N) (hNN' : N.Coprime N') :
    let d := M * N - M' * N'
    d ∣ M * N' + N ^ 2 → d ∣ M' * N + M ^ 2 := by
  let d := M * N - M' * N'
  change d ∣ M * N' + N ^ 2 → d ∣ M' * N + M ^ 2
  intro h
  have hdN : d.Coprime N := by
    unfold Nat.Coprime
    let g := d.gcd N
    have hgN : g ∣ N := Nat.gcd_dvd_right d N
    have hg_sum : g ∣ M * N' + N ^ 2 := (Nat.gcd_dvd_left d N).trans h
    have hg_sq : g ∣ N ^ 2 := hgN.trans (by rw [pow_two]; exact dvd_mul_right N N)
    exact Nat.eq_one_of_dvd_coprimes (hMN.symm.mul_right hNN') hgN
      ((Nat.dvd_add_iff_left hg_sq).mpr hg_sum)
  have hbase : d + M' * N' = M * N := Nat.sub_add_cancel hlt
  have hbalance : N * (M' * N + M ^ 2) = M' * (M * N' + N ^ 2) + M * d := by
    apply Nat.add_right_cancel (m := M * (M' * N'))
    calc
      _ = M' * (M * N' + N ^ 2) + M * (M * N) := by ring
      _ = _ := by rw [← hbase]; ring
  have hmul : d ∣ N * (M' * N + M ^ 2) := by
    rw [hbalance]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left d M)
  exact hdN.dvd_of_dvd_mul_left hmul

/-- For positive-determinant coprime frames either completion divisibility
forces the other. Each base product must be coprime to its own cofactor sum. -/
theorem frame_divisibility_iff {M M' N N' : ℕ}
    (hlt : M' * N' ≤ M * N) (hMN : M.Coprime N) (hMM' : M.Coprime M')
    (hNN' : N.Coprime N') :
    let d := M * N - M' * N'
    (d ∣ M * N' + N ^ 2) ↔ (d ∣ M' * N + M ^ 2) := by
  constructor
  · exact frame_divisibility_forward hlt hMN hNN'
  · have hlt' : N' * M' ≤ N * M := by simpa only [mul_comm] using hlt
    simpa only [mul_comm] using
      (frame_divisibility_forward (M := N) (M' := N') (N := M) (N' := M')
        hlt' hMN.symm hMM')

/-- In the erased-set frame criterion, the second divisibility filter is redundant. -/
theorem frame_divisibility_iff_of_sets {P Q : Finset ℕ}
    (hp : ∀ a ∈ P, 0 < a) (hq : ∀ b ∈ Q, 0 < b)
    (hpw : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (hqw : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (hcross : ∀ a ∈ P, ∀ b ∈ Q, a.Coprime b)
    (hlt : numer P * numer Q ≤ denom P * denom Q) :
    let d := denom P * denom Q - numer P * numer Q
    (d ∣ denom P * numer Q + (denom Q)^2) ↔
      (d ∣ numer P * denom Q + (denom P)^2) := by
  have hMN : (denom P).Coprime (denom Q) :=
    Nat.coprime_prod_left_iff.mpr fun a ha => Nat.coprime_prod_right_iff.mpr (hcross a ha)
  exact frame_divisibility_iff hlt hMN
    (reduced_cofactor_sum P hp hpw).symm (reduced_cofactor_sum Q hq hqw).symm

end Erdos307Structure
