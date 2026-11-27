import Erdos307FrameGCD
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic

namespace Erdos307Structure
open Finset
open scoped BigOperators

private theorem odd_cofactor_of_odd_product {X : Finset ℕ} {x : ℕ} (hx : x ∈ X)
    (hodd : Odd (denom X)) : Odd (denom X / x) := by
  have hdvd : x ∣ denom X := by
    refine ⟨denom (X.erase x), ?_⟩
    simpa [denom, mul_comm] using (Finset.prod_erase_mul X id hx).symm
  have heq : denom X / x * x = denom X := Nat.div_mul_cancel hdvd
  rw [← heq] at hodd
  exact (Nat.odd_mul.mp hodd).1

/-- An odd product forces its cofactor sum to have the parity of the group size,
even for composite denominators. -/
theorem numer_mod_two_of_odd_denom {X : Finset ℕ} (hodd : Odd (denom X)) :
    numer X % 2 = X.card % 2 := by
  have hone (x : ℕ) (hx : x ∈ X) : (denom X / x) % 2 = 1 :=
    Nat.odd_iff.mp (odd_cofactor_of_odd_product hx hodd)
  calc
    _ = (∑ x ∈ X, (denom X / x) % 2) % 2 := by rw [numer, Finset.sum_nat_mod]
    _ = (∑ _x ∈ X, (1 : ℕ)) % 2 := by rw [Finset.sum_congr rfl hone]
    _ = _ := by simp

/-- Mutually coprime grouped slots of even cardinality cannot have a
common odd cofactor, regardless of the primality of individual factors. -/
theorem even_of_common_numer_of_even_cards {X Y : Finset ℕ} {t : ℕ}
    (hXY : (denom X).Coprime (denom Y)) (hX : Even X.card) (hY : Even Y.card)
    (htX : numer X = t) (htY : numer Y = t) : Even t := by
  by_contra ht
  have hodd := Nat.not_even_iff_odd.mp ht
  have hdx : Even (denom X) := by
    by_contra h
    have he := numer_mod_two_of_odd_denom (Nat.not_even_iff_odd.mp h)
    rw [htX, Nat.odd_iff.mp hodd, Nat.even_iff.mp hX] at he
    omega
  have hdy : Even (denom Y) := by
    by_contra h
    have he := numer_mod_two_of_odd_denom (Nat.not_even_iff_odd.mp h)
    rw [htY, Nat.odd_iff.mp hodd, Nat.even_iff.mp hY] at he
    omega
  have ht2 : 2 ∣ Nat.gcd (denom X) (denom Y) := Nat.dvd_gcd hdx.two_dvd hdy.two_dvd
  rw [hXY] at ht2
  norm_num at ht2

/-- In particular, the two-by-two equal-cofactor completion has even reduced
denominator. -/
theorem frame_grouped_even_denominator {M U N V : ℕ} {X Y : Finset ℕ}
    (hlt : U * V < M * N) (hMN : M.Coprime N) (hMU : M.Coprime U) (hNV : N.Coprime V)
    (hX : Even X.card) (hY : Even Y.card) :
    let d := M * N - U * V
    let A := M * V + N ^ 2
    let B := U * N + M ^ 2
    let g := A.gcd B
    let t := d / g
    denom X = A / g → denom Y = B / g → numer X = t → numer Y = t → Even t := by
  intro d A B g t hp hq htX htY
  have hc := (frame_primitive_balance hlt hMN hMU hNV).2.1
  apply even_of_common_numer_of_even_cards _ hX hY htX htY
  rw [hp, hq]
  exact hc

private theorem odd_of_coprime_even {x t : ℕ} (hc : x.Coprime t) (ht : Even t) : Odd x := by
  apply Nat.not_even_iff_odd.mp
  intro hx
  have hd : 2 ∣ x.gcd t := Nat.dvd_gcd hx.two_dvd ht.two_dvd
  rw [hc] at hd
  norm_num at hd

/-- An even reduced completion denominator forces the product of each base
to have the parity of the opposite cofactor sum. -/
theorem frame_base_parity_of_even_reduced_denominator {M U N V : ℕ}
    (hlt : U * V < M * N) (hMN : M.Coprime N) (hMU : M.Coprime U) (hNV : N.Coprime V) :
    let d := M * N - U * V
    let A := M * V + N ^ 2
    let B := U * N + M ^ 2
    let g := A.gcd B
    Even (d / g) → N ≡ U [MOD 2] ∧ M ≡ V [MOD 2] := by
  intro d A B g ht
  change Even ((M * N - U * V) / (M * V + N ^ 2).gcd (U * N + M ^ 2)) at ht
  have hbal := frame_primitive_balance hlt hMN hMU hNV
  have hred := frame_reduced_slot_denominator hlt hMN hMU hNV
  have hp := (odd_of_coprime_even hred.1 ht).natCast_zmod_two
  have hq := (odd_of_coprime_even hred.2.1 ht).natCast_zmod_two
  constructor
  · apply (ZMod.natCast_eq_natCast_iff N U 2).mp
    have hh := congrArg (fun k : ℕ => (k : ZMod 2)) hbal.2.2.1
    simpa only [Nat.cast_mul, Nat.cast_add, hp, hq, ht.natCast_zmod_two,
      mul_one, mul_zero, add_zero] using hh
  · apply (ZMod.natCast_eq_natCast_iff M V 2).mp
    have hh := congrArg (fun k : ℕ => (k : ZMod 2)) hbal.2.2.2
    simpa only [Nat.cast_mul, Nat.cast_add, hp, hq, ht.natCast_zmod_two,
      mul_one, mul_zero, add_zero] using hh

/-- A left grouped slot of at least two members requires the shared gcd to
be strictly below one quarter of the square of the left base product. -/
theorem frame_gcd_lt_quarter_of_grouped_left {M U N V : ℕ} {X : Finset ℕ}
    (hUV : 0 < U * V) (hlt : U * V < M * N)
    (hMN : M.Coprime N) (hMU : M.Coprime U) (hNV : N.Coprime V)
    (hp : ∀ x ∈ X, 0 < x) (hc : Set.Pairwise (X : Set ℕ) Nat.Coprime) (hx : 2 ≤ X.card) :
    let d := M * N - U * V
    let A := M * V + N ^ 2
    let B := U * N + M ^ 2
    let g := A.gcd B
    denom X = A / g → numer X = d / g → 4 * g < M ^ 2 := by
  intro d A B g hXd hXn
  have hgD : g ∣ d := by
    have hi := (frame_gcd_identity hlt.le hMN hMU hNV).1
    change g = A.gcd d at hi
    rw [hi]
    exact Nat.gcd_dvd_right _ _
  have hA : denom X * g = A := by
    rw [hXd]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left A B)
  have hd : numer X * g = d := by
    rw [hXn]
    exact Nat.div_mul_cancel hgD
  have hbound : 4 * A * g ≤ d ^ 2 := calc
    _ = (4 * denom X) * (g * g) := by rw [← hA]; ring
    _ ≤ numer X ^ 2 * (g * g) := Nat.mul_le_mul_right _ (four_denom_le_numer_sq hp hc hx)
    _ = d ^ 2 := by rw [← hd]; ring
  have hN : 0 < N := by
    by_contra! hn
    have hz : N = 0 := by omega
    rw [hz, mul_zero] at hlt
    omega
  have hlt2 : d ^ 2 < (M * N) ^ 2 :=
    Nat.pow_lt_pow_left (Nat.sub_lt (Nat.zero_lt_of_lt hlt) hUV) (by decide)
  have hN2 : 0 < N ^ 2 := pow_pos hN _
  by_contra! hMg
  have hbad : (M * N) ^ 2 ≤ 4 * A * g := calc
    _ = M ^ 2 * N ^ 2 := by ring
    _ ≤ (4 * g) * N ^ 2 := Nat.mul_le_mul_right _ hMg
    _ ≤ (4 * g) * A := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    _ = _ := by ring
  exact (not_lt_of_ge (hbad.trans hbound)) hlt2

#print axioms frame_grouped_even_denominator
#print axioms frame_base_parity_of_even_reduced_denominator
#print axioms frame_gcd_lt_quarter_of_grouped_left
end Erdos307Structure
