import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos307Structure

/-- The two support-square equations for a single new prime imply a
quadratic conic and an exact product of their sum and difference. -/
theorem single_tail_conic {D N q X Y : ℤ}
    (hx : X^2 = (N + 2*D)*q + D) (hy : Y^2 = (N - 2*D)*q + D) :
    (N + 2*D)*Y^2 - (N - 2*D)*X^2 = 4*D^2 ∧
      (X+Y)*(X-Y) = 4*D*q := by
  constructor
  · linear_combination (N+2*D)*hy - (N-2*D)*hx
  · linear_combination hx - hy

/-- If the side containing the new prime has product q*a, and the other
side has product b, then q divides the difference between a and b. -/
theorem prime_tail_mod_complement {D N q a b : ℕ}
    (hq : q.Prime) (hqD : ¬q ∣ D) (hD : a*b = D)
    (hs : (q*a)^2 + b^2 = N*q + D) : a ≡ b [MOD q] := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hzero : (q : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff q q).mpr (dvd_refl q)
  have hb0 : (b : ZMod q) ≠ 0 := by
    intro he
    have hb := (ZMod.natCast_eq_zero_iff b q).mp he
    exact hqD (hD ▸ dvd_mul_of_dvd_right hb a)
  have hc := congrArg (fun t : ℕ => (t : ZMod q)) hs
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, hzero, zero_mul, mul_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at hc
  have hab := congrArg (fun t : ℕ => (t : ZMod q)) hD
  rw [Nat.cast_mul] at hab
  rw [← hab, pow_two] at hc
  exact (ZMod.natCast_eq_natCast_iff a b q).mp (mul_right_cancel₀ hb0 hc).symm

/-- Distinct positive complementary factors give a sharper tail bound than
the bound by the cofactor sum alone. -/
theorem prime_tail_lt_fixed_product {D N q a b : ℕ}
    (hq : q.Prime) (hqD : ¬q ∣ D) (hD : a*b = D)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hs : (q*a)^2 + b^2 = N*q + D) : q < D := by
  have he := prime_tail_mod_complement hq hqD hD hs
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hdiv := (Nat.modEq_iff_dvd' hlt.le).mp he
    have hqle := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdiv
    have hbD : b ≤ D := hD ▸ Nat.le_mul_of_pos_left b ha
    omega
  · have hdiv := (Nat.modEq_iff_dvd' hgt.le).mp he.symm
    have hqle := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdiv
    have haD : a ≤ D := hD ▸ Nat.le_mul_of_pos_right a hb
    omega

private theorem square_parity (x : ℕ) : x^2 % 2 = x % 2 := by
  rw [pow_two, Nat.mul_mod x x 2]
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h <;> simp [h]

/-- The two global squares produce positive complementary divisors of the
old support, with the prime tail absorbed by one of the two products. -/
theorem prime_tail_factors_from_squares {D N q x y : ℕ}
    (hD : 0 < D) (hN : 2*D ≤ N) (hq : q.Prime)
    (hx : x^2 = (N + 2*D)*q + D) (hy : y^2 = (N - 2*D)*q + D) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a*b = D ∧
      (q*a)^2 + b^2 = N*q + D := by
  have hN' : N - 2*D + 2*D = N := Nat.sub_add_cancel hN
  have hNq := congrArg (· * q) hN'
  have hxy : x^2 = y^2 + 4*D*q := by nlinarith
  have hpos : 0 < 4*D*q := by have := hq.pos; positivity
  have hlt : y < x := by
    by_contra! hn
    have hle := Nat.pow_le_pow_left hn 2
    omega
  have heven : (4*D*q) % 2 = 0 := by
    rw [show 4*D*q = 2*(2*D*q) by ring]
    omega
  have hpar := congrArg (· % 2) hxy
  rw [square_parity x, Nat.add_mod, square_parity y, heven, add_zero, Nat.mod_mod] at hpar
  let u := (x+y)/2
  let v := (x-y)/2
  have hu : 2*u = x+y := by dsimp [u]; omega
  have hv : 2*v+y = x := by dsimp [v]; omega
  have hXu : x = u+v := by omega
  have hYu : u = y+v := by omega
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  have hdiff : x^2 = y^2 + 4*(u*v) := by rw [hXu,hYu]; ring
  have hsum : x^2+y^2 = 2*(u^2+v^2) := by rw [hXu,hYu]; ring
  have huv : u*v = D*q := by nlinarith
  have hsq : u^2+v^2 = N*q + D := by nlinarith
  have hdvd : q ∣ u*v := huv.symm ▸ dvd_mul_left q D
  rcases hq.dvd_mul.mp hdvd with hu' | hv'
  · obtain ⟨a,ha⟩ := hu'
    have ha0 : 0 < a := by
      by_contra! hn
      rw [Nat.eq_zero_of_le_zero hn, mul_zero] at ha
      omega
    refine ⟨a,v,ha0,hv0,?_,?_⟩
    · apply Nat.eq_of_mul_eq_mul_left hq.pos
      calc
        _ = u*v := by rw [ha]; ring
        _ = _ := by rw [huv, mul_comm]
    · rwa [← ha]
  · obtain ⟨a,ha⟩ := hv'
    have ha0 : 0 < a := by
      by_contra! hn
      rw [Nat.eq_zero_of_le_zero hn, mul_zero] at ha
      omega
    refine ⟨a,u,ha0,hu0,?_,?_⟩
    · apply Nat.eq_of_mul_eq_mul_left hq.pos
      calc
        _ = u*v := by rw [ha]; ring
        _ = _ := by rw [huv, mul_comm]
    · rwa [← ha, add_comm]

/-- For a positive nonsquare fixed product, any prime tail satisfying both
global squares is strictly below that product. -/
theorem prime_tail_lt_fixed_product_of_two_squares {D N q x y : ℕ}
    (hD : 0 < D) (hN : 2*D ≤ N) (hq : q.Prime) (hqD : ¬q ∣ D)
    (hnot : ¬ IsSquare D)
    (hx : x^2 = (N + 2*D)*q + D) (hy : y^2 = (N - 2*D)*q + D) : q < D := by
  obtain ⟨a,b,ha,hb,he,hs⟩ := prime_tail_factors_from_squares hD hN hq hx hy
  refine prime_tail_lt_fixed_product hq hqD he ha hb ?_ hs
  rintro rfl
  exact hnot ⟨a,he.symm⟩

#print axioms single_tail_conic
#print axioms prime_tail_mod_complement
#print axioms prime_tail_lt_fixed_product
#print axioms prime_tail_factors_from_squares
#print axioms prime_tail_lt_fixed_product_of_two_squares

end Erdos307Structure
