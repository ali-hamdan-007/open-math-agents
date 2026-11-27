import Erdos307FrameOneTest
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos307Structure

private theorem balance_gcd {A B d M U N : ℕ}
    (hbal : N * B = U * A + M * d) (hAM : A.Coprime M) (hAN : A.Coprime N) :
    A.gcd B = A.gcd d := by
  apply Nat.dvd_antisymm
  · let g := A.gcd B
    have hgA : g ∣ A := Nat.gcd_dvd_left _ _
    have hgB : g ∣ B := Nat.gcd_dvd_right _ _
    have hgSum : g ∣ U * A + M * d := hbal ▸ dvd_mul_of_dvd_right hgB N
    have hgMd : g ∣ M * d := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hgA U)).mpr hgSum
    exact Nat.dvd_gcd hgA ((hAM.coprime_dvd_left hgA).dvd_of_dvd_mul_left hgMd)
  · let g := A.gcd d
    have hgA : g ∣ A := Nat.gcd_dvd_left _ _
    have hgd : g ∣ d := Nat.gcd_dvd_right _ _
    have hgNB : g ∣ N * B := hbal.symm ▸
      dvd_add (dvd_mul_of_dvd_right hgA U) (dvd_mul_of_dvd_right hgd M)
    exact Nat.dvd_gcd hgA ((hAN.coprime_dvd_left hgA).dvd_of_dvd_mul_left hgNB)

private theorem frame_balance {M U N V : ℕ} (hlt : U * V ≤ M * N) :
    N * (U * N + M ^ 2) = U * (M * V + N ^ 2) + M * (M * N - U * V) := by
  let d := M * N - U * V
  have hd : d + U * V = M * N := Nat.sub_add_cancel hlt
  change N * (U * N + M ^ 2) = U * (M * V + N ^ 2) + M * d
  apply Nat.add_right_cancel (m := M * (U * V))
  calc
    _ = U * (M * V + N ^ 2) + M * (M * N) := by ring
    _ = _ := by rw [← hd]; ring

private theorem numerator_coprime {M N V : ℕ} (hMN : M.Coprime N) (hNV : N.Coprime V) :
    (M * V + N ^ 2).Coprime M ∧ (M * V + N ^ 2).Coprime N := by
  constructor
  · rw [Nat.coprime_mul_left_add_left]
    exact hMN.symm.pow_left 2
  · rw [pow_two, Nat.coprime_add_mul_left_left]
    exact hMN.mul_left hNV.symm

/-- Both unreduced completion numerators have identical gcd with the determinant.
The common gcd is also the gcd of the numerators with each other. -/
theorem frame_gcd_identity {M U N V : ℕ} (hlt : U * V ≤ M * N)
    (hMN : M.Coprime N) (hMU : M.Coprime U) (hNV : N.Coprime V) :
    let d := M * N - U * V
    let A := M * V + N ^ 2
    let B := U * N + M ^ 2
    A.gcd B = A.gcd d ∧ A.gcd B = B.gcd d := by
  let d := M * N - U * V
  let A := M * V + N ^ 2
  let B := U * N + M ^ 2
  have hA := numerator_coprime hMN hNV
  have hB : B.Coprime N ∧ B.Coprime M := by
    simpa only [mul_comm, B] using (numerator_coprime hMN.symm hMU)
  have hrevlt : V * U ≤ N * M := by simpa only [mul_comm] using hlt
  have hrev : M * A = V * B + N * d := by
    simpa only [mul_comm, A, B, d] using frame_balance hrevlt
  exact ⟨balance_gcd (frame_balance hlt) hA.1 hA.2,
    (Nat.gcd_comm A B).trans (balance_gcd hrev hB.1 hB.2)⟩

/-- The primitive pair after canceling the common gcd has normalized balancing
equations even when the original two completion quotients are fractional. -/
theorem frame_primitive_balance {M U N V : ℕ} (hlt : U * V < M * N)
    (hMN : M.Coprime N) (hMU : M.Coprime U) (hNV : N.Coprime V) :
    let d := M * N - U * V
    let A := M * V + N ^ 2
    let B := U * N + M ^ 2
    let g := A.gcd B
    let p := A / g
    let q := B / g
    let t := d / g
    0 < t ∧ p.Coprime q ∧ N * q = U * p + M * t ∧ M * p = V * q + N * t := by
  let d := M * N - U * V
  let A := M * V + N ^ 2
  let B := U * N + M ^ 2
  let g := A.gcd B
  let p := A / g
  let q := B / g
  let t := d / g
  change 0 < t ∧ p.Coprime q ∧ N * q = U * p + M * t ∧ M * p = V * q + N * t
  have hA : p * g = A := Nat.div_mul_cancel (Nat.gcd_dvd_left A B)
  have hB : q * g = B := Nat.div_mul_cancel (Nat.gcd_dvd_right A B)
  have hdvd : g ∣ d := by
    change A.gcd B ∣ d
    rw [(frame_gcd_identity hlt.le hMN hMU hNV).1]
    exact Nat.gcd_dvd_right _ _
  have hdt : t * g = d := Nat.div_mul_cancel hdvd
  have hd0 : 0 < d := Nat.sub_pos_of_lt hlt
  have ht : 0 < t := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, zero_mul] at hdt
    omega
  have hg : 0 < g := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hdt
    omega
  have hpc : p.Coprime q := by
    change p.gcd q = 1
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← Nat.gcd_mul_right, hA, hB, one_mul]
  have hrevlt : V * U ≤ N * M := by simpa only [mul_comm] using hlt.le
  have hrev : M * A = V * B + N * d := by
    simpa only [mul_comm, A, B, d] using frame_balance hrevlt
  refine ⟨ht, hpc, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_right hg
    simpa only [Nat.add_mul, mul_assoc, hB, hA, hdt] using frame_balance hlt.le
  · apply Nat.eq_of_mul_eq_mul_right hg
    simpa only [Nat.add_mul, mul_assoc, hB, hA, hdt] using hrev

/-- Canceling the gcd leaves the same reduced denominator t in both rational
completion values. Each numerator is also coprime to the product of both bases. -/
theorem frame_reduced_slot_denominator {M U N V : ℕ} (hlt : U * V < M * N)
    (hMN : M.Coprime N) (hMU : M.Coprime U) (hNV : N.Coprime V) :
    let d := M * N - U * V
    let A := M * V + N ^ 2
    let B := U * N + M ^ 2
    let g := A.gcd B
    let p := A / g
    let q := B / g
    let t := d / g
    p.Coprime t ∧ q.Coprime t ∧ p.Coprime (M * N) ∧ q.Coprime (M * N) := by
  intro d A B g p q t
  have hId := frame_gcd_identity hlt.le hMN hMU hNV
  change g = A.gcd d ∧ g = B.gcd d at hId
  have hdvd : g ∣ d := hId.1.symm ▸ Nat.gcd_dvd_right A d
  have hpt : p * g = A := Nat.div_mul_cancel (Nat.gcd_dvd_left A B)
  have hqt : q * g = B := Nat.div_mul_cancel (Nat.gcd_dvd_right A B)
  have htt : t * g = d := Nat.div_mul_cancel hdvd
  have hg : 0 < g := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at htt
    have hpos : 0 < d := Nat.sub_pos_of_lt hlt
    omega
  have hA := numerator_coprime hMN hNV
  have hB : B.Coprime N ∧ B.Coprime M := by
    simpa only [mul_comm, B] using numerator_coprime hMN.symm hMU
  refine ⟨?_, ?_, ?_, ?_⟩
  · change p.gcd t = 1
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← Nat.gcd_mul_right, hpt, htt, ← hId.1, one_mul]
  · change q.gcd t = 1
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← Nat.gcd_mul_right, hqt, htt, ← hId.2, one_mul]
  · exact (hA.1.mul_right hA.2).coprime_dvd_left ⟨g, hpt.symm⟩
  · exact (hB.2.mul_right hB.1).coprime_dvd_left ⟨g, hqt.symm⟩

open Finset
open scoped BigOperators

private theorem member_dvd_denom {X : Finset ℕ} {x : ℕ} (hx : x ∈ X) :
    x ∣ denom X := by
  refine ⟨denom (X.erase x), ?_⟩
  simpa [denom, mul_comm] using (Finset.prod_erase_mul X id hx).symm

private theorem denom_union_disjoint {P X : Finset ℕ} (h : Disjoint P X) :
    denom (P ∪ X) = denom P * denom X := Finset.prod_union h

private theorem numer_union_disjoint {P X : Finset ℕ} (h : Disjoint P X) :
    numer (P ∪ X) = numer P * denom X + denom P * numer X := by
  simp only [numer, Finset.sum_union h, denom_union_disjoint h, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm (denom P) (denom X), Nat.mul_div_assoc _ (member_dvd_denom hx), mul_comm]
  · exact Finset.sum_congr rfl
      (fun x hx => Nat.mul_div_assoc _ (member_dvd_denom hx))

/-- A rationally completed frame can be completed by finite denominator groups
if both primitive products admit denominator groups with common cofactor t. -/
theorem cross_products_of_grouped_frame {P Q X Y : Finset ℕ}
    (hlt : numer P * numer Q < denom P * denom Q)
    (hMN : (denom P).Coprime (denom Q)) (hMU : (denom P).Coprime (numer P))
    (hNV : (denom Q).Coprime (numer Q)) (hPX : Disjoint P X) (hQY : Disjoint Q Y) :
    let M := denom P
    let U := numer P
    let N := denom Q
    let V := numer Q
    let A := M * V + N ^ 2
    let B := U * N + M ^ 2
    let g := A.gcd B
    let t := (M * N - U * V) / g
    denom X = A / g → denom Y = B / g → numer X = t → numer Y = t →
    numer (P ∪ X) = denom (Q ∪ Y) ∧ numer (Q ∪ Y) = denom (P ∪ X) := by
  intro M U N V A B g t hX hY htX htY
  obtain ⟨_, _, hleft, hright⟩ := frame_primitive_balance hlt hMN hMU hNV
  rw [numer_union_disjoint hPX, numer_union_disjoint hQY,
    denom_union_disjoint hPX, denom_union_disjoint hQY, hX, hY, htX, htY]
  exact ⟨hleft.symm, hright.symm⟩

/-- A group with two or more positive pairwise coprime members has cofactor
sum at least twice the square root of its product, in integer form. -/
theorem four_denom_le_numer_sq {X : Finset ℕ} (hp : ∀ x ∈ X, 0 < x)
    (hc : Set.Pairwise (X : Set ℕ) Nat.Coprime) (hs : 2 ≤ X.card) :
    4 * denom X ≤ numer X ^ 2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hs
  have hdiv : x * y ∣ denom X :=
    (hc hx hy hxy).mul_dvd_of_dvd_of_dvd (member_dvd_denom hx) (member_dvd_denom hy)
  obtain ⟨k, hk⟩ := hdiv
  have hpos : 0 < denom X := Finset.prod_pos hp
  have hk1 : 1 ≤ k := by
    by_contra! hn
    have hz : k = 0 := by omega
    rw [hz, mul_zero] at hk
    omega
  have hxq : denom X / x = y * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ (hp x hx)]
  have hyq : denom X / y = x * k := by
    rw [hk, mul_comm x y, mul_assoc, Nat.mul_div_cancel_left _ (hp y hy)]
  have hsum : denom X / x + denom X / y ≤ numer X := by
    have hset : ({x,y} : Finset ℕ) ⊆ X := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hset
      (f := fun a => denom X / a) (by intros; exact Nat.zero_le _)
    simpa [numer, Finset.sum_insert, hxy] using hle
  have hmul : denom X ≤ (denom X / x) * (denom X / y) := by
    rw [hxq, hyq]
    calc
      denom X = x * y * k := hk
      _ = (x * y * k) * 1 := by rw [mul_one]
      _ ≤ (x * y * k) * k := Nat.mul_le_mul_left _ hk1
      _ = (y * k) * (x * k) := by ring
  have hsquares : 4 * ((denom X / x) * (denom X / y)) ≤
      (denom X / x + denom X / y) ^ 2 := by
    exact_mod_cast (show (4 : ℤ) * ((denom X / x : ℕ) * (denom X / y : ℕ)) ≤
      ((denom X / x : ℕ) + (denom X / y : ℕ) : ℤ) ^ 2 by
        nlinarith [sq_nonneg (((denom X / x : ℕ) : ℤ) - ((denom X / y : ℕ) : ℤ))])
  exact (Nat.mul_le_mul_left 4 hmul).trans (hsquares.trans (Nat.pow_le_pow_left hsum 2))

/-- For a frame with singleton left base {2}, a nonintegral primitive
completion cannot be repaired by a coprime group in the left slot. -/
theorem no_grouped_left_slot_of_two {N V : ℕ} {X : Finset ℕ}
    (hV : 0 < V) (hlt : V < 2 * N) (h2N : Nat.Coprime 2 N) (hNV : N.Coprime V)
    (hp : ∀ x ∈ X, 0 < x) (hc : Set.Pairwise (X : Set ℕ) Nat.Coprime) :
    let d := 2 * N - V
    let A := 2 * V + N ^ 2
    let B := N + 4
    let g := A.gcd B
    1 < d / g → denom X = A / g → numer X = d / g → False := by
  intro d A B g ht hDX htX
  have hs : 2 ≤ X.card := by
    by_contra hsmall
    rcases (show X.card = 0 ∨ X.card = 1 by omega) with hz | hone
    · rw [Finset.card_eq_zero.mp hz, numer, Finset.sum_empty] at htX
      omega
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hone
      have hx := hp x (by simp)
      have hnum : numer ({x} : Finset ℕ) = 1 := by simp [numer, denom, Nat.div_self hx]
      omega
  have hgd : g ∣ d := by
    have heq := (frame_gcd_identity (M := 2) (U := 1) (N := N) (V := V)
      (by simpa using hlt.le) h2N (by simp) hNV).1
    change A.gcd B ∣ d
    rw [show A.gcd B = A.gcd d by simpa [A, B, d] using heq]
    exact Nat.gcd_dvd_right _ _
  have hXg : denom X * g = A := by
    rw [hDX]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left A B)
  have htg : numer X * g = d := by
    rw [htX]
    exact Nat.div_mul_cancel hgd
  have hg1 : 1 ≤ g := by
    by_contra! hz
    have hg0 : g = 0 := by omega
    rw [hg0, mul_zero] at htg
    have hdpos : 0 < d := Nat.sub_pos_of_lt hlt
    omega
  have h4 : 4 * A * g ≤ d ^ 2 := calc
    _ = (4 * denom X) * (g * g) := by rw [← hXg]; ring
    _ ≤ numer X ^ 2 * (g * g) := Nat.mul_le_mul_right _ (four_denom_le_numer_sq hp hc hs)
    _ = d ^ 2 := by rw [← htg]; ring
  have hupper : d ^ 2 < (2 * N) ^ 2 := by
    apply Nat.pow_lt_pow_left
    · exact Nat.sub_lt (by omega) hV
    · decide
  have hlower : (2 * N) ^ 2 ≤ 4 * A * g := calc
    _ = 4 * N ^ 2 := by ring
    _ ≤ 4 * A := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    _ = (4 * A) * 1 := by rw [mul_one]
    _ ≤ 4 * A * g := Nat.mul_le_mul_left _ hg1
  exact (not_lt_of_ge (hlower.trans h4)) hupper

#print axioms frame_gcd_identity
#print axioms frame_primitive_balance
#print axioms frame_reduced_slot_denominator
#print axioms cross_products_of_grouped_frame
#print axioms four_denom_le_numer_sq
#print axioms no_grouped_left_slot_of_two
end Erdos307Structure
