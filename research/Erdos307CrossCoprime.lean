import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

open Finset
open scoped BigOperators

namespace Erdos307Structure

/-- Product of the denominators. -/
def denom (A : Finset ℕ) : ℕ := ∏ a ∈ A, a

/-- Numerator of the reciprocal sum over the common denominator. -/
def numer (A : Finset ℕ) : ℕ := ∑ a ∈ A, denom A / a

private lemma denom_erase_mul {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    denom (A.erase a) * a = denom A :=
  Finset.prod_erase_mul A id ha

private lemma dvd_denom {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∣ denom A :=
  ⟨denom (A.erase a), (mul_comm _ _).trans (denom_erase_mul ha) |>.symm⟩

theorem reduced_cofactor_sum (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hpair : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    (numer A).Coprime (denom A) := by
  apply Nat.coprime_prod_right_iff.2
  intro a ha
  have herase : (denom (A.erase a)).Coprime a := by
    apply Nat.coprime_prod_left_iff.2
    intro b hb
    exact hpair (Finset.mem_of_mem_erase hb) ha (Finset.ne_of_mem_erase hb)
  have hdiv : ∀ b ∈ A.erase a, a ∣ denom A / b := by
    intro b hb
    have hbA := Finset.mem_of_mem_erase hb
    have hab := (Finset.ne_of_mem_erase hb).symm
    have hba : a ∈ A.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
    have hquot : denom A / b = denom (A.erase b) := by
      rw [← denom_erase_mul hbA, Nat.mul_div_cancel _ (hpos b hbA)]
    rw [hquot]
    exact dvd_denom hba
  obtain ⟨k, hk⟩ := Finset.dvd_sum hdiv
  change (∑ b ∈ A, denom A / b).Coprime a
  rw [← Finset.sum_erase_add _ _ ha, hk, ← denom_erase_mul ha,
    Nat.mul_div_cancel _ (hpos a ha), Nat.coprime_mul_left_add_left]
  exact herase

private lemma clear_denoms (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) :
    (denom A : ℚ) * (∑ a ∈ A, (a : ℚ)⁻¹) = (numer A : ℚ) := by
  rw [Finset.mul_sum, numer, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hane : (a : ℚ) ≠ 0 := by exact_mod_cast (hpos a ha).ne'
  rw [← div_eq_mul_inv]
  apply (div_eq_iff hane).2
  exact_mod_cast (Nat.div_mul_cancel (dvd_denom ha)).symm

/-- Any solution on positive pairwise coprime denominators exchanges numerators and
denominators. In particular, coprimality across the two sets follows automatically. -/
theorem swap_products (P Q : Finset ℕ)
    (hp : ∀ a ∈ P, 0 < a) (hq : ∀ b ∈ Q, 0 < b)
    (hpw : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (hqw : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (heq : 1 = (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹)) :
    numer P = denom Q ∧ numer Q = denom P ∧
      ∀ a ∈ P, ∀ b ∈ Q, a.Coprime b := by
  have hcP := reduced_cofactor_sum P hp hpw
  have hcQ := reduced_cofactor_sum Q hq hqw
  have hmul : numer P * numer Q = denom P * denom Q := by
    exact_mod_cast (show (numer P : ℚ) * (numer Q : ℚ) = (denom P : ℚ) * (denom Q : ℚ) by
      rw [← clear_denoms P hp, ← clear_denoms Q hq, mul_mul_mul_comm, ← heq, mul_one])
  have left_eq : numer P = denom Q := by
    apply Nat.dvd_antisymm
    · exact hcP.dvd_of_dvd_mul_left (hmul ▸ dvd_mul_right (numer P) (numer Q))
    · exact hcQ.symm.dvd_of_dvd_mul_right (hmul.symm ▸ dvd_mul_left (denom Q) (denom P))
  have right_eq : numer Q = denom P := by
    apply Nat.dvd_antisymm
    · exact hcQ.dvd_of_dvd_mul_right (hmul ▸ dvd_mul_left (numer Q) (numer P))
    · exact hcP.symm.dvd_of_dvd_mul_left (hmul.symm ▸ dvd_mul_right (denom P) (denom Q))
  refine ⟨left_eq, right_eq, ?_⟩
  intro a ha b hb
  rw [right_eq] at hcQ
  exact (hcQ.coprime_dvd_left (dvd_denom ha)).coprime_dvd_right (dvd_denom hb)

private lemma numer_insert {A : Finset ℕ} {a : ℕ} (ha : a ∉ A)
    (ha_pos : 0 < a) : numer (insert a A) = a * numer A + denom A := by
  have hd : denom (insert a A) = a * denom A := Finset.prod_insert ha
  rw [numer, Finset.sum_insert ha, hd, Nat.mul_div_cancel_left _ ha_pos, numer,
    Finset.mul_sum, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun b hb => Nat.mul_div_assoc a (dvd_denom hb)

private lemma positive_denom {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) :
    0 < denom A := Finset.prod_pos hpos

private lemma frame_from_cross {M M' N N' p q : ℕ}
    (hN : 0 < N) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hcrossP : p * M' + M = N * q) (hcrossQ : q * N' + N = M * p) :
    M' * N' < M * N ∧
      2 * (M * N - M' * N') ≤ M * N' + N ^ 2 ∧
      2 * (M * N - M' * N') ≤ M' * N + M ^ 2 ∧
      (M * N - M' * N') ∣ (M * N' + N ^ 2) ∧
      (M * N - M' * N') ∣ (M' * N + M ^ 2) := by
  have hPz : (p : ℤ) * M' + M = (N : ℤ) * q := by exact_mod_cast hcrossP
  have hQz : (q : ℤ) * N' + N = (M : ℤ) * p := by exact_mod_cast hcrossQ
  have hpz : ((M : ℤ) * N - (M' : ℤ) * N') * p = (M : ℤ) * N' + (N : ℤ)^2 := by
    linear_combination -(N' : ℤ) * hPz - (N : ℤ) * hQz
  have hqz : ((M : ℤ) * N - (M' : ℤ) * N') * q = (M' : ℤ) * N + (M : ℤ)^2 := by
    linear_combination -(M : ℤ) * hPz - (M' : ℤ) * hQz
  have hpos : 0 < (M : ℤ) * N' + (N : ℤ)^2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      (pow_pos (by exact_mod_cast hN) _)
  have hltZ : 0 < (M : ℤ) * N - (M' : ℤ) * N' := by
    by_contra! h
    have hc := mul_nonpos_of_nonpos_of_nonneg h (Int.natCast_nonneg p)
    rw [hpz] at hc
    omega
  have hlt : M' * N' < M * N := by
    exact_mod_cast (sub_pos.mp hltZ)
  let Δ := M * N - M' * N'
  have hΔ : (Δ : ℤ) = (M : ℤ) * N - (M' : ℤ) * N' := by
    dsimp [Δ]
    rw [Nat.cast_sub hlt.le]
    simp
  have heqP : Δ * p = M * N' + N ^ 2 := by
    rw [← hΔ] at hpz
    exact_mod_cast hpz
  have heqQ : Δ * q = M' * N + M ^ 2 := by
    rw [← hΔ] at hqz
    exact_mod_cast hqz
  refine ⟨hlt, ?_, ?_, ⟨p, heqP.symm⟩, ⟨q, heqQ.symm⟩⟩
  · rw [← heqP, Nat.mul_comm Δ p]
    exact Nat.mul_le_mul_right Δ hp
  · rw [← heqQ, Nat.mul_comm Δ q]
    exact Nat.mul_le_mul_right Δ hq

/-- The statement of the original pinned FormalConjectures variant. -/
def Original : Prop :=
  ∃ P Q : Finset ℕ, 0 ∉ P ∩ Q ∧ 1 ∉ P ∪ Q ∧
    1 < #P ∧ 1 < #Q ∧ Set.Pairwise P Nat.Coprime ∧ Set.Pairwise Q Nat.Coprime ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)

/-- The Diophantine frame existence statement. -/
def FrameExists : Prop :=
  ∃ P₀ Q₀ : Finset ℕ,
    P₀.Nonempty ∧ Q₀.Nonempty ∧
    (∀ a ∈ P₀, 2 ≤ a) ∧ (∀ b ∈ Q₀, 2 ≤ b) ∧
    Set.Pairwise (P₀ : Set ℕ) Nat.Coprime ∧
    Set.Pairwise (Q₀ : Set ℕ) Nat.Coprime ∧
    (∀ a ∈ P₀, ∀ b ∈ Q₀, Nat.Coprime a b) ∧
    let M := ∏ a ∈ P₀, a
    let M' := ∑ a ∈ P₀, M / a
    let N := ∏ b ∈ Q₀, b
    let N' := ∑ b ∈ Q₀, N / b
    M' * N' < M * N ∧
    2 * (M * N - M' * N') ≤ M * N' + N ^ 2 ∧
    2 * (M * N - M' * N') ≤ M' * N + M ^ 2 ∧
    (M * N - M' * N') ∣ (M * N' + N ^ 2) ∧
    (M * N - M' * N') ∣ (M' * N + M ^ 2)

private lemma two_le_of_mem {A : Finset ℕ} (hcard : 1 < #A) (h1 : 1 ∉ A)
    (hpair : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    ∀ a ∈ A, 2 ≤ a := by
  intro a ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hne : (A.erase 0).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem ha]
      omega
    obtain ⟨b, hb⟩ := hne
    have hb1 : b = 1 := by
      have h := hpair ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
      simpa [Nat.Coprime] using h
    exact h1 (hb1 ▸ Finset.mem_of_mem_erase hb)
  have ha1 : a ≠ 1 := fun h => h1 (h ▸ ha)
  omega

/-- Every solution of the original conjecture yields a Diophantine frame by
erasing a denominator from each side. -/
theorem reverse_frame (h : Original) : FrameExists := by
  obtain ⟨P, Q, _, h1, hcardP, hcardQ, hpairP, hpairQ, heq⟩ := h
  have hp2 : ∀ a ∈ P, 2 ≤ a :=
    two_le_of_mem hcardP (fun hp => h1 (Finset.mem_union_left _ hp)) hpairP
  have hq2 : ∀ b ∈ Q, 2 ≤ b :=
    two_le_of_mem hcardQ (fun hq => h1 (Finset.mem_union_right _ hq)) hpairQ
  obtain ⟨hPQ, hQP, hcop⟩ := swap_products P Q
    (fun a ha => by have := hp2 a ha; omega) (fun b hb => by have := hq2 b hb; omega)
    hpairP hpairQ heq
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < #P by omega)
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < #Q by omega)
  let P₀ := P.erase p
  let Q₀ := Q.erase q
  have hpnot : p ∉ P₀ := Finset.notMem_erase _ _
  have hqnot : q ∉ Q₀ := Finset.notMem_erase _ _
  have hPinsert : insert p P₀ = P := Finset.insert_erase hp
  have hQinsert : insert q Q₀ = Q := Finset.insert_erase hq
  have hP₀ : P₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [show P₀ = P.erase p from rfl, Finset.card_erase_of_mem hp]
    omega
  have hQ₀ : Q₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [show Q₀ = Q.erase q from rfl, Finset.card_erase_of_mem hq]
    omega
  have hposP := hp2 p hp
  have hposQ := hq2 q hq
  have hnP := numer_insert hpnot (by omega)
  have hnQ := numer_insert hqnot (by omega)
  rw [hPinsert] at hnP
  rw [hQinsert] at hnQ
  have hcrossP : p * numer P₀ + denom P₀ = denom Q₀ * q :=
    hnP.symm.trans (hPQ.trans (denom_erase_mul hq).symm)
  have hcrossQ : q * numer Q₀ + denom Q₀ = denom P₀ * p :=
    hnQ.symm.trans (hQP.trans (denom_erase_mul hp).symm)
  refine ⟨P₀, Q₀, hP₀, hQ₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a ha => hp2 a (Finset.mem_of_mem_erase ha)
  · exact fun b hb => hq2 b (Finset.mem_of_mem_erase hb)
  · exact hpairP.mono fun _ ha => Finset.mem_of_mem_erase ha
  · exact hpairQ.mono fun _ hb => Finset.mem_of_mem_erase hb
  · exact fun a ha b hb => hcop a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · apply frame_from_cross (p := p) (q := q) (positive_denom ?_) hposP hposQ hcrossP hcrossQ
    intro b hb
    have := hq2 b (Finset.mem_of_mem_erase hb)
    omega

-- Linear algebra from the frame reduction by @nijv is used below.
private lemma frame_cross_eq {M M' N N' Δ p q : ℕ}
    (hlt : M' * N' < M * N)
    (hΔ : Δ = M * N - M' * N')
    (hp : Δ * p = M * N' + N ^ 2)
    (hq : Δ * q = M' * N + M ^ 2) :
    (p * M' + M) = N * q ∧ (q * N' + N) = M * p := by
  have hΔpos : (0 : ℤ) < (Δ : ℤ) := by omega
  have hΔz : (Δ : ℤ) = (M : ℤ) * (N : ℤ) - (M' : ℤ) * (N' : ℤ) := by omega
  have hpz : (Δ : ℤ) * (p : ℤ) = (M : ℤ) * (N' : ℤ) + (N : ℤ) ^ 2 := by exact_mod_cast hp
  have hqz : (Δ : ℤ) * (q : ℤ) = (M' : ℤ) * (N : ℤ) + (M : ℤ) ^ 2 := by exact_mod_cast hq
  have h1z : (Δ : ℤ) * ((p : ℤ) * (M' : ℤ) + (M : ℤ)) = (Δ : ℤ) * ((N : ℤ) * (q : ℤ)) := by
    calc
      (Δ : ℤ) * ((p : ℤ) * (M' : ℤ) + (M : ℤ))
          = ((Δ : ℤ) * (p : ℤ)) * (M' : ℤ) + (Δ : ℤ) * (M : ℤ) := by ring
      _ = ((M : ℤ) * (N' : ℤ) + (N : ℤ) ^ 2) * (M' : ℤ) +
            ((M : ℤ) * (N : ℤ) - (M' : ℤ) * (N' : ℤ)) * (M : ℤ) := by rw [hpz, hΔz]
      _ = (N : ℤ) * ((M' : ℤ) * (N : ℤ) + (M : ℤ) ^ 2) := by ring
      _ = (N : ℤ) * ((Δ : ℤ) * (q : ℤ)) := by rw [← hqz]
      _ = (Δ : ℤ) * ((N : ℤ) * (q : ℤ)) := by ring
  have h2z : (Δ : ℤ) * ((q : ℤ) * (N' : ℤ) + (N : ℤ)) = (Δ : ℤ) * ((M : ℤ) * (p : ℤ)) := by
    calc
      (Δ : ℤ) * ((q : ℤ) * (N' : ℤ) + (N : ℤ))
          = ((Δ : ℤ) * (q : ℤ)) * (N' : ℤ) + (Δ : ℤ) * (N : ℤ) := by ring
      _ = ((M' : ℤ) * (N : ℤ) + (M : ℤ) ^ 2) * (N' : ℤ) +
            ((M : ℤ) * (N : ℤ) - (M' : ℤ) * (N' : ℤ)) * (N : ℤ) := by rw [hqz, hΔz]
      _ = (M : ℤ) * ((M : ℤ) * (N' : ℤ) + (N : ℤ) ^ 2) := by ring
      _ = (M : ℤ) * ((Δ : ℤ) * (p : ℤ)) := by rw [← hpz]
      _ = (Δ : ℤ) * ((M : ℤ) * (p : ℤ)) := by ring
  have hc1 : (p : ℤ) * (M' : ℤ) + (M : ℤ) = (N : ℤ) * (q : ℤ) :=
    mul_left_cancel₀ hΔpos.ne' h1z
  have hc2 : (q : ℤ) * (N' : ℤ) + (N : ℤ) = (M : ℤ) * (p : ℤ) :=
    mul_left_cancel₀ hΔpos.ne' h2z
  exact ⟨by exact_mod_cast hc1, by exact_mod_cast hc2⟩

private lemma frame_coprime {a M M' N N' p q : ℕ}
    (haM : a ∣ M) (haN : a.Coprime N)
    (hp : p * M' + M = N * q) (hq : q * N' + N = M * p) :
    p.Coprime a := by
  change p.gcd a = 1
  let d := p.gcd a
  have hdp : d ∣ p := Nat.gcd_dvd_left p a
  have hda : d ∣ a := Nat.gcd_dvd_right p a
  have hdM : d ∣ M := hda.trans haM
  have hdNcop : d.Coprime N := haN.coprime_dvd_left hda
  have hdq : d ∣ q := hdNcop.dvd_of_dvd_mul_left <| hp ▸
    dvd_add (dvd_mul_of_dvd_left hdp _) hdM
  have hdN : d ∣ N := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left hdq N')).mpr
    (hq.symm ▸ dvd_mul_of_dvd_right hdp M)
  exact Nat.dvd_one.mp (hdNcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl d) hdN)

private lemma extend_coprime {A : Finset ℕ} {a : ℕ} (ha : 2 ≤ a)
    (hpw : Set.Pairwise (A : Set ℕ) Nat.Coprime) (hcop : ∀ b ∈ A, a.Coprime b) :
    a ∉ A ∧ Set.Pairwise ((insert a A : Finset ℕ) : Set ℕ) Nat.Coprime := by
  refine ⟨?_, ?_⟩
  · intro h
    have hself := (hcop a h).gcd_eq_one
    rw [Nat.gcd_self] at hself
    omega
  · rw [Finset.coe_insert]
    exact hpw.insert fun b hb _ => ⟨hcop b hb, (hcop b hb).symm⟩

private lemma reciprocal_mul_of_swap {P Q : Finset ℕ}
    (hp : ∀ a ∈ P, 0 < a) (hq : ∀ b ∈ Q, 0 < b)
    (hPQ : numer P = denom Q) (hQP : numer Q = denom P) :
    1 = (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹) := by
  have hP : (denom P : ℚ) ≠ 0 := by exact_mod_cast (positive_denom hp).ne'
  have hQ : (denom Q : ℚ) ≠ 0 := by exact_mod_cast (positive_denom hq).ne'
  apply mul_left_cancel₀ (mul_ne_zero hP hQ)
  calc
    _ = (numer P : ℚ) * (numer Q : ℚ) := by rw [mul_one,hPQ,hQP,mul_comm]
    _ = _ := by rw [← clear_denoms P hp, ← clear_denoms Q hq, mul_mul_mul_comm]

/-- A Diophantine frame gives a solution of the original variant. -/
theorem forward_frame (h : FrameExists) : Original := by
  obtain ⟨P₀, Q₀, hP, hQ, hp2, hq2, hpwP, hpwQ, hcop, hlt, hleP, hleQ, hdivP, hdivQ⟩ := h
  let M := denom P₀
  let M' := numer P₀
  let N := denom Q₀
  let N' := numer Q₀
  let Δ := M * N - M' * N'
  let p := (M * N' + N ^ 2) / Δ
  let q := (M' * N + M ^ 2) / Δ
  have hΔ : 0 < Δ := Nat.sub_pos_of_lt hlt
  have hp : 2 ≤ p := (Nat.le_div_iff_mul_le hΔ).2 hleP
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le hΔ).2 hleQ
  have hmulP : Δ * p = M * N' + N ^ 2 := Nat.mul_div_cancel' hdivP
  have hmulQ : Δ * q = M' * N + M ^ 2 := Nat.mul_div_cancel' hdivQ
  obtain ⟨hcP, hcQ⟩ := frame_cross_eq hlt rfl hmulP hmulQ
  obtain ⟨hnP, hpP⟩ := extend_coprime hp hpwP fun a ha =>
    frame_coprime (dvd_denom ha) (Nat.coprime_prod_right_iff.2 fun b hb => hcop a ha b hb) hcP hcQ
  obtain ⟨hnQ, hpQ⟩ := extend_coprime hq hpwQ fun b hb =>
    frame_coprime (dvd_denom hb) (Nat.coprime_prod_right_iff.2 fun a ha => (hcop a ha b hb).symm) hcQ hcP
  have hP₂ (a : ℕ) (ha : a ∈ insert p P₀) : 2 ≤ a := by
    rcases Finset.mem_insert.mp ha with rfl | hin
    · exact hp
    · exact hp2 a hin
  have hQ₂ (b : ℕ) (hb : b ∈ insert q Q₀) : 2 ≤ b := by
    rcases Finset.mem_insert.mp hb with rfl | hin
    · exact hq
    · exact hq2 b hin
  refine ⟨insert p P₀, insert q Q₀, ?_, ?_, ?_, ?_, hpP, hpQ, ?_⟩
  · intro hzero
    have := hP₂ 0 (Finset.mem_inter.mp hzero).1
    omega
  · intro hone
    rcases Finset.mem_union.mp hone with hin | hin
    · have := hP₂ 1 hin
      omega
    · have := hQ₂ 1 hin
      omega
  · rw [Finset.card_insert_of_notMem hnP]
    have := Finset.card_pos.mpr hP
    omega
  · rw [Finset.card_insert_of_notMem hnQ]
    have := Finset.card_pos.mpr hQ
    omega
  · apply reciprocal_mul_of_swap (fun a ha => by have := hP₂ a ha; omega)
      (fun b hb => by have := hQ₂ b hb; omega)
    · rw [numer_insert hnP (by omega)]
      change p * numer P₀ + denom P₀ = ∏ b ∈ insert q Q₀, b
      rw [Finset.prod_insert hnQ (f := fun b => b), mul_comm q]
      exact hcP
    · rw [numer_insert hnQ (by omega)]
      change q * numer Q₀ + denom Q₀ = ∏ a ∈ insert p P₀, a
      rw [Finset.prod_insert hnP (f := fun a => a), mul_comm p]
      exact hcQ

/-- The original variant is equivalent to the integer-only frame existence problem. -/
theorem original_iff_frame : Original ↔ FrameExists :=
  ⟨reverse_frame, forward_frame⟩

end Erdos307Structure

#print axioms Erdos307Structure.swap_products
#print axioms Erdos307Structure.original_iff_frame
