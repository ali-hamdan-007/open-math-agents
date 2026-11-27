import Erdos307EvenSupportJacobi
import Erdos307EvenSupportResidues
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Tactic.IntervalCases

namespace Erdos307Structure
open Finset
open scoped BigOperators

private theorem support_member_dvd {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    p ∣ denom S := Finset.dvd_prod_of_mem id hp

private theorem support_cofactor_erase {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ S) (hp0 : 0 < p) : denom S / p = denom (S.erase p) := by
  have h : denom (S.erase p) * p = denom S := Finset.prod_erase_mul S id hp
  rw [← h, Nat.mul_div_cancel _ hp0]

private theorem support_product_union {S T : Finset ℕ} (h : Disjoint S T) :
    denom (S ∪ T) = denom S * denom T := Finset.prod_union h

private theorem support_numer_union {S T : Finset ℕ} (h : Disjoint S T) :
    numer (S ∪ T) = numer S * denom T + denom S * numer T := by
  simp only [numer, Finset.sum_union h, support_product_union h, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm (denom S) (denom T), Nat.mul_div_assoc _ (support_member_dvd hx), mul_comm]
  · exact Finset.sum_congr rfl (fun x hx => Nat.mul_div_assoc _ (support_member_dvd hx))

private theorem support_product_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) :
    denom (insert a S) = a * denom S := Finset.prod_insert ha

private theorem support_numer_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (hp : 0 < a) :
    numer (insert a S) = denom S + a * numer S := by
  rw [numer, Finset.sum_insert ha, support_product_insert ha, Nat.mul_div_cancel_left _ hp,
    numer, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x hx => Nat.mul_div_assoc a (support_member_dvd hx))

private theorem odd_square_mod_eight {n : ℕ} (h : Odd n) : (n : ZMod 8)^2 = 1 := by
  have hm := Nat.odd_iff.mp h
  have hcases : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rw [← ZMod.natCast_mod n 8]
  rcases hcases with hc | hc | hc | hc <;> rw [hc] <;> decide

private theorem product_odd {S : Finset ℕ} (h : ∀ p ∈ S, Odd p) : Odd (denom S) :=
  Finset.prod_induction _ Odd (fun _ _ h₁ h₂ => h₁.mul h₂) odd_one h

private theorem deriv_mod_eight_of_odd_support {S : Finset ℕ} (hO : ∀ p ∈ S, Odd p) :
    (numer S : ZMod 8) = (denom S : ZMod 8) * ∑ p ∈ S, (p : ZMod 8) := by
  rw [numer, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : ((denom S / p : ℕ) : ZMod 8) * (p : ZMod 8) = (denom S : ZMod 8) :=
    (Nat.cast_mul _ _).symm.trans
      (congrArg (fun n : ℕ => (n : ZMod 8)) (Nat.div_mul_cancel (support_member_dvd hp)))
  calc
    _ = ((denom S / p : ℕ) : ZMod 8) * (p : ZMod 8)^2 := by
      rw [odd_square_mod_eight (hO p hp), mul_one]
    _ = _ := by rw [pow_two, ← mul_assoc, he]

private theorem product_and_sum_mod_four {S : Finset ℕ} (hO : ∀ p ∈ S, Odd p) :
    let m := (S.filter fun p => p % 4 = 3).card
    denom S % 4 = (if m % 2 = 0 then 1 else 3) ∧
      (∑ p ∈ S, p) % 4 = (S.card + 2*m) % 4 := by
  classical
  induction S using Finset.induction_on with
  | empty => decide
  | @insert a S ha ih =>
    have h := ih (fun p hp => hO p (mem_insert_of_mem hp))
    let m := (S.filter fun p => p % 4 = 3).card
    change denom S % 4 = (if m % 2 = 0 then 1 else 3) ∧
      (∑ p ∈ S, p) % 4 = (S.card + 2*m) % 4 at h
    have hao := Nat.odd_iff.mp (hO a (mem_insert_self _ _))
    rw [support_product_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Finset.filter_insert, Nat.mul_mod a (denom S) 4, Nat.add_mod a _ 4, h.1, h.2]
    rcases Nat.odd_mod_four_iff.mp hao with h1 | h3
    · rw [if_neg (show ¬ a % 4 = 3 by omega), h1]
      change (1 * (if m % 2 = 0 then 1 else 3)) % 4 =
          (if m % 2 = 0 then 1 else 3) ∧ _
      constructor
      · by_cases he : m % 2 = 0 <;> simp [he]
      · omega
    · have hna : a ∉ S.filter (fun p => p % 4 = 3) := fun ha' => ha (mem_filter.mp ha').1
      rw [if_pos h3, Finset.card_insert_of_notMem hna, h3]
      change (3 * (if m % 2 = 0 then 1 else 3)) % 4 =
          (if (m + 1) % 2 = 0 then 1 else 3) ∧ _
      constructor
      · by_cases he : m % 2 = 0
        · have he' : (m + 1) % 2 ≠ 0 := by omega
          simp [he, he']
        · have he' : (m + 1) % 2 = 0 := by omega
          simp [he, he']
      · omega

private theorem even_choose_two_iff (m : ℕ) :
    Even (m.choose 2) ↔ m % 4 = 0 ∨ m % 4 = 1 := by
  by_cases hz : m = 0
  · simp [hz]
  have he : (m * (m-1) / 2) % 2 = (m * (m-1) % 4) / 2 := by omega
  have hm : (m-1) % 4 = (m%4+3)%4 := by omega
  rw [Nat.even_iff, Nat.choose_two_right, he, Nat.mul_mod m _ 4, hm]
  have hlt : m % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hh : m % 4 <;> decide

private theorem isolated_even_side_mod_eight {A B : Finset ℕ}
    (ha2 : 2 ∈ A) (hb2 : 2 ∉ B) (ha : ∀ p ∈ A, p.Prime) (hb : ∀ p ∈ B, p.Prime) :
    (denom A : ZMod 8)^2 + (denom B : ZMod 8)^2 = 5 := by
  have haodd : Odd (denom (A.erase 2)) := product_odd (fun p hp =>
    (ha p (mem_of_mem_erase hp)).eq_two_or_odd'.resolve_left (ne_of_mem_erase hp))
  have hbodd : Odd (denom B) := product_odd (fun p hp =>
    (hb p hp).eq_two_or_odd'.resolve_left (fun e => hb2 (e ▸ hp)))
  have hprod : denom A = 2 * denom (A.erase 2) := by
    rw [← support_product_insert (show 2 ∉ A.erase 2 by simp), Finset.insert_erase ha2]
  rw [hprod, Nat.cast_mul, mul_pow, odd_square_mod_eight haodd, odd_square_mod_eight hbodd,
    mul_one]
  decide

/-- For an all-prime reciprocal-product solution using 2, the number of
odd primes congruent to one modulo four is two modulo four. Its odd support
product is also fixed modulo eight by the number of odd primes. -/
theorem prime_even_support_count {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hmul : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹))
    (h2 : 2 ∈ P ∪ Q) :
    let S := (P ∪ Q).erase 2
    let k := S.card
    let m := (S.filter fun p => p % 4 = 3).card
    (k - m) % 4 = 2 ∧
      denom S % 8 = (if k % 4 = 0 then 5 else if k % 4 = 1 then 3 else
        if k % 4 = 2 then 1 else 7) := by
  classical
  let T := P ∪ Q
  let S := T.erase 2
  let k := S.card
  let m := (S.filter fun p => p % 4 = 3).card
  have hpw : Set.Pairwise (P : Set ℕ) Nat.Coprime :=
    fun p hp q hq hne => (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hne
  have hqw : Set.Pairwise (Q : Set ℕ) Nat.Coprime :=
    fun p hp q hq hne => (Nat.coprime_primes (hQ p hp) (hQ q hq)).mpr hne
  obtain ⟨hPQ,hQP,hcross⟩ := swap_products P Q (fun p hp => (hP p hp).pos)
    (fun p hp => (hQ p hp).pos) hpw hqw hmul
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have he := hcross p hp p hq
    rw [Nat.Coprime, Nat.gcd_self] at he
    exact (hP p hp).ne_one he
  have hST : insert 2 S = T := Finset.insert_erase h2
  have hNot : 2 ∉ S := Finset.notMem_erase _ _
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime :=
    (Finset.mem_union.mp hp).elim (hP p) (hQ p)
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := hT p (Finset.mem_of_mem_erase hp)
  have ho (p : ℕ) (hp : p ∈ S) : Odd p :=
    (hS p hp).eq_two_or_odd'.resolve_left (Finset.ne_of_mem_erase hp)
  have hsum : (numer T : ZMod 8) = 5 := by
    change (numer (P ∪ Q) : ZMod 8) = 5
    rw [support_numer_union hdis, hPQ,hQP, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ← pow_two, ← pow_two]
    rcases Finset.mem_union.mp h2 with hp | hq
    · rw [add_comm]
      exact isolated_even_side_mod_eight hp (fun h => Finset.disjoint_left.mp hdis hp h) hP hQ
    · exact isolated_even_side_mod_eight hq (fun h => Finset.disjoint_left.mp hdis h hq) hQ hP
  have hder : (((denom S * (1 + 2 * ∑ p ∈ S, p) : ℕ) : ZMod 8)) = 5 := by
    rw [← hST, support_numer_insert hNot (by decide), Nat.cast_add, Nat.cast_mul,
      deriv_mod_eight_of_odd_support ho] at hsum
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, ← hsum]
    push_cast
    ring
  have hm4 := product_and_sum_mod_four ho
  change denom S % 4 = (if m % 2 = 0 then 1 else 3) ∧
    (∑ p ∈ S, p) % 4 = (k + 2*m) % 4 at hm4
  have hder' := (ZMod.natCast_eq_natCast_iff' (denom S * (1 + 2 * ∑ p ∈ S, p)) 5 8).mp hder
  have ht8 : (1 + 2 * ∑ p ∈ S, p) % 8 = (1 + 2*k + 4*m) % 8 := by omega
  have hd : (denom S * (1 + 2*k + 4*m)) % 8 = 5 := by
    rw [Nat.mul_mod, ← ht8, ← Nat.mul_mod]
    exact hder'
  have hj (p : ℕ) (hp : p ∈ S) :
      jacobiSym ((2 : ℤ) * (denom (S.erase p) : ℤ)) p = 1 := by
    have hpT := Finset.mem_of_mem_erase hp
    have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
    have hc : denom T / p = 2 * denom (S.erase p) := by
      rw [support_cofactor_erase hpT (hS p hp).pos, ← hST,
        Finset.erase_insert_of_ne hp2.symm, support_product_insert
          (fun hn => hNot (Finset.mem_of_mem_erase hn))]
    have hsq := support_cofactor_isSquare_of_reciprocals
      (fun p hp => (hP p hp).one_lt) (fun p hp => (hQ p hp).one_lt) hpw hqw hmul hpT
    change IsSquare (((denom T / p : ℕ) : ZMod p)) at hsq
    rw [hc, Nat.cast_mul] at hsq
    let _ : Fact p.Prime := ⟨hS p hp⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    apply (legendreSym.eq_one_iff p ?_).mpr
    · push_cast
      exact hsq
    · push_cast
      change ((2 : ℕ) : ZMod p) * (denom (S.erase p) : ZMod p) ≠ 0
      rw [← Nat.cast_mul]
      apply (ZMod.natCast_eq_zero_iff _ _).not.mpr
      intro hz
      have hpp := hS p hp
      rcases hpp.dvd_mul.mp hz with htwo | hprod
      · rcases (Nat.dvd_prime Nat.prime_two).mp htwo with he | he
        · exact hpp.ne_one he
        · exact hp2 he
      · obtain ⟨q,hq,hdiv⟩ :=
          (hpp.prime.dvd_finsetProd_iff (S := S.erase p) id).mp hprod
        rcases (Nat.dvd_prime (hS q (Finset.mem_of_mem_erase hq))).mp hdiv with he | he
        · exact hpp.ne_one he
        · exact Finset.ne_of_mem_erase hq he.symm
  have hrec := jacobi_two_of_even_support S hS ho hj
  have how := product_odd ho
  rw [jacobiSym.at_two how, ZMod.χ₈_nat_eq_if_mod_eight, Nat.odd_iff.mp how, if_neg (by decide)] at hrec
  have hsign : (denom S % 8 = 1 ∨ denom S % 8 = 7) ↔ (m % 4 = 0 ∨ m % 4 = 1) := by
    rw [← even_choose_two_iff]
    rw [← neg_one_pow_eq_one_iff_even (show (-1 : ℤ) ≠ 1 by decide), ← hrec]
    by_cases he : denom S % 8 = 1 ∨ denom S % 8 = 7 <;> simp [he]
  exact even_support_one_mod_four_count (Finset.card_filter_le _ _) hm4.1 hd hsign

/-- Direct finite-set form of the congruence on the number of primes
which are one modulo four. -/
theorem prime_one_mod_four_count {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hmul : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹))
    (h2 : 2 ∈ P ∪ Q) : ((P ∪ Q).filter fun p => p % 4 = 1).card % 4 = 2 := by
  let T := P ∪ Q
  let S := T.erase 2
  have heq : S.filter (fun p => ¬ p % 4 = 3) = T.filter (fun p => p % 4 = 1) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hp,hn⟩
      obtain ⟨hp2,hpT⟩ := Finset.mem_erase.mp hp
      have hprime := (Finset.mem_union.mp hpT).elim (hP p) (hQ p)
      have hodd := hprime.eq_two_or_odd'.resolve_left hp2
      exact ⟨hpT, (Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd)).resolve_right hn⟩
    · rintro ⟨hp,hp1⟩
      exact ⟨Finset.mem_erase.mpr ⟨by omega, hp⟩, by omega⟩
  have hc := Finset.card_filter_add_card_filter_not (s := S) (fun p => p % 4 = 3)
  rw [heq] at hc
  have ht := (prime_even_support_count hP hQ hmul h2).1
  change (S.card - (S.filter fun p => p % 4 = 3).card) % 4 = 2 at ht
  have hn : S.card - (S.filter fun p => p % 4 = 3).card =
      (T.filter fun p => p % 4 = 1).card := by omega
  rwa [hn] at ht

#print axioms prime_even_support_count
#print axioms prime_one_mod_four_count

end Erdos307Structure
