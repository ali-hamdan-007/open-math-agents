import A056777Squarefree
import Mathlib.Tactic.IntervalCases

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777OddFour

private theorem odd_prime_of_mem {n p : ℕ} (hn : Odd n) (hp : p ∈ n.primeFactors) : Odd p := by
  have hd := (Nat.mem_primeFactors.mp hp).2.1
  rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with rfl | h
  · have := Nat.odd_iff.mp hn
    omega
  · exact Nat.odd_iff.mpr h

/-- Every distinct prime factor of an odd integer contributes a factor of two to its totient. -/
theorem two_pow_card_dvd_totient {n : ℕ} (hn : Odd n) :
    2 ^ n.primeFactors.card ∣ n.totient := by
  have hz : n ≠ 0 := by have := Nat.odd_iff.mp hn; omega
  rw [Nat.totient_eq_prod_factorization hz, Finsupp.prod, Nat.support_factorization,
    ← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  apply dvd_mul_of_dvd_right
  have := Nat.odd_iff.mp (odd_prime_of_mem hn hp)
  omega

private theorem four_dvd_geom_even_length {p : ℕ} (hp : 4 ∣ p + 1) (k : ℕ) :
    4 ∣ ∑ i ∈ Finset.range (2 * k), p ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k+1) = 2*k+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    apply dvd_add ih
    have h := dvd_mul_of_dvd_right hp (p ^ (2*k))
    rw [pow_succ p (2*k)]
    simpa [Nat.mul_add, add_comm] using h

private theorem even_sigma_prime_powers_mul {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hop : Odd p) (hoq : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hcount : Even (a+b))
    (ht : ¬ 8 ∣ (p^a*q^b).totient) :
    Odd (σ 1 (p^a*q^b)) ∨ 8 ∣ σ 1 (p^a*q^b) := by
  have hco := (((Nat.coprime_primes hp hq).mpr hne).pow_left a).pow_right b
  have hφ : (p^a*q^b).totient =
      (p^(a-1)*(p-1))*(q^(b-1)*(q-1)) := by
    rw [Nat.totient_mul hco, Nat.totient_prime_pow hp ha, Nat.totient_prime_pow hq hb]
  have hp1 := Nat.odd_iff.mp hop
  have hq1 := Nat.odd_iff.mp hoq
  have hpp : 4 ∣ p+1 := by
    by_contra h
    have hp4 : 4 ∣ p - 1 := by omega
    have hq2 : 2 ∣ q - 1 := by omega
    exact ht (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right hp4 _) (dvd_mul_of_dvd_right hq2 _))
  have hqp : 4 ∣ q+1 := by
    by_contra h
    have hq4 : 4 ∣ q - 1 := by omega
    have hp2 : 2 ∣ p - 1 := by omega
    exact ht (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right hp2 _) (dvd_mul_of_dvd_right hq4 _))
  have hh := Nat.even_iff.mp hcount
  by_cases hae : a % 2 = 0
  · left
    have hbe : b % 2 = 0 := by omega
    have hz : p^a*q^b ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
    apply (A056777Parity.odd_sigma_iff_square_or_twice_square hz).mpr
    exact Or.inl ⟨p^(a/2)*q^(b/2), by rw [mul_pow, ← pow_mul, ← pow_mul,
      show a/2*2 = a by omega, show b/2*2 = b by omega]⟩
  · right
    rw [isMultiplicative_sigma.map_mul_of_coprime hco, sigma_one_apply_prime_pow hp,
      sigma_one_apply_prime_pow hq]
    have ha' : a+1 = 2*((a+1)/2) := by omega
    have hb' : b+1 = 2*((b+1)/2) := by omega
    have hd₁ : 4 ∣ ∑ i ∈ Finset.range (a+1), p^i := by
      calc
        4 ∣ ∑ i ∈ Finset.range (2*((a+1)/2)), p^i := four_dvd_geom_even_length hpp _
        _ = _ := by rw [← ha']
    have hd₂ : 4 ∣ ∑ i ∈ Finset.range (b+1), q^i := by
      calc
        4 ∣ ∑ i ∈ Finset.range (2*((b+1)/2)), q^i := four_dvd_geom_even_length hqp _
        _ = _ := by rw [← hb']
    exact (show 8 ∣ 4*4 by decide).trans (mul_dvd_mul hd₁ hd₂)

private theorem sigma_of_odd_even_count {n : ℕ} (hn : Odd n)
    (hl : Even n.primeFactorsList.length)
    (ht : ¬ 8 ∣ n.totient) :
    Odd (σ 1 n) ∨ 8 ∣ σ 1 n := by
  by_cases hone : n = 1
  · subst n
    exact Or.inl (by decide)
  have hz : n ≠ 0 := by have := Nat.odd_iff.mp hn; omega
  have hcard : n.primeFactors.card ≤ 2 := by
    by_contra! h
    exact ht ((pow_dvd_pow 2 h).trans (two_pow_card_dvd_totient hn))
  have hpos : 0 < n.primeFactors.card := by
    by_contra! h
    have he : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
    exact (Nat.primeFactors_eq_empty.mp he).elim hz hone
  have hprod := Nat.prod_factorization_pow_eq_self hz
  rw [Finsupp.prod, Nat.support_factorization] at hprod
  rcases (show n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 by omega) with h₁ | h₂
  · obtain ⟨p, hpF⟩ := Finset.card_eq_one.mp h₁
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hpF])
    rw [hpF, Finset.prod_singleton] at hprod
    have he := hl
    rw [← hprod, hp.primeFactorsList_pow, List.length_replicate] at he
    have hh := Nat.even_iff.mp he
    left
    apply (A056777Parity.odd_sigma_iff_square_or_twice_square hz).mpr
    exact Or.inl ⟨p ^ (n.factorization p / 2),
      hprod.symm.trans (by rw [← pow_mul, show n.factorization p / 2 * 2 = n.factorization p by omega])⟩
  · obtain ⟨p,q,hne,hpF⟩ := Finset.card_eq_two.mp h₂
    have hpm : p ∈ n.primeFactors := by simp [hpF]
    have hqm : q ∈ n.primeFactors := by simp [hpF]
    have hp := Nat.prime_of_mem_primeFactors hpm
    have hq := Nat.prime_of_mem_primeFactors hqm
    have hop := odd_prime_of_mem hn hpm
    have hoq := odd_prime_of_mem hn hqm
    let a := n.factorization p
    let b := n.factorization q
    have ha : 0 < a := hp.factorization_pos_of_dvd hz (Nat.mem_primeFactors.mp hpm).2.1
    have hb : 0 < b := hq.factorization_pos_of_dvd hz (Nat.mem_primeFactors.mp hqm).2.1
    rw [hpF, Finset.prod_insert (by simpa using hne), Finset.prod_singleton] at hprod
    change p ^ a * q ^ b = n at hprod
    have hlen := (Nat.perm_primeFactorsList_mul (pow_ne_zero a hp.ne_zero)
      (pow_ne_zero b hq.ne_zero)).length_eq
    rw [hprod, hp.primeFactorsList_pow, hq.primeFactorsList_pow,
      List.length_append, List.length_replicate, List.length_replicate] at hlen
    rw [hlen] at hl
    rw [← hprod] at ht ⊢
    exact even_sigma_prime_powers_mul hp hq hne hop hoq ha hb hl ht

/-- An odd endpoint with an even number of prime factors (with multiplicity) cannot be
twelve away from an odd squarefree endpoint
with at least three prime factors if both arithmetic-function jumps equal the gap. -/
theorem no_squarefree_odd_even_count_pair {n m : ℕ}
    (hn : Odd n) (hm : Odd m) (hnf : Squarefree n)
    (hncard : 3 ≤ n.primeFactors.card)
    (hmeven : Even m.primeFactorsList.length)
    (hgap : n + 12 = m ∨ m + 12 = n)
    (hφ : n.totient + m = m.totient + n)
    (hσ : σ 1 n + m = σ 1 m + n) : False := by
  have hdφ : 8 ∣ n.totient := (pow_dvd_pow 2 hncard).trans (two_pow_card_dvd_totient hn)
  have hfilt : (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)) =
      n.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have ho := Nat.odd_iff.mp (odd_prime_of_mem hn hp)
    have hpos := hp'.factorization_pos_of_dvd hnf.ne_zero (Nat.mem_primeFactors.mp hp).2.1
    have hle := hnf.natFactorization_le_one p
    have he : n.factorization p = 1 := by omega
    exact ⟨by omega, he ▸ (by decide : Odd 1)⟩
  have hdσ := A056777Squarefree.two_pow_card_odd_exponents_dvd_sigma hnf.ne_zero
  rw [hfilt] at hdσ
  have hdσ' : 8 ∣ σ 1 n := (pow_dvd_pow 2 hncard).trans hdσ
  have hmφ : ¬ 8 ∣ m.totient := by omega
  rcases sigma_of_odd_even_count hm hmeven hmφ with ho | hd
  · have := Nat.odd_iff.mp ho
    omega
  · omega

/-- The odd squarefree case with an odd four-factor partner is excluded. -/
theorem no_squarefree_odd_four_pair {n m : ℕ}
    (hn : Odd n) (hm : Odd m) (hnf : Squarefree n)
    (hncard : 3 ≤ n.primeFactors.card)
    (hmfour : m.primeFactorsList.length = 4)
    (hgap : n + 12 = m ∨ m + 12 = n)
    (hφ : n.totient + m = m.totient + n)
    (hσ : σ 1 n + m = σ 1 m + n) : False :=
  no_squarefree_odd_even_count_pair hn hm hnf hncard (hmfour ▸ (by decide : Even 4))
    hgap hφ hσ

end A056777OddFour

#print axioms A056777OddFour.no_squarefree_odd_even_count_pair
