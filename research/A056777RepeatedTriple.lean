import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open Nat

namespace A056777RepeatedTriple

/-- A nonsquarefree number with exactly three prime factors has the form p²q. -/
theorem pow_two_mul_of_nonsquarefree_length_three {n : ℕ}
    (h : n.primeFactorsList.length = 3) (hs : ¬ Squarefree n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p ^ 2 * q := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  have hn' := Nat.prod_primeFactorsList hn
  have hd : ¬ n.primeFactorsList.Nodup := fun hnd =>
    hs ((Nat.squarefree_iff_nodup_primeFactorsList hn).mpr hnd)
  have hp {p : ℕ} (hm : p ∈ n.primeFactorsList) := Nat.prime_of_mem_primeFactorsList hm
  obtain ⟨a, b, c, heq⟩ : ∃ a b c, n.primeFactorsList = [a,b,c] := by
    generalize hl : n.primeFactorsList = l at h ⊢
    cases l with
    | nil => simp at h
    | cons a l =>
      cases l with
      | nil => simp at h
      | cons b l =>
        cases l with
        | nil => simp at h
        | cons c l =>
          cases l with
          | nil => exact ⟨a,b,c,rfl⟩
          | cons d l => simp at h
  have ha := hp (p := a) (by simp [heq])
  have hb := hp (p := b) (by simp [heq])
  have hc := hp (p := c) (by simp [heq])
  simp only [heq, List.prod_cons, List.prod_nil, mul_one] at hn'
  have hrepeated : a = b ∨ a = c ∨ b = c := by
    by_contra! H
    apply hd
    simp [heq, H.1, H.2.1, H.2.2]
  rcases hrepeated with rfl | rfl | rfl
  · exact ⟨a, c, ha, hc, by nlinarith only [hn']⟩
  · exact ⟨a, b, ha, hb, by nlinarith only [hn']⟩
  · exact ⟨b, a, hb, ha, by nlinarith only [hn']⟩

private theorem totient_defect_cube {p : ℕ} (hp : p.Prime) :
    (p ^ 3).totient + p ^ 2 = p ^ 3 := by
  rw [show 3 = 2 + 1 by rfl, Nat.totient_prime_pow_succ hp]
  have h : p - 1 + 1 = p := by have := hp.one_lt; omega
  calc
    p ^ 2 * (p - 1) + p ^ 2 = p ^ 2 * (p - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ = p ^ (2 + 1) := by rw [h]; exact (pow_succ p 2).symm

private theorem totient_defect_repeated {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hne : r ≠ s) :
    (r ^ 2 * s).totient + r * (r + s - 1) = r ^ 2 * s := by
  have hcop := ((Nat.coprime_primes hr hs).mpr hne).pow_left 2
  rw [Nat.totient_mul hcop, show 2 = 1 + 1 by rfl, Nat.totient_prime_pow_succ hr,
    pow_one, Nat.totient_prime hs]
  have hr1 : 1 ≤ r := hr.pos
  have hs1 : 1 ≤ s := hs.pos
  have hrs : 1 ≤ r + s := by omega
  zify [hr1, hs1, hrs]
  ring

/-- A prime cube and a product r²s of distinct primes have different totient defects. -/
theorem cube_defect_ne_repeated_defect {p r s : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hs : s.Prime) (hne : r ≠ s) :
    ¬ ((p ^ 3).totient + r ^ 2 * s = (r ^ 2 * s).totient + p ^ 3) := by
  intro he
  have hc := totient_defect_cube hp
  have hq := totient_defect_repeated hr hs hne
  have heq : p ^ 2 = r * (r + s - 1) := by omega
  have hdiv : r ∣ p ^ 2 := ⟨r + s - 1, heq⟩
  have hdivp := hr.dvd_of_dvd_pow hdiv
  obtain h | h := (Nat.dvd_prime hp).mp hdivp
  · exact hr.ne_one h
  · subst r
    have hcancel : p = p + s - 1 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      simpa [pow_two] using heq
    have := hs.one_lt
    omega

/-- If both endpoints have three prime factors including repetitions, neither endpoint can
be a prime cube. Only the products of two distinct primes with one repeated remain. -/
theorem distinct_repeated_endpoints_of_totient_step {n : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : (n+12).primeFactorsList.length = 3)
    (hn' : ¬ Squarefree n) (hm' : ¬ Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12) :
    ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ p ≠ q ∧ r ≠ s ∧
      n = p ^ 2 * q ∧ n + 12 = r ^ 2 * s := by
  obtain ⟨p, q, hp, hq, hpq⟩ := pow_two_mul_of_nonsquarefree_length_three hn hn'
  obtain ⟨r, s, hr, hs, hrs⟩ := pow_two_mul_of_nonsquarefree_length_three hm hm'
  have hbal : n.totient + (n+12) = (n+12).totient + n := by omega
  have hbal' : (p ^ 2 * q).totient + r ^ 2 * s = (r ^ 2 * s).totient + p ^ 2 * q := by
    rw [← hpq, ← hrs]
    exact hbal
  clear hbal

  by_cases he₁ : p = q
  · subst q
    rw [← pow_succ] at hbal' hpq
    by_cases he₂ : r = s
    · subst s
      rw [← pow_succ] at hrs hbal'
      change (p ^ 3).totient + r ^ 3 = (r ^ 3).totient + p ^ 3 at hbal'
      have h₁ := totient_defect_cube hp
      have h₂ := totient_defect_cube hr
      have he : p ^ 2 = r ^ 2 := by omega
      have he' := (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp he
      subst r
      change n = p ^ 3 at hpq
      change n + 12 = p ^ 3 at hrs
      omega
    · exact (cube_defect_ne_repeated_defect hp hr hs he₂ hbal').elim
  · by_cases he₂ : r = s
    · subst s
      rw [← pow_succ] at hbal'
      exact (cube_defect_ne_repeated_defect hr hp hq he₁ hbal'.symm).elim
    · exact ⟨p, q, r, s, hp, hq, hr, hs, he₁, he₂, hpq, hrs⟩

end A056777RepeatedTriple

#print axioms A056777RepeatedTriple.distinct_repeated_endpoints_of_totient_step
