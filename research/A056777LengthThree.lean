import A056777Squarefree
import A056777RepeatedTripleApplication
import A056777CubeSquarefreeTriple
import A056777MixedTriple

open scoped ArithmeticFunction.sigma
open Nat

namespace A056777LengthThree

private theorem prime_triple_of_squarefree_length_three {n : ℕ}
    (h : n.primeFactorsList.length = 3) (hs : Squarefree n) :
    ∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ n = r*s*t := by
  have hprod := Nat.prod_primeFactorsList hs.ne_zero
  have hnd := hs.nodup_primeFactorsList
  obtain ⟨r,s,t,heq⟩ : ∃ r s t, n.primeFactorsList = [r,s,t] := by
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
  have hr := Nat.prime_of_mem_primeFactorsList (n := n) (p := r) (by simp [heq])
  have hsp := Nat.prime_of_mem_primeFactorsList (n := n) (p := s) (by simp [heq])
  have ht := Nat.prime_of_mem_primeFactorsList (n := n) (p := t) (by simp [heq])
  simp only [heq, List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hnd
  exact ⟨r,s,t,hr,hsp,ht,hnd.1.1,hnd.1.2,hnd.2,by simpa [heq, mul_assoc] using hprod.symm⟩

private theorem no_mixed_squarefree_nonsquarefree {n m : ℕ}
    (hlen₁ : n.primeFactorsList.length = 3) (hlen₂ : m.primeFactorsList.length = 3)
    (hns₁ : ¬ Squarefree n) (hsf₂ : Squarefree m)
    (hgap : n + 12 = m ∨ m + 12 = n)
    (hφ : n.totient + m = m.totient + n)
    (hσ : σ 1 n + m = σ 1 m + n) : False := by
  obtain ⟨p,q,hp,hq,rfl⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hlen₁ hns₁
  obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,rfl⟩ :=
    prime_triple_of_squarefree_length_three hlen₂ hsf₂
  by_cases he : p = q
  · subst q
    rw [← pow_succ] at hgap hφ hσ
    change (p ^ 3).totient + r*s*t = (r*s*t).totient + p ^ 3 at hφ
    change σ 1 (p ^ 3) + r*s*t = σ 1 (r*s*t) + p ^ 3 at hσ
    have hh := A056777CubeSquarefreeTriple.no_cube_squarefree_triple_at_distance_twelve
      hp hr hs ht hrs hrt hst (by omega)
    change p ^ 3 + 12 = r*s*t ∨ r*s*t + 12 = p ^ 3 at hgap
    omega
  · exact A056777MixedTriple.no_mixed_triple_gap_twelve hp hq hr hs ht he hrs hrt hst hgap hφ hσ

/-- The A056777 conditions cannot hold when both endpoints have exactly three prime factors
counted with multiplicity. This includes all repeated-factor shapes. -/
theorem no_pair_of_length_three {n : ℕ}
    (hlen₁ : n.primeFactorsList.length = 3)
    (hlen₂ : (n + 12).primeFactorsList.length = 3)
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) : False := by
  have hn : 1 < n := by
    by_contra! h
    interval_cases n <;> simp at hlen₁
  have hnp : ¬n.Prime := by
    intro hp
    simp [Nat.primeFactorsList_prime hp] at hlen₁
  have hφ : n.totient + (n + 12) = (n + 12).totient + n := by omega
  have hσ : σ 1 n + (n + 12) = σ 1 (n + 12) + n := by omega
  by_cases hsf₁ : Squarefree n <;> by_cases hsf₂ : Squarefree (n + 12)
  · obtain ⟨p,hp,_,_,hp',he⟩ := A056777Squarefree.prime_quadruple_of_squarefree_pair
      hn hnp hsf₁ hsf₂ ht hs
    have hlist := Nat.perm_primeFactorsList_mul hp.ne_zero hp'.ne_zero
    rw [← he, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hp'] at hlist
    have := hlist.length_eq
    simp [hlen₁] at this
  · exact no_mixed_squarefree_nonsquarefree hlen₂ hlen₁ hsf₂ hsf₁ (Or.inr rfl) hφ.symm hσ.symm
  · exact no_mixed_squarefree_nonsquarefree hlen₁ hlen₂ hsf₁ hsf₂ (Or.inl rfl) hφ hσ
  · exact A056777RepeatedTriple.no_pair_of_nonsquarefree_length_three hlen₁ hlen₂ hsf₁ hsf₂ ht hs

end A056777LengthThree

#print axioms A056777LengthThree.no_pair_of_length_three
