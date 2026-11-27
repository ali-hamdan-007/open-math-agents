import SmallPairs
import A056777OddSquarefreeThreeFiveMoments
import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777.SmallPairs

private theorem squarefree_triple_shape {n : ℕ}
    (hn : n.primeFactorsList.length=3) (hs : Squarefree n) :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧
      a<b ∧ b<c ∧ n=a*b*c := by
  obtain ⟨a,b,c,he⟩ : ∃ a b c, n.primeFactorsList = [a,b,c] := by
    generalize hl : n.primeFactorsList = l at hn ⊢
    rcases l with _ | ⟨a,l⟩
    · simp at hn
    rcases l with _ | ⟨b,l⟩
    · simp at hn
    rcases l with _ | ⟨c,l⟩
    · simp at hn
    rcases l with _ | ⟨d,l⟩
    · exact ⟨a,b,c,rfl⟩
    · simp at hn
  have ha := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=a) (by simp [he])
  have hb := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=b) (by simp [he])
  have hc := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=c) (by simp [he])
  have hnd := hs.nodup_primeFactorsList
  simp only [he,List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at hnd
  have hsorted := (Nat.primeFactorsList_sorted n).pairwise
  simp only [he, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at hsorted
  have hab : a ≤ b := hsorted.1 b (Or.inl rfl)
  have hbc : b ≤ c := hsorted.2.1 c rfl
  exact ⟨a,b,c,ha,hb,hc,lt_of_le_of_ne hab hnd.1.1,lt_of_le_of_ne hbc hnd.2,
    by simpa [he,mul_assoc] using (Nat.prod_primeFactorsList hs.ne_zero).symm⟩

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p=p+1 := by
  simpa using sigma_one_apply_prime_pow (i:=1) hp

private theorem triple_formulas {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    (a*b*c).totient+(a*b+a*c+b*c)+1=a*b*c+(a+b+c) ∧
      σ 1 (a*b*c)+(a*b*c).totient=2*(a*b*c)+2*(a+b+c) := by
  have h₁ := (Nat.coprime_primes ha hb).mpr hab
  have h₂ := ((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc)
  rw [Nat.totient_mul h₂,Nat.totient_mul h₁,Nat.totient_prime ha,Nat.totient_prime hb,
    Nat.totient_prime hc,isMultiplicative_sigma.map_mul_of_coprime h₂,
    isMultiplicative_sigma.map_mul_of_coprime h₁,sigma_prime ha,sigma_prime hb,sigma_prime hc]
  have ha1 := ha.pos
  have hb1 := hb.pos
  have hc1 := hc.pos
  zify [ha1,hb1,hc1]
  constructor <;> ring

private theorem fourth_times_prime_formulas {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) :
    (p^4*q).totient+p^3*(p+q-1)=p^4*q ∧
      σ 1 (p^4*q)+(p^4*q).totient=2*(p^4*q)+(p^2+p+1)*(q+1)+2*p^3 := by
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 4
  have hsig : σ 1 (p^4)=1+p+p^2+p^3+p^4 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  rw [Nat.totient_mul hc,show (p^4).totient=p^3*(p-1) from Nat.totient_prime_pow_succ hp 3,
    Nat.totient_prime hq,isMultiplicative_sigma.map_mul_of_coprime hc,hsig,sigma_prime hq]
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hpq1 : 1≤p+q := by omega
  zify [hp1,hq1,hpq1]
  constructor <;> ring

/-- An exclusion entirely within the two smaller prime roots suffices.
It uses neither the large root nor an independent unrepeated prime parameter. -/
def PairBarrier : Prop :=
  ∀ p a b : ℕ, p.Prime → a.Prime → b.Prime → p%4=3 →
    (p%5=2 ∨ p%5=3) → 23≤p → 11<a → a<b → b<p →
    p^2<a^3 → 2*a*b<p^2 → ¬ p^3 ∣ pairExpr a b

theorem exact_residual_of_pair_barrier (no : PairBarrier) :
    OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1.H2 := by
  intro n m hn hm ho hs hg hphi hsig _
  obtain ⟨_,p,q,hp,hq,hpq,hp4,_,hq11,h70,_,hsize,hp5,_,rfl,hroots⟩ :=
    A056777OddSquarefreeThreeFive.odd_squarefree_three_five_sharp_root_bounds
      hn hm hs ho (Or.inr hg) hphi hsig
  obtain ⟨a,b,c,ha,hb,hc,hab,hbc,rfl⟩ := squarefree_triple_shape hn hs
  have hac := hab.trans hbc
  have haQ : q<a := hroots a ha ⟨b*c,by ring⟩
  have hpgt : 2*q<p := by omega
  have ⟨hF,hK⟩ := fourth_times_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas ha hb hc hab.ne hac.ne hbc.ne
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c) := by omega
  have hprod : a*b*c=p^4*q+12 := hg.symm
  have hpair : p^3 ∣ pairExpr a b :=
    moment_pair_dvd_nat p q a b c ha.pos hb.pos (by omega) hM hprod
  have hM' := hM
  have hL' := hL
  have hZ' := hprod
  have hpq1 : 1≤p+q := by omega
  zify [hpq1] at hM' hL' hZ'
  obtain ⟨_,hbP,_,habP⟩ := two_small_one_large (p:ℤ) q a b c
    (by exact_mod_cast (show 5≤p by omega)) (by exact_mod_cast hq11)
    (by exact_mod_cast hpgt) (by exact_mod_cast ha.pos)
    (by exact_mod_cast hab.le) (by exact_mod_cast hbc.le) hL' hM' hZ'
  have hsize' : p^2<a^3 := hsize.trans (Nat.pow_lt_pow_left haQ (by decide))
  have habP' : a*b < p*q := by exact_mod_cast habP
  have hmul := Nat.mul_lt_mul_of_pos_left hpgt hp.pos
  have h2ab := Nat.mul_lt_mul_of_pos_left habP' (by decide : 0<2)
  have hlast : 2*a*b < p^2 := by
    rw [Nat.mul_assoc]
    exact h2ab.trans (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul)
  exact no p a b hp ha hb hp4 hp5 (by omega) (by omega) hab
    (by exact_mod_cast hbP) hsize' hlast hpair

end A056777.SmallPairs

#print axioms A056777.SmallPairs.exact_residual_of_pair_barrier
