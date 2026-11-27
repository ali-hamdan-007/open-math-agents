import A056777OddSquarefreeThreeFive
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777OddSquarefreeThreeFive

private theorem squarefree_triple_shape {n : ℕ}
    (hn : n.primeFactorsList.length=3) (hs : Squarefree n) :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧
      a≠b ∧ a≠c ∧ b≠c ∧ n=a*b*c := by
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
  exact ⟨a,b,c,ha,hb,hc,hnd.1.1,hnd.1.2,hnd.2,
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

private def twiceSum (p q : ℤ) : ℤ := (p^2+p+1)*(q+1)+2*p^3
private def twicePairSum (p q : ℤ) : ℤ := 2*p^3*(p+q-1)+twiceSum p q-2

private def scaledDiscriminant (p q D : ℤ) : ℤ :=
  let L := twiceSum p q
  let M := twicePairSum p q
  let Z := p^4*q+D
  16*L^2*M^2-128*M^3-128*L^3*Z-6912*Z^2+1152*L*M*Z

private theorem negative_cubic_plus (p q : ℤ) (hp : 4≤p) (hq : p≤2*q) :
    scaledDiscriminant p q (12) < 0 := by
  let U := p-4
  let V := 2*q-p
  have hU : 0≤U := by dsimp [U]; omega
  have hV : 0≤V := by dsimp [V]; omega
  let c0 : ℤ := 45450586608+U*(151269655936+U*(237320663240+U*(231465309744+U*(156079495591+U*(76680177212+U*(28220821398+U*(7886565180+U*(1679079177+U*(270726024+U*(32515910+U*(2819452+U*(166767+U*(6020+U*(100))))))))))))))
  let c1 : ℤ := 58430090880+U*(186815798768+U*(275986987392+U*(249166894932+U*(153250173200+U*(67766232432+U*(22154623152+U*(5420113236+U*(992076744+U*(134155248+U*(13025848+U*(859860+U*(34584+U*(640)))))))))))))
  let c2 : ℤ := 8711949896+U*(25465819824+U*(34106887762+U*(27658865496+U*(15119219492+U*(5867108552+U*(1656955142+U*(343082072+U*(51683492+U*(5523792+U*(397538+U*(17296+U*(344))))))))))))
  let c3 : ℤ := 476170592+U*(1250465508+U*(1491138928+U*(1065569808+U*(506973776+U*(168622804+U*(40009560+U*(6772528+U*(801544+U*(63172+U*(2984+U*(64)))))))))))
  let c4 : ℤ := 9175887+U*(21161196+U*(21952614+U*(13495932+U*(5446985+U*(1508544+U*(290422+U*(38388+U*(3335+U*(172+U*(4))))))))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by dsimp [c0, c1, c2, c3, c4]; positivity
  have he : -scaledDiscriminant p q (12) = c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by
    dsimp [scaledDiscriminant, twiceSum, twicePairSum, U, V, c0, c1, c2, c3, c4]
    ring
  rw [←he] at hpos
  exact neg_pos.mp hpos

private theorem negative_cubic_minus (p q : ℤ) (hp : 4≤p) (hq : p≤2*q) :
    scaledDiscriminant p q (-12) < 0 := by
  let U := p-4
  let V := 2*q-p
  have hU : 0≤U := by dsimp [U]; omega
  have hV : 0≤V := by dsimp [V]; omega
  let c0 : ℤ := 28253174256+U*(113486935936+U*(200507752136+U*(210590123952+U*(148488609319+U*(74845082684+U*(27925988886+U*(7856221500+U*(1677264777+U*(270678024+U*(32515910+U*(2819452+U*(166767+U*(6020+U*(100))))))))))))))
  let c1 : ℤ := 55491509376+U*(181214714864+U*(271321109760+U*(246949079508+U*(152592613904+U*(67641780720+U*(22139948976+U*(5419128276+U*(992047944+U*(134155248+U*(13025848+U*(859860+U*(34584+U*(640)))))))))))))
  let c2 : ℤ := 8539509320+U*(25188341040+U*(33915677650+U*(27585708888+U*(15102436004+U*(5864799944+U*(1656778886+U*(343076312+U*(51683492+U*(5523792+U*(397538+U*(17296+U*(344))))))))))))
  let c3 : ℤ := 472614368+U*(1245893220+U*(1488671344+U*(1064854416+U*(506856272+U*(168612436+U*(40009176+U*(6772528+U*(801544+U*(63172+U*(2984+U*(64)))))))))))
  let c4 : ℤ := 9175887+U*(21161196+U*(21952614+U*(13495932+U*(5446985+U*(1508544+U*(290422+U*(38388+U*(3335+U*(172+U*(4))))))))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by dsimp [c0, c1, c2, c3, c4]; positivity
  have he : -scaledDiscriminant p q (-12) = c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by
    dsimp [scaledDiscriminant, twiceSum, twicePairSum, U, V, c0, c1, c2, c3, c4]
    ring
  rw [←he] at hpos
  exact neg_pos.mp hpos

private theorem discriminant_nonnegative (p q a b c D : ℤ)
    (hL : 2*(a+b+c)=twiceSum p q) (hM : 2*(a*b+a*c+b*c)=twicePairSum p q)
    (hZ : a*b*c=p^4*q+D) :
    0≤scaledDiscriminant p q D := by
  unfold scaledDiscriminant
  dsimp only
  rw [←hL,←hM,←hZ]
  have he :
      16*(2*(a+b+c))^2*(2*(a*b+a*c+b*c))^2-128*(2*(a*b+a*c+b*c))^3-
      128*(2*(a+b+c))^3*(a*b*c)-6912*(a*b*c)^2+
      1152*(2*(a+b+c))*(2*(a*b+a*c+b*c))*(a*b*c) =
      256*(a-b)^2*(a-c)^2*(b-c)^2 := by ring
  rw [he]
  positivity

private theorem second_newton (a b c : ℤ) :
    3*(a+b+c)*(a*b*c)≤(a*b+a*c+b*c)^2 := by
  nlinarith only [sq_nonneg (a*b-a*c),sq_nonneg (a*b-b*c),sq_nonneg (a*c-b*c)]

private theorem no_repeated_base_three (q a b c D : ℤ)
    (hq : 11≤q) (hD : D=12∨D=-12)
    (hL : 2*(a+b+c)=twiceSum 3 q) (hM : 2*(a*b+a*c+b*c)=twicePairSum 3 q)
    (hZ : a*b*c=3^4*q+D) : False := by
  have hn := second_newton a b c
  have hmargin : 0 < 4*(3*(a+b+c)*(a*b*c)-(a*b+a*c+b*c)^2) := by
    have hq2 : 121≤q^2 := by
      have h := mul_nonneg (show 0≤q-11 by omega) (show 0≤q+11 by omega)
      nlinarith only [h]
    have hL' := congrArg (fun x : ℤ => (3^4*q+D)*x) hL
    have hM' := congrArg (fun x : ℤ => x^2) hM
    have he : 4*(3*(a+b+c)*(a*b*c)-(a*b+a*c+b*c)^2) =
        6*twiceSum 3 q*(3^4*q+D)-(twicePairSum 3 q)^2 := by
      rw [hZ]
      linear_combination 6*hL'-hM'
    rw [he]
    dsimp [twicePairSum,twiceSum]
    rcases hD with rfl|rfl <;> nlinarith only [hq,hq2]
  nlinarith only [hn,hmargin]

private theorem no_unrepeated_base_three {p a b c : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hc : c.Prime) (hp : 3≤p)
    (hgap : p^4*3+12=a*b*c ∨ a*b*c+12=p^4*3)
    (hL : 2*(a+b+c)=(p^2+p+1)*(3+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+3-1)+(a+b+c)) : False := by
  have hdiv : 3∣a*b*c := by omega
  simp only [Nat.prime_three.dvd_mul] at hdiv
  have hex {x : ℕ} (hx : x.Prime) (hh : 3∣x) : x=3 := by
    rcases (Nat.dvd_prime hx).mp hh with h|h
    · omega
    · exact h.symm
  have hP : 1≤p+3 := by omega
  have hp2 : 9≤p^2 := Nat.pow_le_pow_left hp 2
  rcases hdiv with (h|h)|h
  · obtain rfl := hex ha h
    zify [hP] at hgap hL hM hp hp2
    rcases hgap with hg|hg <;> nlinarith only [hg,hL,hM,hp,hp2]
  · obtain rfl := hex hb h
    zify [hP] at hgap hL hM hp hp2
    rcases hgap with hg|hg <;> nlinarith only [hg,hL,hM,hp,hp2]
  · obtain rfl := hex hc h
    zify [hP] at hgap hL hM hp hp2
    rcases hgap with hg|hg <;> nlinarith only [hg,hL,hM,hp,hp2]

/-- In addition to its forced p⁴q shape, the quintic endpoint must have q≥11
and the repeated prime strictly larger than 2q. -/
theorem narrowed_odd_squarefree_three_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ p%4=3 ∧ q%8=3 ∧
      11≤q ∧ 2*q<p ∧ m=p^4*q := by
  obtain ⟨p,q,hp,hq,hpq,hp4,hq8,hm'⟩ :=
    remaining_odd_squarefree_three_five hn hm hs ho hgap hφ hσ
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hn'⟩ := squarefree_triple_shape hn hs
  rw [hn',hm'] at hgap hφ hσ
  have hgap' : p^4*q+12=a*b*c ∨ a*b*c+12=p^4*q := hgap.symm
  have ⟨hF,hK⟩ := fourth_times_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas ha hb hc hab hac hbc
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c) := by omega
  have hp3 : 3≤p := by omega
  have hq3 : q≠3 := by
    rintro rfl
    exact no_unrepeated_base_three ha hb hc hp3 hgap' hL hM
  have hq11 : 11≤q := by omega
  let D : ℤ := (a:ℤ)*b*c-(p:ℤ)^4*q
  have hD : D=12∨D=-12 := by zify at hgap'; dsimp [D]; omega
  have hpq1 : 1≤p+q := by omega
  zify [hpq1] at hL hM
  have hL' : 2*((a:ℤ)+b+c)=twiceSum p q := hL
  have hM' : 2*((a:ℤ)*b+(a:ℤ)*c+(b:ℤ)*c)=twicePairSum p q := by
    dsimp [twicePairSum,twiceSum]
    linarith only [hL,hM]
  have hZ : (a:ℤ)*b*c=(p:ℤ)^4*q+D := by dsimp [D]; ring
  have hp' : p≠3 := by
    rintro rfl
    exact no_repeated_base_three q a b c D (by exact_mod_cast hq11) hD hL' hM' hZ
  have hpZ : (4:ℤ)≤p := by
    exact_mod_cast (show 4≤p by omega)
  have hqP : 2*q<p := by
    by_contra! h
    have hqZ : (p:ℤ)≤2*q := by exact_mod_cast h
    have hnn := discriminant_nonnegative p q a b c D hL' hM' hZ
    rcases hD with hd|hd
    · rw [hd] at hnn
      exact (not_lt_of_ge hnn) (negative_cubic_plus p q hpZ hqZ)
    · rw [hd] at hnn
      exact (not_lt_of_ge hnn) (negative_cubic_minus p q hpZ hqZ)
  exact ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,hqP,hm'⟩

private theorem zmod_three_moments :
    ∀ p q a b c : ZMod 3, p≠0 → q≠0 →
      2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 → a*b*c=p^4*q → p≠q := by
  decide

/-- The two prime bases in the remaining p⁴q case also have different
residues modulo three. -/
theorem narrowed_odd_squarefree_three_five_mod_three {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ p%4=3 ∧ q%8=3 ∧
      11≤q ∧ 2*q<p ∧ p%3≠q%3 ∧ m=p^4*q := by
  obtain ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,h2qp,hm'⟩ :=
    narrowed_odd_squarefree_three_five hn hm hs ho hgap hφ hσ
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hn'⟩ := squarefree_triple_shape hn hs
  rw [hn',hm'] at hgap hφ hσ
  have hK := (fourth_times_prime_formulas hp hq hpq).2
  have hK' := (triple_formulas ha hb hc hab hac hbc).2
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hL' := congrArg (fun x : ℕ => (x : ZMod 3)) hL
  push_cast at hL'
  have hZ : (a : ZMod 3)*b*c=(p : ZMod 3)^4*q := by
    have hz : (12 : ZMod 3)=0 := by decide
    rcases hgap with h|h
    · have H := congrArg (fun x : ℕ => (x : ZMod 3)) h
      push_cast at H
      simpa only [hz,add_zero] using H
    · have H := congrArg (fun x : ℕ => (x : ZMod 3)) h
      push_cast at H
      simpa only [hz,add_zero] using H.symm
  have hnonzero {x : ℕ} (hx : x.Prime) (hx' : 3<x) : (x : ZMod 3) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff x 3).mp h
    rcases (Nat.dvd_prime hx).mp hd with hd | hd <;> omega
  have hnon := zmod_three_moments p q a b c (hnonzero hp (by omega))
    (hnonzero hq (by omega)) hL' hZ
  have hmod : p%3≠q%3 := by
    intro h
    apply hnon
    rw [←ZMod.natCast_mod p 3,←ZMod.natCast_mod q 3,h]
  exact ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,h2qp,hmod,hm'⟩

end A056777OddSquarefreeThreeFive

#print axioms A056777OddSquarefreeThreeFive.narrowed_odd_squarefree_three_five

#print axioms A056777OddSquarefreeThreeFive.narrowed_odd_squarefree_three_five_mod_three
