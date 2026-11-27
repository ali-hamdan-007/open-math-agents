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

private theorem five_cubic_negative (p q D : ℤ) (hp : 23≤p) (hq : 11≤q) (hD : -12≤D) :
    250-25*twiceSum p q+5*twicePairSum p q-2*(p^4*q+D) < 0 := by
  let U := p-23
  let V := q-11
  let W := D+12
  have hU : 0≤U := by dsimp [U]; omega
  have hV : 0≤V := by dsimp [V]; omega
  have hW : 0≤W := by dsimp [W]; omega
  let P := 2*U^4*V+12*U^4+174*U^3*V+1044*U^3+5678*U^2*V+34188*U^2+
    82406*U*V+500076*U+449072*V+2760528+2*W
  have hpos : 0<P := by dsimp [P]; positivity
  have he : -(250-25*twiceSum p q+5*twicePairSum p q-2*(p^4*q+D))=P := by
    dsimp [twiceSum,twicePairSum,P,U,V,W]
    ring
  rw [←he] at hpos
  exact neg_pos.mp hpos

private theorem triple_root_not_five (p q a b c D : ℤ)
    (hp : 23≤p) (hq : 11≤q) (hD : -12≤D)
    (hL : 2*(a+b+c)=twiceSum p q) (hM : 2*(a*b+a*c+b*c)=twicePairSum p q)
    (hZ : a*b*c=p^4*q+D) : a≠5 ∧ b≠5 ∧ c≠5 := by
  have he : 250-25*twiceSum p q+5*twicePairSum p q-2*(p^4*q+D) =
      2*(5-a)*(5-b)*(5-c) := by
    rw [←hL,←hM,←hZ]
    ring
  have hneg := five_cubic_negative p q D hp hq hD
  rw [he] at hneg
  refine ⟨?_,?_,?_⟩
  all_goals
    intro h
    rw [h] at hneg
    norm_num at hneg

set_option maxHeartbeats 2000000 in
private theorem zmod_five_minus :
    ∀ p q a b c : ZMod 5, p≠0 → q≠0 → a≠0 → b≠0 → c≠0 →
      2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 →
      2*(a*b+a*c+b*c)=2*p^3*(p+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2 →
      a*b*c=p^4*q-12 → False := by
  decide

set_option maxHeartbeats 2000000 in
private theorem zmod_five_plus :
    ∀ p q a b c : ZMod 5, p≠0 → q≠0 → a≠0 → b≠0 → c≠0 →
      2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 →
      2*(a*b+a*c+b*c)=2*p^3*(p+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2 →
      a*b*c=p^4*q+12 → (p=2 ∨ p=3) ∧ q=2 := by
  decide

private theorem cubic_gap_bound (p q a b c : ℤ) (hp : 2*q<p) (hq : 11≤q)
    (hqa : q+1≠a) (hqb : q+1≠b) (hqc : q+1≠c)
    (hL : 2*(a+b+c)=twiceSum p q) (hM : 2*(a*b+a*c+b*c)=twicePairSum p q)
    (hZ : a*b*c=p^4*q+12) : p^2<q^3 := by
  by_contra! hpow
  have hp23 : 23≤p := by omega
  let f (x : ℤ) := 2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*(p^4*q+12)
  have hfac (x : ℤ) : f x=2*(x-a)*(x-b)*(x-c) := by
    dsimp [f]
    rw [←hL,←hM,←hZ]
    ring
  have hneg : f q<0 := by
    have he : f q= -(p^2+p-1)*(q^3-q)-24 := by dsimp [f,twiceSum,twicePairSum]; ring
    rw [he]
    have hprod := mul_nonneg (show 0≤p^2+p-1 by nlinarith [sq_nonneg p]) (show 0≤q^3-q by
      nlinarith [sq_nonneg q, mul_nonneg (show 0≤q by omega) (show 0≤q^2-1 by nlinarith)])
    linarith
  have hpos : 0<f (q+2) := by
    have he : f (q+2)=4*p^3*(p-q-2)-(p^2+p)*(q^3+4*q^2+5*q+2)+
        (q^3+8*q^2+17*q-14) := by dsimp [f,twiceSum,twicePairSum]; ring
    rw [he]
    have h₁ := mul_le_mul_of_nonneg_left (show 5*p≤12*(p-q-2) by omega)
      (show 0≤p^3 by positivity)
    have h₂ : 2*(q^3+4*q^2+5*q+2)≤3*q^3 := by
      have hh := mul_nonneg (show 0≤q-11 by omega) (show 0≤q^2 by positivity)
      nlinarith [sq_nonneg (q-5)]
    have h₃ := mul_le_mul_of_nonneg_left (h₂.trans (mul_le_mul_of_nonneg_left hpow (by decide)))
      (show 0≤p^2+p by positivity)
    have h₄ := mul_le_mul_of_nonneg_right (show 12*(p^2+p)≤13*p^2 by
      nlinarith [mul_nonneg (show 0≤p by omega) (show 0≤p-12 by omega)])
      (show 0≤3*p^2 by positivity)
    have h₅ : 0<p^4 := by positivity
    have h₆ : 0≤q^3+8*q^2+17*q-14 := by
      have : 0≤q^3 := by positivity
      nlinarith
    nlinarith only [h₁,h₃,h₄,h₅,h₆]
  let s (x y : ℤ) : ℤ := if x<y then -1 else 1
  have hs0 (x y : ℤ) (hxy : x≠y) : 0<s x y*(x-y) := by
    unfold s
    split <;> omega
  have hs1 (y : ℤ) (hy : q≠y) (hy' : q+1≠y) (hy'' : q+2≠y) :
      s q y=s (q+2) y := by
    unfold s
    by_cases h : q<y
    · have h' : q+2<y := by omega
      simp [h,h']
    · have h' : ¬q+2<y := by omega
      simp [h,h']
  rw [hfac] at hneg hpos
  have hn₁ : q≠a ∧ q≠b ∧ q≠c := by
    refine ⟨?_,?_,?_⟩ <;> intro h <;> rw [←h] at hneg <;> norm_num at hneg
  have hn₂ : q+2≠a ∧ q+2≠b ∧ q+2≠c := by
    refine ⟨?_,?_,?_⟩ <;> intro h <;> rw [←h] at hpos <;> norm_num at hpos
  have t₁ := mul_pos (mul_pos (hs0 q a hn₁.1) (hs0 q b hn₁.2.1)) (hs0 q c hn₁.2.2)
  have t₂ := mul_pos (mul_pos (hs0 (q+2) a hn₂.1) (hs0 (q+2) b hn₂.2.1))
    (hs0 (q+2) c hn₂.2.2)
  rw [←hs1 a hn₁.1 hqa hn₂.1,←hs1 b hn₁.2.1 hqb hn₂.2.1,←hs1 c hn₁.2.2 hqc hn₂.2.2] at t₂
  have e (x : ℤ) : (s q a*(x-a))*(s q b*(x-b))*(s q c*(x-c)) =
      (s q a*s q b*s q c)*((x-a)*(x-b)*(x-c)) := by ring
  rw [e] at t₁ t₂
  have hz₁ : (q-a)*(q-b)*(q-c)<0 := by linarith
  have hz₂ : 0<(q+2-a)*(q+2-b)*(q+2-c) := by linarith
  have hv := pos_of_mul_pos_left t₂ hz₂.le
  have := mul_neg_of_pos_of_neg hv hz₁
  exact (not_lt_of_ge t₁.le this)

set_option maxHeartbeats 1200000 in
/-- The squarefree triple can only be the larger endpoint in the remaining odd
p⁴q case. The two prime bases also satisfy the displayed residues modulo five. -/
theorem odd_squarefree_three_five_orientation_mod_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    m+12=n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧
      p%4=3 ∧ q%8=3 ∧ 11≤q ∧ 2*q<p ∧ p%3≠q%3 ∧ p^2<q^3 ∧
      (p%5=2 ∨ p%5=3) ∧ q%5=2 ∧ m=p^4*q := by
  obtain ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,h2q,hpq3,hm'⟩ :=
    narrowed_odd_squarefree_three_five_mod_three hn hm hs ho hgap hφ hσ
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hn'⟩ := squarefree_triple_shape hn hs
  have hg := hgap
  rw [hn',hm'] at hg hφ hσ
  have ⟨hF,hK⟩ := fourth_times_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas ha hb hc hab hac hbc
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hP : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c) := by omega
  have hpq1 : 1≤p+q := by omega
  let D : ℤ := (a:ℤ)*b*c-(p:ℤ)^4*q
  have hD : -12≤D := by
    zify at hg
    dsimp [D]
    omega
  have hz : (a:ℤ)*b*c=(p:ℤ)^4*q+D := by dsimp [D]; ring
  have hp23 : (23:ℤ)≤p := by exact_mod_cast (show 23≤p by omega)
  have hq11' : (11:ℤ)≤q := by exact_mod_cast hq11
  have hLZ := hL
  have hPZ := hP
  zify [hpq1] at hLZ hPZ
  have hMZ : 2*((a:ℤ)*b+(a:ℤ)*c+(b:ℤ)*c)=twicePairSum p q := by
    dsimp [twicePairSum,twiceSum]
    linarith only [hLZ,hPZ]
  obtain ⟨ha5,hb5,hc5⟩ := triple_root_not_five p q a b c D hp23 hq11' hD hLZ hMZ hz
  have nozero {x : ℕ} (hx : x.Prime) (hx5 : x≠5) : (x:ZMod 5)≠0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff x 5).mp he
    rcases (Nat.dvd_prime hx).mp hd with hd|hd <;> omega
  have hp0 := nozero hp (by omega)
  have hq0 := nozero hq (by omega)
  have ha0 := nozero ha (fun h => ha5 (by exact_mod_cast h))
  have hb0 := nozero hb (fun h => hb5 (by exact_mod_cast h))
  have hc0 := nozero hc (fun h => hc5 (by exact_mod_cast h))
  have hL5 := congrArg (fun x : ℕ => (x : ZMod 5)) hL
  push_cast at hL5
  have hM5 := congrArg (fun x : ℤ => (x : ZMod 5)) hMZ
  simp only [twicePairSum,twiceSum] at hM5
  push_cast at hM5
  rcases hgap with h|h
  · have hg' : a*b*c+12=p^4*q := by simpa only [hn',hm'] using h
    have H := congrArg (fun x : ℕ => (x:ZMod 5)) hg'
    push_cast at H
    have hZ5 : (a:ZMod 5)*b*c=(p:ZMod 5)^4*q-12 := eq_sub_of_add_eq H
    exact (zmod_five_minus p q a b c hp0 hq0 ha0 hb0 hc0 hL5 hM5 hZ5).elim
  · have hg' : p^4*q+12=a*b*c := by simpa only [hn',hm'] using h
    have H := congrArg (fun x : ℕ => (x:ZMod 5)) hg'
    push_cast at H
    have hpqZ := zmod_five_plus p q a b c hp0 hq0 ha0 hb0 hc0 hL5 hM5 H.symm
    have htwo : (2:ZMod 5).val=2 := by decide
    have hthree : (3:ZMod 5).val=3 := by decide
    have hq5 : q%5=2 := by
      have hv := congrArg ZMod.val hpqZ.2
      simpa only [ZMod.val_natCast,htwo,hthree] using hv
    have hp5 : p%5=2 ∨ p%5=3 := by
      rcases hpqZ.1 with h|h
      · left
        have hv := congrArg ZMod.val h
        simpa only [ZMod.val_natCast,htwo,hthree] using hv
      · right
        have hv := congrArg ZMod.val h
        simpa only [ZMod.val_natCast,htwo,hthree] using hv
    have rootne {x : ℕ} (hx : x∣n) : (q:ℤ)+1≠x := by
      obtain ⟨y,hy⟩ := hx
      intro heq
      have heq' : q+1=x := by exact_mod_cast heq
      have hxodd := Nat.odd_iff.mp (Nat.odd_mul.mp (hy ▸ ho)).1
      omega
    have hda : a∣n := by rw [hn']; exact ⟨b*c, by ring⟩
    have hdb : b∣n := by rw [hn']; exact ⟨a*c, by ring⟩
    have hdc : c∣n := by rw [hn']; exact ⟨a*b, by ring⟩
    have hzplus : (a:ℤ)*b*c=(p:ℤ)^4*q+12 := by exact_mod_cast hg'.symm
    have hbound := cubic_gap_bound p q a b c (by exact_mod_cast h2q) hq11'
      (rootne hda) (rootne hdb) (rootne hdc) hLZ hMZ hzplus
    exact ⟨h,p,q,hp,hq,hpq,hp4,hq8,hq11,h2q,hpq3,by exact_mod_cast hbound,hp5,hq5,hm'⟩

set_option maxHeartbeats 1800000 in
private theorem negative_sharp_discriminant (p q : ℤ) (hp : 23≤p) (hq : 29*p≤70*q) :
    scaledDiscriminant p q 12 < 0 := by
  let U := p-23
  let V := 70*q-29*p
  have hU : 0≤U := by dsimp [U]; omega
  have hV : 0≤V := by dsimp [V]; omega
  let c0 : ℤ := 2403716796067445186686389360+U*(1372459527095887592479466496+U*(361628144733141041153285376+U*(58222985448896711891716608+U*(6390878780772289890372672+U*(505065819550972484165760+U*(29568278933414371856160+U*(1298512064396999209536+U*(42785955404740676160+U*(1045114907226283008+U*(18409103874792896+U*(221824252323584+U*(1647405171312+U*(5838639040+U*(1827904))))))))))))))
  let c1 : ℤ := 197280657948445250404317120+U*(110903391225402830723172672+U*(28772082605849105526280128+U*(4561165586053861675076160+U*(492954098940766485290304+U*(38355423730864527114432+U*(2210396180511519262656+U*(95528104701881499840+U*(3096061219965103680+U*(74320710890708416+U*(1284393199856320+U*(15132464586048+U*(108942182528+U*(361946624)))))))))))))
  let c2 : ℤ := 146731586148712503419040+U*(76011019035194702499264+U*(18045738264251846831328+U*(2596284058024279753344+U*(252113798427792625440+U*(17407694618644958784+U*(876345106837510944+U*(32409895802685312+U*(873914076692576+U*(16755554494400+U*(216827234080+U*(1700379136+U*(6111104))))))))))))
  let c3 : ℤ := 36507580065752402880+U*(17288993510411446208+U*(3721481303182344320+U*(480612921522981248+U*(41377674101069504+U*(2493544352928960+U*(107330336015488+U*(3299759547648+U*(71010508736+U*(1018718528+U*(8768384+U*(34304)))))))))))
  let c4 : ℤ := 3027038472181360+U*(1298417823121216+U*(250638775757408+U*(28672378598720+U*(2152656064528+U*(110829558784+U*(3962794848+U*(97167040+U*(1563632+U*(14912+U*(64))))))))))
  let C := c0 + V*(c1+V*(c2+V*(c3+V*c4)))
  have hpos : 0<C := by
    dsimp [C,c0,c1,c2,c3,c4]
    positivity
  have he : -(70:ℤ)^4 * scaledDiscriminant p q 12 = C := by
    dsimp [scaledDiscriminant,twiceSum,twicePairSum,U,V,C,c0,c1,c2,c3,c4]
    ring
  have hprod : 0 < -(70:ℤ)^4 * scaledDiscriminant p q 12 := he ▸ hpos
  exact neg_pos.mp (show -scaledDiscriminant p q 12 > 0 by nlinarith only [hprod])

private theorem cubic_linear_positive (p q : ℤ) (hp : 2*q<p) (hq : 11≤q) :
    2*twiceSum p q*q < twicePairSum p q := by
  let U := p-(2*q+1)
  let V := q-11
  have hU : 0≤U := by dsimp [U]; omega
  have hV : 0≤V := by dsimp [V]; omega
  let C := 2*U^4 + 14*U^3*V + 162*U^3 + 34*U^2*V^2 + 789*U^2*V +
    4578*U^2 + 32*U*V^3 + 1118*U*V^2 + 13023*U*V + 50578*U +
    8*V^4 + 376*V^3 + 6628*V^2 + 51937*V + 152650
  have hpos : 0<C := by
    dsimp [C]
    positivity
  have he : twicePairSum p q-2*twiceSum p q*q=C := by
    dsimp [twicePairSum,twiceSum,C,U,V]
    ring
  omega

private theorem cubic_root_gt_q (p q x : ℤ) (hp : 2*q<p) (hq : 11≤q) (hx : 0≤x)
    (hroot : 2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*(p^4*q+12)=0) :
    q<x := by
  by_contra! hxq
  let f (z : ℤ) := 2*z^3-twiceSum p q*z^2+twicePairSum p q*z-2*(p^4*q+12)
  have hL : 0≤twiceSum p q := by
    have hp0 : 0≤p := by omega
    have hq0 : 0≤q := by omega
    dsimp [twiceSum]
    positivity
  have hM := cubic_linear_positive p q hp hq
  have hdiff : f q-f x=(q-x)*(2*(q^2+q*x+x^2)+twicePairSum p q-twiceSum p q*(q+x)) := by
    dsimp [f]
    ring
  have hprod : 0≤twiceSum p q*(q-x) := mul_nonneg hL (by omega)
  have hqx : 0≤q*x := mul_nonneg (by omega) hx
  have hinner : 0≤2*(q^2+q*x+x^2)+twicePairSum p q-twiceSum p q*(q+x) := by
    nlinarith only [hprod,hqx,hM,sq_nonneg q,sq_nonneg x]
  have hnon := mul_nonneg (show 0≤q-x by omega) hinner
  have hqeval : f q= -(p^2+p-1)*(q^3-q)-24 := by dsimp [f,twicePairSum,twiceSum]; ring
  have hprod' := mul_nonneg (show 0≤p^2+p-1 by nlinarith [sq_nonneg p]) (show 0≤q^3-q by
    nlinarith [sq_nonneg q, mul_nonneg (show 0≤q by omega) (show 0≤q^2-1 by nlinarith)])
  change f x=0 at hroot
  nlinarith only [hroot,hqeval,hdiff,hnon,hprod']

/-- In the remaining odd case the repeated prime exceeds 70/29 times the
other prime, and every prime factor of the squarefree endpoint exceeds that other prime. -/
theorem odd_squarefree_three_five_sharp_root_bounds {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    m+12=n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧
      p%4=3 ∧ q%8=3 ∧ 11≤q ∧ 70*q<29*p ∧ p%3≠q%3 ∧ p^2<q^3 ∧
      (p%5=2 ∨ p%5=3) ∧ q%5=2 ∧ m=p^4*q ∧
      ∀ x : ℕ, x.Prime → x∣n → q<x := by
  obtain ⟨hg,p,q,hp,hq,hpq,hp4,hq8,hq11,h2q,hpq3,hpqBound,hp5,hq5,hm'⟩ :=
    odd_squarefree_three_five_orientation_mod_five hn hm hs ho hgap hφ hσ
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hn'⟩ := squarefree_triple_shape hn hs
  rw [hn',hm'] at hg hφ hσ
  have ⟨hF,hK⟩ := fourth_times_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas ha hb hc hab hac hbc
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hP : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c) := by omega
  have hpq1 : 1≤p+q := by omega
  zify [hpq1] at hL hP
  have hM : 2*((a:ℤ)*b+(a:ℤ)*c+(b:ℤ)*c)=twicePairSum p q := by
    dsimp [twicePairSum,twiceSum]
    linarith only [hL,hP]
  have hZ : (a:ℤ)*b*c=(p:ℤ)^4*q+12 := by exact_mod_cast hg.symm
  have hdisc := discriminant_nonnegative p q a b c 12 hL hM hZ
  have hp23 : (23:ℤ)≤p := by exact_mod_cast (show 23≤p by omega)
  have hratio : 70*q<29*p := by
    by_contra! h
    exact (not_lt_of_ge hdisc) (negative_sharp_discriminant p q hp23 (by exact_mod_cast h))
  change 2*((a:ℤ)+b+c)=twiceSum p q at hL
  have hfactor (x : ℤ) :
      2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*((p:ℤ)^4*q+12) =
        2*(x-a)*(x-b)*(x-c) := by
    rw [←hL,←hM,←hZ]
    ring
  refine ⟨by simpa only [hm',hn'] using hg,p,q,hp,hq,hpq,hp4,hq8,hq11,hratio,hpq3,hpqBound,hp5,hq5,hm',?_⟩
  intro x hx hxn
  rw [hn'] at hxn
  rcases hx.dvd_mul.mp hxn with h|h
  · rcases hx.dvd_mul.mp h with h|h
    · have hxa : x=a := (Nat.dvd_prime ha).mp h |>.resolve_left hx.ne_one
      subst x
      exact_mod_cast (cubic_root_gt_q p q a (by exact_mod_cast h2q) (by exact_mod_cast hq11)
        (Int.natCast_nonneg a) (by rw [hfactor]; ring))
    · have hxb : x=b := (Nat.dvd_prime hb).mp h |>.resolve_left hx.ne_one
      subst x
      exact_mod_cast (cubic_root_gt_q p q b (by exact_mod_cast h2q) (by exact_mod_cast hq11)
        (Int.natCast_nonneg b) (by rw [hfactor]; ring))
  · have hxc : x=c := (Nat.dvd_prime hc).mp h |>.resolve_left hx.ne_one
    subst x
    exact_mod_cast (cubic_root_gt_q p q c (by exact_mod_cast h2q) (by exact_mod_cast hq11)
      (Int.natCast_nonneg c) (by rw [hfactor]; ring))

set_option maxHeartbeats 2000000 in
/-- The three integer roots satisfy a product identity independent of the
unrepeated prime parameter q. Each quadratic value consequently divides the
fixed degree-sixteen expression in p. -/
theorem cubic_root_quadratic_product (p q a b c : ℤ)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    let T (x : ℤ) := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
    T a*T b*T c=2*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
      29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72) := by
  let h := p^2+p+1
  let j := -(2*p^3+p^2+p+1)
  let k := 2*p^4
  let E (L M Z : ℤ) :=
    8*h^3*Z^2+4*h^2*j*M*Z+2*h^2*k*M^2+2*h*j*k*L*M+
      2*h*k^2*L^2+4*j*k^2*L+8*k^3+4*L*Z*(-2*h^2*k+h*j^2)+
      4*M*(-2*h*k^2+j^2*k)+8*Z*(-3*h*j*k+j^3)
  let T (x : ℤ) := h*x^2-(2*p^3+p^2+p+1)*x+k
  have he : 8*(T a*T b*T c)=E (2*(a+b+c)) (2*(a*b+a*c+b*c)) (a*b*c) := by
    dsimp [E,T,j]
    ring
  have hL' : 2*(a+b+c)=twiceSum p q := hL
  have hM' : 2*(a*b+a*c+b*c)=twicePairSum p q := by
    dsimp [twicePairSum]
    nlinarith only [hM,hL']
  rw [hL',hM',hZ] at he
  have he' : E (twiceSum p q) (twicePairSum p q) (p^4*q+12) =
      16*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
      29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72) := by
    dsimp [E,h,j,k,twiceSum,twicePairSum]
    ring
  rw [he'] at he
  change T a*T b*T c=_
  linarith only [he]

/-- For a fixed repeated prime and a root, the positive quadratic coefficient
allows reconstruction of the other prime by a single exact division. -/
theorem cubic_root_recovers_unrepeated_prime (p q x : ℤ) (hp : 3≤p)
    (hx : 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
      (2*p^3*(p+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2)*x
      -2*(p^4*q+12)=0) :
    let T := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
    0<T ∧ q*T=2*x^3-(p^2+p+1+2*p^3)*x^2+(2*p^4+p^2+p-1)*x-24 := by
  let T := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
  let u := p-3
  have hu : 0≤u := by dsimp [u]; omega
  let C := 4*u^6+76*u^5+603*u^4+2550*u^3+6045*u^2+7594*u+3935
  have hc : 0<C := by dsimp [C]; positivity
  have he : 4*(p^2+p+1)*T=(2*(p^2+p+1)*x-(2*p^3+p^2+p+1))^2+C := by
    dsimp [T,C,u]
    ring
  have hprod : 0<4*(p^2+p+1)*T := by
    rw [he]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hc
  have hp0 : 0≤p := by omega
  refine ⟨pos_of_mul_pos_right hprod (by positivity),?_⟩
  linear_combination -hx

/-- At least one of the roots lies strictly between q and p. Its quadratic
value is a positive divisor of a polynomial in p and determines q exactly. -/
theorem cubic_root_reconstruction_candidate (p q a b c : ℤ)
    (hq : 11≤q) (hp : 2*q<p) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    let T (x : ℤ) := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
    ∃ x : ℤ, q<x ∧ x<p ∧ (x=a ∨ x=b ∨ x=c) ∧ 0<T x ∧
      q*T x=2*x^3-(p^2+p+1+2*p^3)*x^2+(2*p^4+p^2+p-1)*x-24 ∧
      T x∣2*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
        29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72) := by
  have hp3 : 3≤p := by omega
  have hq0 : 0≤q := by omega
  have hp0 : 0≤p := by omega
  have hL' : 2*(a+b+c)=twiceSum p q := hL
  have hM' : 2*(a*b+a*c+b*c)=twicePairSum p q := by
    dsimp [twicePairSum]
    nlinarith only [hL',hM]
  have hpos : 0<2*p*twiceSum p q-twicePairSum p q-6*p^2 := by
    have he : 2*p*twiceSum p q-twicePairSum p q-6*p^2 =
        (p^2+p-1)*q+p^2*(2*p^2-5)+2*p^3+p+1 := by
      dsimp [twiceSum,twicePairSum]
      ring
    rw [he]
    have h₁ := mul_nonneg (show 0≤p^2+p-1 by nlinarith [sq_nonneg p]) hq0
    have h₂ := mul_nonneg (sq_nonneg p) (show 0≤2*p^2-5 by
      nlinarith [mul_nonneg (show 0≤p-3 by omega) (show 0≤p+3 by omega)])
    have h₃ : 0≤p^3 := by positivity
    nlinarith only [h₁,h₂,h₃,hp3]
  have hsmall : a<p ∨ b<p ∨ c<p := by
    by_contra! h
    obtain ⟨hpa,hpb,hpc⟩ := h
    have h₁ := mul_nonneg (show 0≤a-p by omega) (show 0≤b-p by omega)
    have h₂ := mul_nonneg (show 0≤a-p by omega) (show 0≤c-p by omega)
    have h₃ := mul_nonneg (show 0≤b-p by omega) (show 0≤c-p by omega)
    have hsum := congrArg (fun y : ℤ => 2*p*y) hL'
    nlinarith only [hpos,h₁,h₂,h₃,hsum,hM']
  let T (x : ℤ) := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
  let P := 2*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
    29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72)
  have hprod : T a*T b*T c=P := cubic_root_quadratic_product p q a b c hL hM hZ
  have root (x : ℤ) (hx : x=a ∨ x=b ∨ x=c) :
      2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*(p^4*q+12)=0 := by
    rw [←hL',←hM',←hZ]
    rcases hx with rfl|rfl|rfl <;> ring
  have exhibit (x : ℤ) (hx : 0≤x) (hxp : x<p) (hr : x=a ∨ x=b ∨ x=c)
      (hd : T x∣P) :
      ∃ y : ℤ, q<y ∧ y<p ∧ (y=a ∨ y=b ∨ y=c) ∧ 0<T y ∧
        q*T y=2*y^3-(p^2+p+1+2*p^3)*y^2+(2*p^4+p^2+p-1)*y-24 ∧ T y∣P := by
    obtain ⟨ht,hqT⟩ := cubic_root_recovers_unrepeated_prime p q x hp3 (root x hr)
    exact ⟨x,cubic_root_gt_q p q x hp hq hx (root x hr),hxp,hr,ht,hqT,hd⟩
  change ∃ x : ℤ, q<x ∧ x<p ∧ (x=a ∨ x=b ∨ x=c) ∧ 0<T x ∧
    q*T x=2*x^3-(p^2+p+1+2*p^3)*x^2+(2*p^4+p^2+p-1)*x-24 ∧ T x∣P
  rcases hsmall with h|h|h
  · exact exhibit a ha h (Or.inl rfl) ⟨T b*T c,by rw [←hprod]; ring⟩
  · exact exhibit b hb h (Or.inr (Or.inl rfl)) ⟨T a*T c,by rw [←hprod]; ring⟩
  · exact exhibit c hc h (Or.inr (Or.inr rfl)) ⟨T a*T b,by rw [←hprod]; ring⟩

/-- For sufficiently large q, the consecutive-odd-root interval improves
the cubic bound to 3p² < q³. -/
theorem cubic_gap_bound_three (p q a b c : ℤ) (hp : 2*q<p) (hq : 107≤q)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hqa : q+1≠a) (hqb : q+1≠b) (hqc : q+1≠c)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    3*p^2<q^3 := by
  by_contra! hpow
  have hq0 : 0≤q := by omega
  have hp0 : 0<p := by omega
  have h5 : 5*q≤p := by
    by_contra! he
    have H := mul_pos (show 0<5*q-p by omega) (show 0<5*q+p by omega)
    have J := mul_nonneg (sq_nonneg q) (show 0≤q-75 by omega)
    have K : 3*p^2<q^3 := by nlinarith only [H,J]
    linarith only [hpow,K]
  have hp100 : 100≤p := by omega
  have hL' : 2*(a+b+c)=twiceSum p q := hL
  have hM' : 2*(a*b+a*c+b*c)=twicePairSum p q := by
    dsimp [twicePairSum]
    nlinarith only [hL',hM]
  let f (x : ℤ) := 2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*(p^4*q+12)
  have hfactor (x : ℤ) : f x=2*(x-a)*(x-b)*(x-c) := by
    dsimp [f]
    rw [←hL',←hM',←hZ]
    ring
  have hpos : 0<f (q+2) := by
    have he : f (q+2)=4*p^3*(p-q-2)-(p^2+p)*(q^3+4*q^2+5*q+2)+
        (q^3+8*q^2+17*q-14) := by dsimp [f,twiceSum,twicePairSum]; ring
    rw [he]
    have h₁ := mul_le_mul_of_nonneg_left (show 19*p≤24*(p-q-2) by omega)
      (show 0≤p^3 by positivity)
    have h₂ : 24*(q^3+4*q^2+5*q+2)≤25*q^3 := by
      let v := q-107
      have hv : 0≤v := by dsimp [v]; omega
      have E : 25*q^3-24*(q^3+4*q^2+5*q+2)=v^3+225*v^2+13683*v+113051 := by
        dsimp [v]
        ring
      have H : 0≤v^3+225*v^2+13683*v+113051 := by positivity
      omega
    have h₃ := mul_le_mul_of_nonneg_left (h₂.trans (mul_le_mul_of_nonneg_left hpow (by decide)))
      (show 0≤p^2+p by positivity)
    have h₄ := mul_le_mul_of_nonneg_right (show 100*(p^2+p)≤101*p^2 by
      nlinarith [mul_nonneg hp0.le (show 0≤p-100 by omega)])
      (show 0≤75*p^2 by positivity)
    have h₅ : 0<p^4 := by positivity
    have h₆ : 0≤q^3+8*q^2+17*q-14 := by
      have : 0≤q^3 := by positivity
      nlinarith
    nlinarith only [h₁,h₃,h₄,h₅,h₆]
  have hA : f a=0 := by rw [hfactor]; ring
  have hB : f b=0 := by rw [hfactor]; ring
  have hC : f c=0 := by rw [hfactor]; ring
  have h₁ := cubic_root_gt_q p q a hp (by omega) ha hA
  have h₂ := cubic_root_gt_q p q b hp (by omega) hb hB
  have h₃ := cubic_root_gt_q p q c hp (by omega) hc hC
  have hA' : q+2≠a := by
    intro h
    rw [h,hA] at hpos
    exact (lt_irrefl _ hpos)
  have hB' : q+2≠b := by
    intro h
    rw [h,hB] at hpos
    exact (lt_irrefl _ hpos)
  have hC' : q+2≠c := by
    intro h
    rw [h,hC] at hpos
    exact (lt_irrefl _ hpos)
  rw [hfactor] at hpos
  have hprod := mul_neg_of_pos_of_neg
    (mul_pos_of_neg_of_neg (show q+2-a<0 by omega) (show q+2-b<0 by omega))
    (show q+2-c<0 by omega)
  nlinarith only [hpos,hprod]

end A056777OddSquarefreeThreeFive

#print axioms A056777OddSquarefreeThreeFive.narrowed_odd_squarefree_three_five

#print axioms A056777OddSquarefreeThreeFive.narrowed_odd_squarefree_three_five_mod_three

#print axioms A056777OddSquarefreeThreeFive.odd_squarefree_three_five_orientation_mod_five

#print axioms A056777OddSquarefreeThreeFive.odd_squarefree_three_five_sharp_root_bounds

#print axioms A056777OddSquarefreeThreeFive.cubic_root_quadratic_product

#print axioms A056777OddSquarefreeThreeFive.cubic_root_recovers_unrepeated_prime

#print axioms A056777OddSquarefreeThreeFive.cubic_root_reconstruction_candidate

#print axioms A056777OddSquarefreeThreeFive.cubic_gap_bound_three
