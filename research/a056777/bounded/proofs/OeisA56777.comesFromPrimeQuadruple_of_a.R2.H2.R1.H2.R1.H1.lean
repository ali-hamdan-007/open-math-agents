import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1

/-! Bounded prime-root divisor case. The stored integer brackets and coverage are
replayed by Lean's kernel. -/

namespace A056777Bounded


def cubic (L M C x : ℤ) : ℤ := ((2*x-L)*x+M)*x-C

def slope (L M x y : ℤ) : ℤ := 2*(x*x+x*y+y*y)-L*(x+y)+M

theorem cubic_diff (L M C x y : ℤ) :
    cubic L M C y - cubic L M C x = (y-x)*slope L M x y := by
  unfold cubic slope
  ring

theorem slope_antitone {L M P u v u' v' : ℤ}
    (hL : 6*P ≤ L) (hu : u ≤ u') (hv : v ≤ v') (hu' : u' ≤ P) (hv' : v' ≤ P) :
    slope L M u' v' ≤ slope L M u v := by
  have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu)
    (show 2*(u'+u+v)-L ≤ 0 by linarith)
  have h₂ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv)
    (show 2*(u'+v'+v)-L ≤ 0 by linarith)
  unfold slope
  nlinarith only [h₁,h₂]

theorem no_root_between {L M C P a b x : ℤ} (hL : 6*P ≤ L) (hab : a+1 ≤ b)
    (hb : b+1 ≤ P) (hx : x ≤ P)
    (hfa : cubic L M C a < 0) (hfa' : 0 < cubic L M C (a+1))
    (hfb : 0 < cubic L M C b) (hfb' : cubic L M C (b+1) < 0) :
    cubic L M C x ≠ 0 := by
  have ha' : a+1 ≤ P := by omega
  have hbp : b ≤ P := by omega
  have leftSlope : 0 ≤ slope L M a (a+1) := by linarith [cubic_diff L M C a (a+1)]
  have rightSlope : slope L M b (b+1) ≤ 0 := by linarith [cubic_diff L M C b (b+1)]
  by_cases hxa : x ≤ a
  · have h := slope_antitone (M:=M) hL hxa (show a ≤ a+1 by omega) (by omega) ha'
    have hmul := mul_nonneg (show 0 ≤ a-x by omega) (leftSlope.trans h)
    linarith [cubic_diff L M C x a]
  by_cases hxb : b+1 ≤ x
  · have h := slope_antitone (M:=M) hL (show b ≤ b+1 by omega) hxb hb hx
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x-(b+1) by omega) (h.trans rightSlope)
    linarith [cubic_diff L M C (b+1) x]
  have hax : a+1 ≤ x := by omega
  have hxb' : x ≤ b := by omega
  by_cases hsign : 0 ≤ slope L M (a+1) x
  · have hmul := mul_nonneg (show 0 ≤ x-(a+1) by omega) hsign
    linarith [cubic_diff L M C (a+1) x]
  · have h := slope_antitone (M:=M) hL hax hxb' hx hbp
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ b-x by omega)
      (h.trans (le_of_lt (lt_of_not_ge hsign)))
    linarith [cubic_diff L M C x b]

theorem no_root_below_peak {L M C P a x : ℤ} (hL : 6*P ≤ L)
    (ha : a+1 ≤ P) (hx : x ≤ P)
    (hfa : cubic L M C a < 0) (hleft : 0 ≤ slope L M (a-1) a)
    (hright : slope L M a (a+1) ≤ 0) : cubic L M C x ≠ 0 := by
  obtain hxa|rfl|hax := lt_trichotomy x a
  · have h := slope_antitone (M:=M) hL (show x ≤ a-1 by omega) (le_refl a)
        (by omega) (by omega)
    have hmul := mul_nonneg (show 0 ≤ a-x by omega) (hleft.trans h)
    linarith [cubic_diff L M C x a]
  · exact ne_of_lt hfa
  · have h := slope_antitone (M:=M) hL (le_refl a) (show a+1 ≤ x by omega) (by omega) hx
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x-a by omega) (h.trans hright)
    linarith [cubic_diff L M C a x]

def sumCoeff (p q : ℤ) : ℤ := (p*p+p+1)*(q+1)+2*p^3

def pairCoeff (p q : ℤ) : ℤ := 2*p^3*(p+q-1)+sumCoeff p q-2

def productCoeff (p q : ℤ) : ℤ := 2*(p^4*q+12)



/-- Filtering multiples of these constants reduces the kernel replay cost.
Soundness only needs every constant to be greater than one. -/
def divisors : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]

def possiblePrime (p : ℕ) : Bool :=
  divisors.all fun d => decide (p ≤ d ∨ p % d ≠ 0)

theorem prime_possiblePrime {p : ℕ} (hp : p.Prime) : possiblePrime p = true := by
  apply List.all_eq_true.mpr
  intro d hd
  have h1 : 1 < d := by
    change d ∈ divisors at hd
    unfold divisors at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  apply decide_eq_true
  by_contra! h
  have hdvd : d ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h.2
  rcases hp.eq_one_or_self_of_dvd d hdvd with hbad|hbad <;> omega

def qFromIndex (i : ℕ) : ℕ := 40*i+27

theorem q_index_eq {q : ℕ} (h8 : q%8=3) (h5 : q%5=2) :
    qFromIndex (q/40)=q := by
  have hmod8 : (q%40)%8=q%8 := Nat.mod_mod_of_dvd q (by decide)
  have hmod5 : (q%40)%5=q%5 := Nat.mod_mod_of_dvd q (by decide)
  unfold qFromIndex
  omega

theorem p_mod_twenty {p : ℕ} (h4 : p%4=3) (h5 : p%5=2 ∨ p%5=3) :
    p%20=3 ∨ p%20=7 := by
  have hmod4 : (p%20)%4=p%4 := Nat.mod_mod_of_dvd p (by decide)
  have hmod5 : (p%20)%5=p%5 := Nat.mod_mod_of_dvd p (by decide)
  omega

-- Every index is less than 2^18. A zero upper field represents a negative peak.
def signCertificate (p q data : ℕ) : Bool :=
  let L := sumCoeff p q
  let M := pairCoeff p q
  let C := productCoeff p q
  let a : ℤ := (data % 262144 : ℕ)
  let high := data / 262144
  decide (6*(p:ℤ) ≤ L) &&
    if high = 0 then
      decide (a+1 ≤ p ∧ cubic L M C a < 0 ∧
        0 ≤ slope L M (a-1) a ∧ slope L M a (a+1) ≤ 0)
    else
      let b : ℤ := high
      decide (a+1 ≤ b ∧ b+1 ≤ p ∧ cubic L M C a < 0 ∧ 0 < cubic L M C (a+1) ∧
        0 < cubic L M C b ∧ cubic L M C (b+1) < 0)

theorem signCertificate_sound {p q x data : ℕ} (hc : signCertificate p q data = true)
    (hx : x ≤ p) : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x ≠ 0 := by
  unfold signCertificate at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hL,hc⟩ := hc
  have hxp : (x:ℤ) ≤ (p:ℤ) := by exact_mod_cast hx
  split at hc
  next _ =>
    simp only [decide_eq_true_eq] at hc
    exact no_root_below_peak hL hc.1 hxp hc.2.1 hc.2.2.1 hc.2.2.2
  next _ =>
    simp only [decide_eq_true_eq] at hc
    exact no_root_between hL hc.1 hc.2.1 hxp hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2

def candidateP (q p : ℕ) : Bool :=
  decide (2*q < p ∧ p*p < q^3 ∧ p%3 ≠ q%3) && possiblePrime p

def candidateList (q low count : ℕ) : List ℕ :=
  ((List.range count).flatMap fun i =>
    [20*(low+i)+3,20*(low+i)+7]).filter (candidateP q)

theorem candidateP_mem {p q lo c : ℕ} (hp : p.Prime)
    (hpLo : 2*q < p) (hpHi : p^2 < q^3) (hmod : p%3 ≠ q%3) (hmod20 : p%20=3 ∨ p%20=7)
    (hlo : lo ≤ p/20) (hhi : p/20 < lo+c) : p ∈ candidateList q lo c := by
  unfold candidateList
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨p/20-lo, List.mem_range.mpr (by omega), ?_⟩
    obtain h3|h7 := hmod20
    · have he : 20*(lo+(p/20-lo))+3=p := by omega
      simp [he]
    · have he : 20*(lo+(p/20-lo))+7=p := by omega
      simp [he]
  · unfold candidateP
    simp only [Bool.and_eq_true]
    exact ⟨decide_eq_true ⟨hpLo,by simpa only [pow_two] using hpHi,hmod⟩,
      prime_possiblePrime hp⟩

theorem bounded_of_signCertificates
    (checks : ∀ p q : ℕ, p.Prime → q.Prime → q<4000 → q%8=3 → q%5=2 →
      p%4=3 → (p%5=2 ∨ p%5=3) → 2*q<p → p^2<q^3 → p%3≠q%3 →
      ∃ d, signCertificate p q d = true) :
    OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H1 := by
  intro p q x hp hq _ hp4 hq8 _ hpLo hmod hpHi hp5 hq5 hqMax _ _ hx _
  dsimp only
  intro _ hrec _
  obtain ⟨d,hd⟩ := checks p q hp hq hqMax hq8 hq5 hp4 hp5 hpLo hpHi hmod
  apply signCertificate_sound hd (le_of_lt hx)
  simp only [cubic, pairCoeff, sumCoeff, productCoeff]
  linear_combination -hrec

def expandSign (p q field : ℕ) : ℕ :=
  let lower := q + field % 4096
  let upperOffset := field / 4096
  let upper := if upperOffset = 0 then 0 else p-upperOffset
  lower + 262144*upper

def natQTerm (p q : ℕ) : ℕ := (p*p+p+1)*(q+1)
def natSumCoeff (p q : ℕ) : ℕ := natQTerm p q+2*p*p*p
def natPairPlusTwo (p q : ℕ) : ℕ := 2*p*p*p*(p+q)+natQTerm p q
def natProductCoeff (p q : ℕ) : ℕ := 2*(p*p*p*p*q+12)

def cubicHigh (p q x : ℕ) : ℕ := (2*x*x+natPairPlusTwo p q)*x
def cubicLow (p q x : ℕ) : ℕ := (natSumCoeff p q*x+2)*x+natProductCoeff p q
def slopeHigh (p q x y : ℕ) : ℕ := 2*(x*x+x*y+y*y)+natPairPlusTwo p q
def slopeLow (p q x y : ℕ) : ℕ := natSumCoeff p q*(x+y)+2

theorem natSumCoeff_cast (p q : ℕ) : (natSumCoeff p q : ℤ) = sumCoeff p q := by
  unfold natSumCoeff natQTerm sumCoeff
  push_cast
  ring

theorem cubic_parts (p q x : ℕ) :
    cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x =
      (cubicHigh p q x : ℤ) - cubicLow p q x := by
  simp only [cubic,pairCoeff,sumCoeff,productCoeff,cubicHigh,cubicLow,
    natPairPlusTwo,natSumCoeff,natQTerm,natProductCoeff]
  push_cast
  ring

theorem slope_parts (p q x y : ℕ) :
    slope (sumCoeff p q) (pairCoeff p q) x y =
      (slopeHigh p q x y : ℤ) - slopeLow p q x y := by
  simp only [slope,pairCoeff,sumCoeff,slopeHigh,slopeLow,natPairPlusTwo,natSumCoeff,natQTerm]
  push_cast
  ring

/-- Evaluate the same signs using only nonnegative literal arithmetic. -/
def fastSign (p q field : ℕ) : Bool :=
  let a := q+field%4096
  let offset := field/4096
  decide (6*p ≤ natSumCoeff p q ∧ a < 262144) &&
    if offset = 0 then
      decide (1 ≤ a ∧ a+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        slopeLow p q (a-1) a ≤ slopeHigh p q (a-1) a ∧
        slopeHigh p q a (a+1) ≤ slopeLow p q a (a+1))
    else
      let b := p-offset
      decide (a+1 ≤ b ∧ b+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        cubicLow p q (a+1) < cubicHigh p q (a+1) ∧
        cubicLow p q b < cubicHigh p q b ∧
        cubicHigh p q (b+1) < cubicLow p q (b+1))

theorem fastSign_sound {p q field : ℕ} (h : fastSign p q field = true) :
    signCertificate p q (expandSign p q field) = true := by
  let a := q+field%4096
  let o := field/4096
  let b := if o=0 then 0 else p-o
  have hbase : 6*p ≤ natSumCoeff p q ∧ a<262144 := by
    have hh := (show decide (6*p ≤ natSumCoeff p q ∧ a < 262144) = true ∧ _ by
      simpa only [fastSign,a,Bool.and_eq_true] using h).1
    exact decide_eq_true_eq.mp hh
  have hL : 6*(p:ℤ) ≤ sumCoeff p q := by
    rw [← natSumCoeff_cast]
    exact_mod_cast hbase.1
  have hmod : (a+262144*b)%262144 = a := by omega
  have hdiv : (a+262144*b)/262144 = b := by omega
  change signCertificate p q (a+262144*b) = true
  simp only [signCertificate,hmod,hdiv,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨hL,?_⟩
  by_cases ho : o=0
  · have hb : b=0 := by simp [b,ho]
    simp only [hb,if_true,decide_eq_true_eq]
    have hcase : 1 ≤ a ∧ a+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        slopeLow p q (a-1) a ≤ slopeHigh p q (a-1) a ∧
        slopeHigh p q a (a+1) ≤ slopeLow p q a (a+1) := by
      have hh : field/4096=0 := ho
      simp only [fastSign,hh,if_true,Bool.and_eq_true,decide_eq_true_eq] at h
      exact h.2
    obtain ⟨ha,hap,hc,hl,hr⟩ := hcase
    refine ⟨by exact_mod_cast hap,?_,?_,?_⟩
    · rw [cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hc)
    · have hs : ((a-1 : ℕ) : ℤ) = (a:ℤ)-1 := by
        rw [Int.ofNat_sub ha]
        rfl
      rw [← hs,slope_parts]
      exact sub_nonneg.mpr (by exact_mod_cast hl)
    · rw [← Int.natCast_succ,slope_parts]
      exact sub_nonpos.mpr (by exact_mod_cast hr)
  · have hb : b=p-o := if_neg ho
    have hcase : a+1 ≤ b ∧ b+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        cubicLow p q (a+1) < cubicHigh p q (a+1) ∧
        cubicLow p q b < cubicHigh p q b ∧
        cubicHigh p q (b+1) < cubicLow p q (b+1) := by
      have hh : ¬field/4096=0 := ho
      simp only [fastSign,hh,if_false,Bool.and_eq_true,decide_eq_true_eq] at h
      simpa only [a,o,hb] using h.2
    obtain ⟨hab,hbp,hca,hca',hcb,hcb'⟩ := hcase
    have hbn : b≠0 := by omega
    simp only [hbn,if_false,decide_eq_true_eq]
    refine ⟨by exact_mod_cast hab,by exact_mod_cast hbp,?_,?_,?_,?_⟩
    · rw [cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hca)
    · rw [← Int.natCast_succ,cubic_parts]
      exact sub_pos.mpr (by exact_mod_cast hca')
    · rw [cubic_parts]
      exact sub_pos.mpr (by exact_mod_cast hcb)
    · rw [← Int.natCast_succ,cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hcb')

def fastPacked (q : ℕ) : List ℕ → ℕ → Bool
  | [], data => decide (data = 0)
  | p::ps, data =>
    fastSign p q (data % 16777216) &&
      fastPacked q ps (data / 16777216)

theorem fastPacked_sound {q p : ℕ} {ps : List ℕ} {data : ℕ}
    (h : fastPacked q ps data = true) (hp : p ∈ ps) :
    ∃ d, signCertificate p q d = true := by
  induction ps generalizing data with
  | nil => simp at hp
  | cons a as ih =>
    simp only [fastPacked,Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hpas
    · exact ⟨_,fastSign_sound h.1⟩
    · exact ih h.2 hpas

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked01 {p : ℕ} (hp : p.Prime) (hlo : 2*67 < p)
    (hhi : p^2 < 67^3) (hmod : p%3 ≠ 67%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 67 d = true := by
  have replay1_0 : fastPacked 67 (candidateList 67 0 28)
      0x2500002600002600002600102700102a00302c00403a011 = true := by decide +kernel
  have hs : p*p ≤ 67^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 28 := by
    have hc : (67^3 : ℕ).sqrt = 548 := by decide +kernel
    rw [hc] at hpBound
    omega
  exact fastPacked_sound replay1_0 (candidateP_mem hp hlo hhi hmod hres (by omega) (by omega))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked02 {p : ℕ} (hp : p.Prime) (hlo : 2*107 < p)
    (hhi : p^2 < 107^3) (hmod : p%3 ≠ 107%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 107 d = true := by
  have replay2_0 : fastPacked 107 (candidateList 107 0 56)
      0x3a00003a00003a00003a00003a00003b00103b00103c00103c00103d00203e00203e00303f00304000404500704c00d05201300001a = true := by decide +kernel
  have hs : p*p ≤ 107^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 56 := by
    have hc : (107^3 : ℕ).sqrt = 1106 := by decide +kernel
    rw [hc] at hpBound
    omega
  exact fastPacked_sound replay2_0 (candidateP_mem hp hlo hhi hmod hres (by omega) (by omega))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked05 {p : ℕ} (hp : p.Prime) (hlo : 2*227 < p)
    (hhi : p^2 < 227^3) (hmod : p%3 ≠ 227%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 227 d = true := by
  have replay5_0 : fastPacked 227 (candidateList 227 0 172)
      0x7700007700007700007700007700007800007800007800007800007800007800007800107900107900107900107900107900107a00107a00107a00107b00107b00207c00207c00207c00207d00207d00207d00207e00307e00307e00308000408000408300608400608500708700808a00a08b00b08e00d09000f0960130a201e0ab02600005d00005100003e000032 = true := by decide +kernel
  have hs : p*p ≤ 227^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 172 := by
    have hc : (227^3 : ℕ).sqrt = 3420 := by decide +kernel
    rw [hc] at hpBound
    omega
  exact fastPacked_sound replay5_0 (candidateP_mem hp hlo hhi hmod hres (by omega) (by omega))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked07 {p : ℕ} (hp : p.Prime) (hlo : 2*307 < p)
    (hhi : p^2 < 307^3) (hmod : p%3 ≠ 307%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 307 d = true := by
  have replay7_0 : fastPacked 307 (candidateList 307 0 256)
      0xa00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a10000a10000a10000a10010a10010a10010a20010a20010a20010a20010a20010a30010a30010a30010a30010a30010a30010a40010a40010a40010a40010a40020a50020a50020a60020a60020a70020a80030a80030a80030a90040a90040aa0040aa0040ab0040ac0050ac0050ac0050ae0060af0070b00070b10080b20080b30090b500a0b700c0b800c0ba00e0bc00f0bd0100c00130ca01a0ce01e0d70260dc02a0e503212707100006100004e = true := by decide +kernel
  have replay7_1 : fastPacked 307 (candidateList 307 256 13)
      0x9f00009f0000a0000 = true := by decide +kernel
  have hs : p*p ≤ 307^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 269 := by
    have hc : (307^3 : ℕ).sqrt = 5379 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 2 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay7_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay7_1 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked08 {p : ℕ} (hp : p.Prime) (hlo : 2*347 < p)
    (hhi : p^2 < 347^3) (hmod : p%3 ≠ 347%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 347 d = true := by
  have replay8_0 : fastPacked 347 (candidateList 347 0 256)
      0xb50000b50000b50000b50000b60000b60010b60010b60010b60010b60010b60010b60010b60010b60010b60010b70010b70010b70010b70010b70010b70010b80010b80010b80010b80010b80010b80010b80010b90010b90020b90020ba0020ba0020ba0020bb0020bc0030bc0030bc0030bc0030bd0030be0030be0040bf0040bf0040c00040c00050c10050c20060c30060c50070c70080c70090c80090c900a0ca00a0cc00b0cc00c0ce00d0d000e0d000f0d50120d60130e301d0e70200ea0230fa03110d04211804d000088000075000056 = true := by decide +kernel
  have replay8_1 : fastPacked 347 (candidateList 347 256 68)
      0xb40000b40000b40000b40000b40000b40000b40000b40000b40000b40000b40000b40000b40000b40000b40000b40000b50000b50000b50000b50000b50000b50000b50000b5000 = true := by decide +kernel
  have hs : p*p ≤ 347^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 324 := by
    have hc : (347^3 : ℕ).sqrt = 6463 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 2 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay8_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay8_1 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked11 {p : ℕ} (hp : p.Prime) (hlo : 2*467 < p)
    (hhi : p^2 < 467^3) (hmod : p%3 ≠ 467%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 467 d = true := by
  have replay11_0 : fastPacked 467 (candidateList 467 0 256)
      0xf70020f70020f70020f70020f80020f80020f80020f80020f90020f90020f90020f90020f90020f90030fa0030fa0030fb0030fb0030fb0030fb0030fc0030fc0030fc0040fd0040fd0040fd0040fd0040fe0040fe0050ff0050ff00510000610100610200610400710500810500810600810600810700910900a10a00a10b00b10c00c10d00d10f00e11100f11201011601211a01511e01812001912101a12501d12701f12c02312e02513402913802d13b02f14b03d1500420000bf0000ac0000a000006e = true := by decide +kernel
  have replay11_1 : fastPacked 467 (candidateList 467 256 249)
      0xf00000f00000f00000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f10000f20000f20000f20000f20000f20000f20000f20000f20000f20000f20000f20000f20000f20000f20000f30000f30010f30010f30010f30010f30010f30010f30010f30010f30010f30010f40010f40010f40010f40010f40010f40010f40010f40010f50010f50010f50010f50010f50010f50010f50010f50010f60010f60010f60010f60010f60010f60010f60010f60010f60010f70020f7002 = true := by decide +kernel
  have hs : p*p ≤ 467^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 505 := by
    have hc : (467^3 : ℕ).sqrt = 10091 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 2 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay11_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay11_1 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked13 {p : ℕ} (hp : p.Prime) (hlo : 2*547 < p)
    (hhi : p^2 < 547^3) (hmod : p%3 ≠ 547%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 547 d = true := by
  have replay13_0 : fastPacked 547 (candidateList 547 0 256)
      0x12400312400312500312500312500412600412600412600412700412700412700412800512900512a00612a00612b00612b00612c00612c00612d00712e00812f00813000813000913100913200a13300a13400a13500b13600c13600c13700c13800d13b00f13b00f13e01114101314201314701714801714901814f01c15001d15201f15402015a02415e02816002a16402c17103817a03f17e04318a04e1940561a80691ca0890000db0000cf0000b000009d000091000072 = true := by decide +kernel
  have replay13_1 : fastPacked 547 (candidateList 547 256 256)
      0x11a00011b00011b00011b00011b00011b00011b00011b00011b00011b00011b00011b00011b00011b00011b00011b00111b00111b00111b00111c00111c00111c00111c00111c00111c00111c00111c00111c00111c00111c00111c00111c00111c00111d00111d00111d00111d00111d00111d00111d00111d00111d00111d00111e00111e00111e00111e00111e00111e00111e00111e00111e00111e00111e00111f00111f00111f00111f00111f00111f00111f00111f001120002120002120002120002120002121002121002121002121002121002121002121002121002122002122002122003123003123003123003124003124003 = true := by decide +kernel
  have replay13_2 : fastPacked 547 (candidateList 547 512 128)
      0x11900011900011900011900011900011900011900011900011900011900011900011900011900011900011900011900011900011900011900011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a00011a000 = true := by decide +kernel
  have hs : p*p ≤ 547^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 640 := by
    have hc : (547^3 : ℕ).sqrt = 12793 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 3 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay13_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay13_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay13_2 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked14 {p : ℕ} (hp : p.Prime) (hlo : 2*587 < p)
    (hhi : p^2 < 587^3) (hmod : p%3 ≠ 587%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 587 d = true := by
  have replay14_0 : fastPacked 587 (candidateList 587 0 256)
      0x13b00413b00413c00413c00413d00513d00513d00513e00513e00513e00513e00513f00613f00613f00614000614000614200714200714200714300714300814400814400814500814600914600914600914700a14800a14a00b14a00b14c00c14c00d14e00e15201015401115501115601215701315801415c01715e01716101a16201b16501d16902016d02217002517802b18303418d03c1920411960441a104e1a90551ba0641c206c1e00881fe0a52270ce0000c40000b8 = true := by decide +kernel
  have replay14_1 : fastPacked 587 (candidateList 587 256 256)
      0x13000113000113000113000113000113000113000113000113000113100113100113100113100113100113100113100113100113100113100113100113100113100113100113200113200113200113200113200113200113200113200113200113200113200113300113300113300113300113300113300113300113300113400113400213400213400213400213500213500213500213500213500213500213500213600213600213600213600213600213700213700213700313700313700313800313800313800313800313800313900313900313900313900313900313900313a00313a00413a00413a00413b004 = true := by decide +kernel
  have replay14_2 : fastPacked 587 (candidateList 587 512 200)
      0x12d00012d00012d00012d00012d00012d00012d00012d00012d00012d00012d00012d00012d00012d00012d00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012e00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f00012f000130001130001130001 = true := by decide +kernel
  have hs : p*p ≤ 587^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 712 := by
    have hc : (587^3 : ℕ).sqrt = 14221 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 3 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay14_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay14_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay14_2 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked19 {p : ℕ} (hp : p.Prime) (hlo : 2*787 < p)
    (hhi : p^2 < 787^3) (hmod : p%3 ≠ 787%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 787 d = true := by
  have replay19_0 : fastPacked 787 (candidateList 787 0 256)
      0x1b200b1b300b1b400c1b400c1b600d1b700d1b700e1b800e1b900e1b900f1ba00f1bd0111bf0121c20131c30141c30151c50151c60161c70171cb0191cd01b1cf01c1d101d1d301f1d401f1d80221da0231de0261e00281e402a1e502c1e702d1ea0301f50381f703a20204220d04b21004e22706222c06623306d25508b25d09326d0a227a0ae2e511700012a00011e00010b0000cd0000ae0000a2 = true := by decide +kernel
  have replay19_1 : fastPacked 787 (candidateList 787 256 256)
      0x19c00219c00219c00219c00219c00219c00219c00219c00219c00219d00219d00219d00219d00219d00219d00219e00319e00319e00319e00319e00319e00319e00319f00319f00319f00319f00319f00319f0031a00031a00031a00031a00031a00031a00041a10041a10041a10041a20041a20041a20041a20041a20041a20041a30041a30041a30041a30041a30041a40051a40051a40051a40051a50051a50051a50051a50051a50051a60051a60051a60061a60061a60061a70061a90071a90071a90071a90071aa0071aa0071ab0081ab0081ab0081ab0081ac0081ac0081ac0081ac0081ae0091af0091af00a1b000a1b100b1b200b = true := by decide +kernel
  have replay19_2 : fastPacked 787 (candidateList 787 512 256)
      0x19500119500119500119600119600119600119600119600119600119600119600119600119600119600119600119600119600119600119600119600119600119600119600119700119700119700119700119700119700119700119700119700119700119700119700119700119700119700119800119800119800119800119800119800119800119800119800119800119800119800119800119800119900119900119900119900119900119900119900119900119900119900119900119a00119a00219a00219a00219a00219a00219a00219a00219a00219a00219b00219b00219b00219b00219b00219b00219b00219b00219b00219c002 = true := by decide +kernel
  have replay19_3 : fastPacked 787 (candidateList 787 768 256)
      0x193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000193000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000194000195000195000195000195000195000195000195000195000195000195000195001195001195001195001195001195001195001195001195001195001195001195001195001 = true := by decide +kernel
  have replay19_4 : fastPacked 787 (candidateList 787 1024 80)
      0x192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000192000193000193000 = true := by decide +kernel
  have hs : p*p ≤ 787^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1104 := by
    have hc : (787^3 : ℕ).sqrt = 22078 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 5 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay19_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay19_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay19_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay19_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay19_4 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked20 {p : ℕ} (hp : p.Prime) (hlo : 2*827 < p)
    (hhi : p^2 < 827^3) (hmod : p%3 ≠ 827%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 827 d = true := by
  have replay20_0 : fastPacked 827 (candidateList 827 0 256)
      0x1cb00d1cc00d1cc00e1cd00e1cf00f1d00101d10101d20111d20111d30111d40121d40121d50121d60131d60131d80141dc0171dd0171de0181de0181df0191e101a1e101a1e401c1e701d1e801e1e801f1ea0201ed0221f10251f30261f802a1fa02b1ff02e20a03721003c21303f21904321b04521f04823005623505b24306724a06d25707926f08f2870a52a70c40001510001140000e80000d50000c90000aa = true := by decide +kernel
  have replay20_1 : fastPacked 827 (candidateList 827 256 256)
      0x1b20031b20031b20031b20031b30031b30031b30031b30031b30031b30031b30031b40031b40031b40031b40031b40031b40031b40031b50031b50031b50031b50041b50041b50041b60041b60041b60041b60041b60041b60041b60041b70041b70041b70041b80041b80051b80051b80051b90051b90051b90051b90051ba0051ba0051bb0061bb0061bb0061bc0061bc0061bd0061bd0061bd0071be0071be0071be0071bf0071c00081c00081c00081c10081c10081c20091c20091c20091c30091c40091c400a1c500a1c500a1c500a1c600a1c600b1c600b1c700b1c700b1c800b1c800c1c900c1ca00c1ca00d = true := by decide +kernel
  have replay20_2 : fastPacked 827 (candidateList 827 512 256)
      0x1ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ab0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ac0011ad0011ad0011ad0011ad0011ad0011ad0011ad0011ad0011ad0011ad0011ad0011ae0011ae0011ae0011ae0011ae0011ae0011ae0021ae0021ae0021ae0021ae0021af0021af0021af0021af0021af0021af0021af0021af0021af0021af0021af0021b00021b00021b00021b00021b00021b00021b00021b00021b00021b10021b10021b10021b10021b10021b10021b10021b1002 = true := by decide +kernel
  have replay20_3 : fastPacked 827 (candidateList 827 768 256)
      0x1a70001a70001a70001a70001a70001a70001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a80001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90001a90011a90011a90011a90011a90011a90011a90011a90011a90011a90011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011aa0011ab0011ab001 = true := by decide +kernel
  have replay20_4 : fastPacked 827 (candidateList 827 1024 166)
      0x1a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a60001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a70001a7000 = true := by decide +kernel
  have hs : p*p ≤ 827^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1190 := by
    have hc : (827^3 : ℕ).sqrt = 23782 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 5 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay20_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay20_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay20_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay20_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay20_4 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked22 {p : ℕ} (hp : p.Prime) (hlo : 2*907 < p)
    (hhi : p^2 < 907^3) (hmod : p%3 ≠ 907%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 907 d = true := by
  have replay22_0 : fastPacked 907 (candidateList 907 0 256)
      0x1fe0121ff01320001320001320301520401620601620701720801720801820901920e01b21201e21502021702121802221a02321c02521d02622302a22702d22a02f22e03123103423203523a03b23c03d24304224804624d04a25104d25304f25a05426f06627206928907e2a20942a909b2f60e330b0f833e1290001430001360001240001170000e50000c60000ba = true := by decide +kernel
  have replay22_1 : fastPacked 907 (candidateList 907 256 256)
      0x1de0031de0041de0041de0041de0041de0041df0041df0041df0041df0041df0041df0041e00041e00041e00041e00041e10041e10041e10041e10051e20051e20051e20051e20051e20051e20051e30051e30051e30051e40051e40051e40061e40061e40061e50061e50061e50061e60061e60061e60071e70071e70071e70071e70071e80071e80071e80071e80071e90081e90081e90081ea0081ea0081ea0081eb0081eb0081eb0091ec0091ec0091ec0091ec0091ed0091ee00a1f000b1f000b1f100b1f100b1f200b1f300c1f300c1f300c1f400c1f400d1f400d1f500d1f500d1f500d1f800f1f900f1fa0101fb0101fd0111fd011 = true := by decide +kernel
  have replay22_2 : fastPacked 907 (candidateList 907 512 256)
      0x1d50011d50011d50011d50011d50011d50011d60011d60011d60011d60011d60011d60011d60011d60011d60011d60011d60011d60011d60011d60011d60011d70011d70021d70021d70021d70021d70021d70021d70021d70021d70021d70021d70021d80021d80021d80021d80021d80021d80021d80021d80021d80021d80021d80021d90021d90021d90021d90021d90021d90021d90021d90021d90021d90021da0021da0021da0021da0021da0021da0021da0021da0021da0021db0031db0031db0031db0031db0031dc0031dc0031dc0031dc0031dc0031dc0031dc0031dd0031dd0031dd0031dd0031dd0031dd0031dd0031de003 = true := by decide +kernel
  have replay22_3 : fastPacked 907 (candidateList 907 768 256)
      0x1d10001d10001d10001d10001d10001d10001d20001d20001d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d20011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d30011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d40011d50011d50011d50011d50011d50011d50011d50011d50011d50011d50011d50011d50011d5001 = true := by decide +kernel
  have replay22_4 : fastPacked 907 (candidateList 907 1024 256)
      0x1cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d10001d1000 = true := by decide +kernel
  have replay22_5 : fastPacked 907 (candidateList 907 1280 86)
      0x1ce0001ce0001ce0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf0001cf000 = true := by decide +kernel
  have hs : p*p ≤ 907^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1366 := by
    have hc : (907^3 : ℕ).sqrt = 27315 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 6 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay22_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay22_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay22_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay22_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay22_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay22_5 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked23 {p : ℕ} (hp : p.Prime) (hlo : 2*947 < p)
    (hhi : p^2 < 947^3) (hmod : p%3 ≠ 947%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 947 d = true := by
  have replay23_0 : fastPacked 947 (candidateList 947 0 256)
      0x21801421901521a01621b01721e01821f01922001a22201a22201b22401c22401c22501d22601d22801e22801f22b02023202523302623402623502723602823902a23a02a23e02d24203024303224503224703424b03725303d25603f25f04726104826a04f27e06128a06b29007029b07a2a007e2a80852d10aa2df0b730b0e23280fe3aa17d00015d00013e00011f0000ed = true := by decide +kernel
  have replay23_1 : fastPacked 947 (candidateList 947 256 256)
      0x1f40041f50041f50041f50041f50041f60051f60051f60051f60051f60051f70051f70051f70051f70051f80051f80051f80051f80051f80051f80061f90061f90061f90061f90061fa0061fa0061fa0061fa0061fa0061fa0061fb0061fb0071fb0071fc0071fc0071fd0071fd0071fd0071fe0081fe0081fe0081ff0081ff00820000920100920100920100920300a20300a20300a20400a20400a20500b20500b20600b20600b20700c20800c20800c20900d20a00d20b00e20b00e20c00e20c00e20e00f20e00f20f00f20f010210010210010211011211011212011212012213012214012214013216013217014 = true := by decide +kernel
  have replay23_2 : fastPacked 947 (candidateList 947 512 256)
      0x1eb0011eb0011eb0011eb0011eb0021eb0021eb0021eb0021eb0021eb0021eb0021eb0021eb0021eb0021ec0021ec0021ec0021ec0021ec0021ec0021ec0021ec0021ec0021ec0021ec0021ec0021ed0021ed0021ed0021ed0021ed0021ed0021ed0021ed0021ed0021ee0021ee0021ee0021ee0021ee0021ee0021ee0021ee0021ee0021ef0021ef0021ef0021ef0031ef0031ef0031ef0031ef0031ef0031f00031f00031f00031f00031f00031f00031f00031f10031f10031f10031f10031f10031f10031f10031f10031f20031f20031f20031f20031f20031f20031f20041f30041f30041f30041f30041f30041f40041f40041f4004 = true := by decide +kernel
  have replay23_3 : fastPacked 947 (candidateList 947 768 256)
      0x1e60011e60011e60011e60011e60011e60011e60011e60011e60011e60011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e70011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e80011e90011e90011e90011e90011e90011e90011e90011e90011e90011e90011e90011e90011e90011e90011e90011e90011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011ea0011eb0011eb001 = true := by decide +kernel
  have replay23_4 : fastPacked 947 (candidateList 947 1024 256)
      0x1e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e50001e60001e60001e60001e60001e60001e60001e60001e60001e60001e60011e60011e60011e60011e60011e60011e60011e6001 = true := by decide +kernel
  have replay23_5 : fastPacked 947 (candidateList 947 1280 178)
      0x1e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e30001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e40001e4000 = true := by decide +kernel
  have hs : p*p ≤ 947^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1458 := by
    have hc : (947^3 : ℕ).sqrt = 29142 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 6 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay23_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay23_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay23_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay23_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay23_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay23_5 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked29 {p : ℕ} (hp : p.Prime) (hlo : 2*1187 < p)
    (hhi : p^2 < 1187^3) (hmod : p%3 ≠ 1187%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1187 d = true := by
  have replay29_0 : fastPacked 1187 (candidateList 1187 0 256)
      0x2be02d2c102f2c20302c50322ca0352cd0372cf0392d203b2d403c2d703f2d80402da0412db0422df0452e10462e604a2f60562f80582fb05a2fd05c30005f30606330806531206e31d07632107a32507d32a08233708d34e0a23560a93760c637e0cd3a30f04401880001cb0001b900019a00018d00017b00013000011d0000f2 = true := by decide +kernel
  have replay29_1 : fastPacked 1187 (candidateList 1187 256 256)
      0x27d00927e00927e00927e00927f00a27f00a27f00a28000a28000a28000a28100b28100b28200b28200b28300b28300b28300b28300c28300c28400c28400c28400c28500c28500d28600d28600d28700d28700d28700d28700e28800e28900e28900e28a00f28b00f28c00f28c01028d01028e01128e01128f01128f01129001229201229301329301329401329601529701529801629801629901629a01729a01729c01829d01829f01a2a001a2a001a2a201b2a301c2a501d2a601e2a601e2a801f2aa0202ac0212ac0222ae0222ae0232af0232b10242b10252b20252b40262b50272b60282b70292ba02a2bc02c = true := by decide +kernel
  have replay29_2 : fastPacked 1187 (candidateList 1187 512 256)
      0x26c00326d00326d00326d00326d00426d00426d00426d00426d00426e00426e00426e00426e00426e00426e00426e00426e00426e00426f00426f00426f00426f00426f00426f00426f00427000427000427000427000427000427000427000527100527100527100527100527200527200527200527200527200527200527300527300527300527300527300527400627400627400627400627400627500627500627500627500627500627500627600627600627600727700727700727700727700727700727800727800727800727900727900727900727900827900827a00827a00827a00827a00827a00827b00827c00927c00927c009 = true := by decide +kernel
  have replay29_3 : fastPacked 1187 (candidateList 1187 768 256)
      0x26500226500226500226500226500226600226600226600226600226600226600226600226600226600226600226600226600226600226600226600226600226600226600226600226700226700226700226700226700226700226700226700226700226800226800226800226800226800226800226800226800226800226800226800226800226900226900226900226900226900226900226900226900326900326900326a00326a00326a00326a00326a00326a00326a00326a00326a00326a00326a00326b00326b00326b00326b00326b00326b00326b00326b00326b00326c00326c00326c00326c00326c00326c00326c00326c00326c003 = true := by decide +kernel
  have replay29_4 : fastPacked 1187 (candidateList 1187 1024 256)
      0x261001261001261001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001262001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001263001264001264001264001264001264001264001264001264001264001264001264001264001264001264001264001264001264001265001265001265001265001265002265002265002265002265002265002265002265002 = true := by decide +kernel
  have replay29_5 : fastPacked 1187 (candidateList 1187 1280 256)
      0x25f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00025f00125f00125f00125f00125f00125f00125f00125f00125f00125f00125f00125f001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001260001261001261001261001261001261001261001261001261001261001261001261001261001261001261001261001261001261001261001261001261001 = true := by decide +kernel
  have replay29_6 : fastPacked 1187 (candidateList 1187 1536 256)
      0x25d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025e00025f00025f00025f00025f00025f00025f00025f000 = true := by decide +kernel
  have replay29_7 : fastPacked 1187 (candidateList 1187 1792 253)
      0x25c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025c00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d00025d000 = true := by decide +kernel
  have hs : p*p ≤ 1187^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 2045 := by
    have hc : (1187^3 : ℕ).sqrt = 40895 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 8 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay29_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay29_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay29_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay29_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay29_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay29_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay29_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay29_7 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked32 {p : ℕ} (hp : p.Prime) (hlo : 2*1307 < p)
    (hhi : p^2 < 1307^3) (hmod : p%3 ≠ 1307%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1307 d = true := by
  have replay32_0 : fastPacked 1307 (candidateList 1307 0 256)
      0x31904031d04331f04432304732a04d32e04f33205233605533805733c05b33e05c34105e34306034806434b06635306d36b08136e08337308737608a37b08f38509738909a39a0aa3ac0ba3b50c13bb0c73c40d03df0e841211942712c49e1a04dc1dd0001f0000193000167000155000135000129000116 = true := by decide +kernel
  have replay32_1 : fastPacked 1307 (candidateList 1307 256 256)
      0x2c300c2c400d2c400d2c500d2c500d2c600d2c600e2c700e2c700e2c800e2c800f2c800f2c900f2ca00f2ca0102ca0102cb0102cb0102cb0102cc0102cc0112cd0112cd0112ce0112cf0122cf0122cf0122d00122d00132d10132d10132d20132d20142d40142d50152d60152d60162d70162d90172d90172da0172db0182dc0192de0192df01a2e001b2e001b2e301d2e401d2e501e2e601e2e701f2e801f2e90202eb0212ec0222ef0242f00242f10252f30262f50272f80292f80292f902a2fc02c2fe02d30002f30102f30303030403130503230703330803430903530b03630c03730f03931003931403c31603e = true := by decide +kernel
  have replay32_2 : fastPacked 1307 (candidateList 1307 512 256)
      0x2ae0052af0052af0052af0052af0052af0052af0052b00052b00052b00052b00052b00052b00052b00052b00052b10052b10052b10052b10062b10062b20062b20062b20062b20062b20062b20062b20062b30062b30062b30062b30062b30062b40062b40072b40072b50072b50072b50072b50072b50072b60072b60072b60072b60072b70072b70082b70082b70082b80082b80082b80082b80082b90082b90082b90082b90082ba0092ba0092ba0092ba0092bb0092bb0092bb0092bb0092bc0092bc0092bc00a2bd00a2bd00a2be00a2be00a2be00a2be00a2bf00a2bf00b2bf00b2c000b2c000b2c000b2c000b2c200c2c200c2c200c = true := by decide +kernel
  have replay32_3 : fastPacked 1307 (candidateList 1307 768 256)
      0x2a60022a60022a60022a60022a60022a60022a60022a60022a60022a60022a60022a60022a60032a60032a60032a60032a60032a70032a70032a70032a70032a70032a70032a70032a70032a70032a70032a70032a70032a70032a80032a80032a80032a80032a80032a90032a90032a90032a90032a90032a90032a90032a90032a90032a90032aa0032aa0032aa0032aa0032aa0032aa0032aa0042ab0042ab0042ab0042ab0042ab0042ab0042ab0042ab0042ab0042ab0042ab0042ac0042ac0042ac0042ac0042ac0042ac0042ad0042ad0042ad0042ad0042ad0042ad0042ad0042ad0042ae0042ae0052ae0052ae0052ae0052ae0052ae005 = true := by decide +kernel
  have replay32_4 : fastPacked 1307 (candidateList 1307 1024 256)
      0x2a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a10012a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a20022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a30022a40022a40022a40022a40022a40022a40022a40022a40022a40022a40022a40022a40022a40022a50022a50022a50022a50022a50022a50022a50022a50022a50022a50022a50022a5002 = true := by decide +kernel
  have replay32_5 : fastPacked 1307 (candidateList 1307 1280 256)
      0x29d00129d00129d00129d00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129e00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f00129f0012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a00012a1001 = true := by decide +kernel
  have replay32_6 : fastPacked 1307 (candidateList 1307 1536 256)
      0x29b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029c00029c00029c00029c00029c00029c00029c00029c00029c00029c00029c00029c00029c00029c00029c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129c00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d00129d001 = true := by decide +kernel
  have replay32_7 : fastPacked 1307 (candidateList 1307 1792 256)
      0x29900029900029900029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029a00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b00029b000 = true := by decide +kernel
  have replay32_8 : fastPacked 1307 (candidateList 1307 2048 256)
      0x298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000299000 = true := by decide +kernel
  have replay32_9 : fastPacked 1307 (candidateList 1307 2304 59)
      0x298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000298000 = true := by decide +kernel
  have hs : p*p ≤ 1307^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 2363 := by
    have hc : (1307^3 : ℕ).sqrt = 47251 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 10 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay32_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay32_9 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked35 {p : ℕ} (hp : p.Prime) (hlo : 2*1427 < p)
    (hhi : p^2 < 1427^3) (hmod : p%3 ≠ 1427%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1427 d = true := by
  have replay35_0 : fastPacked 1427 (candidateList 1427 0 256)
      0x37b05938105d38405f38a06439306c39907039e0743a40793a807c3ae0823b10843b50873b808a3c00903c40943d109f3f70c13fc0c54050cd40a0d24140da4240ea42c0f144e11147613648b14a49b1594b817552e1e900021a0002080001ca0001bd00018c00012e = true := by decide +kernel
  have replay35_1 : fastPacked 1427 (candidateList 1427 256 256)
      0x30a01030c01130c01130c01130d01230e01230f01230f01331001331001331101331101431201431301531401531401531401531401531501631601631601631601631701731801731901831901831a01831b01831b01931c01931c01931e01a31e01a31f01b32101c32201d32301d32401e32601f32701f32701f32802032a02132c02232e02332f02433002433402733502833602833702933802a33a02b33b02c33e02d33f02e34303034403234503234803434b03634e03834f03935003935303c35703e35904035a04135d04235f04436004436204636404836504836804b36a04c36d04e36f04f374053378056 = true := by decide +kernel
  have replay35_2 : fastPacked 1427 (candidateList 1427 512 256)
      0x2f10062f10062f10062f20072f20072f20072f20072f20072f30072f30072f30072f30072f30072f30072f40072f40072f40072f40072f40072f40072f50082f50082f50082f60082f60082f60082f60082f60082f60082f70082f70082f70082f70092f80092f80092f90092f90092f90092f90092fa0092fa0092fa00a2fa00a2fb00a2fb00a2fb00a2fc00a2fc00a2fc00a2fc00a2fd00b2fd00b2fe00b2fe00b2fe00b2ff00b2ff00b2ff00b2ff00c30000c30000c30100c30100c30100c30100c30200d30200d30300d30400d30400d30400e30400e30500e30500e30500e30600e30600f30600f30700f30700f309010309010309010 = true := by decide +kernel
  have replay35_3 : fastPacked 1427 (candidateList 1427 768 256)
      0x2e60032e60032e60032e60032e70032e70032e70032e70032e70032e70032e70032e70032e70032e70032e70032e70032e70042e80042e80042e80042e80042e80042e80042e80042e80042e80042e80042e80042e80042e90042e90042e90042e90042ea0042ea0042ea0042ea0042ea0042ea0042ea0042eb0042eb0042eb0042eb0042eb0052eb0052eb0052eb0052eb0052ec0052ec0052ec0052ec0052ec0052ed0052ed0052ed0052ed0052ed0052ed0052ed0052ed0052ed0052ee0052ee0052ee0052ee0052ee0052ef0062ef0062ef0062ef0062ef0062ef0062ef0062f00062f00062f00062f00062f00062f00062f00062f10062f1006 = true := by decide +kernel
  have replay35_4 : fastPacked 1427 (candidateList 1427 1024 256)
      0x2e00022e00022e00022e10022e10022e10022e10022e10022e10022e10022e10022e10022e10022e10022e10022e10022e10022e10022e10022e20022e20022e20022e20022e20022e20022e20022e20022e20022e20022e20022e20022e20022e20022e20022e20022e30022e30022e30022e30022e30022e30022e30022e30022e30022e30022e30032e30032e30032e40032e40032e40032e40032e40032e40032e40032e40032e40032e40032e40032e40032e40032e40032e40032e50032e50032e50032e50032e50032e50032e50032e50032e60032e60032e60032e60032e60032e60032e6003 = true := by decide +kernel
  have replay35_5 : fastPacked 1427 (candidateList 1427 1280 256)
      0x2dc0012dc0012dc0012dc0012dc0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012dd0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0012de0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022df0022e00022e00022e00022e00022e00022e00022e00022e00022e00022e00022e00022e00022e0002 = true := by decide +kernel
  have replay35_6 : fastPacked 1427 (candidateList 1427 1536 256)
      0x2da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012da0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012db0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc0012dc001 = true := by decide +kernel
  have replay35_7 : fastPacked 1427 (candidateList 1427 1792 256)
      0x2d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80002d80012d80012d80012d80012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012d90012da0012da0012da0012da0012da0012da001 = true := by decide +kernel
  have replay35_8 : fastPacked 1427 (candidateList 1427 2048 256)
      0x2d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d70002d80002d80002d80002d80002d80002d8000 = true := by decide +kernel
  have replay35_9 : fastPacked 1427 (candidateList 1427 2304 256)
      0x2d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d60002d6000 = true := by decide +kernel
  have replay35_10 : fastPacked 1427 (candidateList 1427 2560 136)
      0x2d40002d40002d40002d40002d40002d40002d40002d40002d40002d40002d40002d40002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d50002d5000 = true := by decide +kernel
  have hs : p*p ≤ 1427^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 2696 := by
    have hc : (1427^3 : ℕ).sqrt = 53905 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 11 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay35_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay35_10 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked40 {p : ℕ} (hp : p.Prime) (hlo : 2*1627 < p)
    (hhi : p^2 < 1627^3) (hmod : p%3 ≠ 1627%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1627 d = true := by
  have replay40_0 : fastPacked 1627 (candidateList 1627 0 256)
      0x4380994420a14470a544a0a84610bc4700c947b0d34870de48f0e54950ea4a30f74db12b5251705861ce5ec23200029f00028000026100024f0002040001d30001b4000195000175000169 = true := by decide +kernel
  have replay40_1 : fastPacked 1627 (candidateList 1627 256 256)
      0x38401938401938501a38601a38601a38701a38701b38801b38901b38901c38901c38b01d38b01d38c01d38d01e38f01f39002039102039102039302139502239502239602339702339702339802439a02539a02539c02639d02739e02739f02839f0283a10293a302b3a402b3a502b3a902e3a902e3ab02f3ad0303ad0313af0323b00323b00333b10333b20343b30343b80383b90383ba0393bc03a3be03b3be03c3c003d3c203e3c303f3c60413c60413c80423c90433ca0443d20493dd0513de0523e00533e30553e60573eb05b3ee05e3f005f3f20613f30623f50633f70653f90663fb06840f07741107941908042108642d090431093 = true := by decide +kernel
  have replay40_2 : fastPacked 1627 (candidateList 1627 512 256)
      0x36200a36200a36200a36200a36300a36300a36300a36400b36400b36400b36400b36400b36500b36500b36500b36600b36600b36600b36600c36600c36700c36700c36700c36800c36800c36800c36800c36900d36900d36a00d36a00d36a00d36b00d36b00d36c00e36c00e36d00e36d00e36d00e36d00e36d00e36d00e36e00f36e00f36f00f36f00f36f00f37001037001037101037201037201037201037201137301137301137401137401137501237501237501237501237601237801337801337801337901437a01437b01437b01537c01537c01537d01637d01637e01637f017380017381017381018382018382018383018384019 = true := by decide +kernel
  have replay40_3 : fastPacked 1627 (candidateList 1627 768 256)
      0x35400535400535400535400535400535400535400535500635500635500635500635500635500635500635600635600635600635600635600635700635700635700635700635700635800635800635800635800735800735800735800735900735900735900735900735900735900735a00735a00735a00735a00735b00735b00735b00735b00735b00735b00835b00835c00835c00835c00835c00835c00835d00835d00835d00835d00835d00835d00835e00835e00835e00835f00935f00935f00935f00935f00935f00936000936000936000936000936000936100936100936100a36100a36100a36100a36200a = true := by decide +kernel
  have replay40_4 : fastPacked 1627 (candidateList 1627 1024 256)
      0x34b00334b00334b00334b00334b00334b00334b00334c00334c00334c00334c00334c00334c00334c00334c00334c00334c00334c00334d00334d00334d00334d00334d00334d00334d00334d00434d00434d00434d00434d00434e00434e00434e00434e00434e00434e00434e00434e00434e00434e00434f00434f00434f00434f00434f00434f00434f00434f00434f00434f00434f004350004350004350004350004350004350004350004350004351004351004351004351004351005351005351005351005351005351005351005352005352005352005352005352005352005352005352005353005353005353005353005353005353005353005353005353005 = true := by decide +kernel
  have replay40_5 : fastPacked 1627 (candidateList 1627 1280 256)
      0x34600234600234600234600234600234600234600234600234600234600234600234700234700234700234700234700234700234700234700234700234700234700234700234700234700234700234700234700234700234700234700234700234800234800234800234800234800234800234800234800234800234800234800234800234800234800234800234800234900234900234900234900234900234900234900334900334900334900334900334900334900334900334900334a00334a00334a00334a00334a00334a00334a00334a00334a00334a00334a00334a00334a00334a00334b00334b00334b00334b00334b00334b00334b00334b00334b003 = true := by decide +kernel
  have replay40_6 : fastPacked 1627 (candidateList 1627 1536 256)
      0x342001342001342001342001342001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001343001344001344001344001344001344001344002344002344002344002344002344002344002344002344002344002344002344002344002344002344002344002344002344002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002345002346002346002346002346002346002 = true := by decide +kernel
  have replay40_7 : fastPacked 1627 (candidateList 1627 1792 256)
      0x340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001340001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001341001342001342001342001342001342001342001342001342001342001342001342001342001342001342001342001342001342001342001342001342001342001 = true := by decide +kernel
  have replay40_8 : fastPacked 1627 (candidateList 1627 2048 256)
      0x33e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133e00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f00133f001340001340001340001340001340001340001340001 = true := by decide +kernel
  have replay40_9 : fastPacked 1627 (candidateList 1627 2304 256)
      0x33c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00033d00133d00133d00133d00133d00133d00133d00133d00133d00133d00133d00133e00133e00133e00133e00133e00133e00133e00133e00133e001 = true := by decide +kernel
  have replay40_10 : fastPacked 1627 (candidateList 1627 2560 256)
      0x33b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c00033c000 = true := by decide +kernel
  have replay40_11 : fastPacked 1627 (candidateList 1627 2816 256)
      0x33a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b00033b000 = true := by decide +kernel
  have replay40_12 : fastPacked 1627 (candidateList 1627 3072 210)
      0x33900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033900033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a00033a000 = true := by decide +kernel
  have hs : p*p ≤ 1627^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3282 := by
    have hc : (1627^3 : ℕ).sqrt = 65626 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 13 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay40_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay40_12 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked41 {p : ℕ} (hp : p.Prime) (hlo : 2*1667 < p)
    (hhi : p^2 < 1667^3) (hmod : p%3 ≠ 1667%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1667 d = true := by
  have replay41_0 : fastPacked 1667 (candidateList 1667 0 256)
      0x45f0a746b0b14700b647d0c14920d349e0de4ab0e94b90f64c20fe4d310e4da1144e511f4ed12650413b51314953d17165d28b0002a700029500028800027600025700024a0002190001ed0001db0001ce0001bc000190000152 = true := by decide +kernel
  have replay41_1 : fastPacked 1667 (candidateList 1667 256 256)
      0x39e01b3a001d3a101d3a101d3a201e3a301e3a401f3a60203a60203a70203a80213a90213a90223ab0233ac0233ac0233ad0243ad0243ae0243af0253b00253b00263b10263b30273b40283b50283b60293b70293b802a3b802a3b902b3bc02c3bc02d3be02e3c10303c30313c40313c50323c90353ca0353cb0363cc0373cf0393d203b3d503d3d703e3d803f3de0433e00443e30463e40473e60483e804a3eb04c3ef04f3f20513f70553fa0573fc05840105c40505f40b06340c06440f06641406a41b06f41f07342107442507842807a42a07c42f08043208243508443a08843e08b44409044609245109b4580a1 = true := by decide +kernel
  have replay41_2 : fastPacked 1667 (candidateList 1667 512 256)
      0x37900b37900b37900b37900b37a00b37a00b37a00b37b00b37b00b37b00c37b00c37b00c37c00c37c00c37c00c37c00c37c00c37d00c37d00c37d00c37e00d37e00d37f00d37f00d37f00d38000d38000d38000e38000e38100e38100e38100e38200e38300f38300f38400f38400f38400f38501038501038501038601038601038701038801138801138801138901138901138901138a01238b01238b01238b01238c01338c01338d01338d01338d01338e01438f01439001439001539001539001539101539201539201639401639401739401739501739501739601739601839701839801839801839801939901939c01a39c01b39d01b = true := by decide +kernel
  have replay41_3 : fastPacked 1667 (candidateList 1667 768 256)
      0x36900636900636900636900636900636a00636a00636a00636a00636a00636a00636a00636a00636a00636b00636b00636b00636b00636b00636b00636b00636b00636c00636c00636c00636c00636c00636c00636c00636c00736d00736e00736e00736e00736e00736e00736e00736f00736f00736f00736f00737000837000837000837000837000837000837000837000837100837100837100837200837200837200837200837200937300937300937300937300937300937300937400937400937400937400937500937500937500937500a37600a37600a37600a37600a37700a37700a37700a37700a37700a37800a37800a37800b37800b = true := by decide +kernel
  have replay41_4 : fastPacked 1667 (candidateList 1667 1024 256)
      0x361003361003361003361003361003361003361003361003361004361004362004362004362004362004362004362004362004362004362004362004362004363004363004363004363004363004363004363004363004363004363004363004363004364004364004364004364004364004364004364004364004364004365004365004365004365004365004365004365004365004365004366005366005366005366005366005366005366005366005366005366005367005367005367005367005367005367005368005368005368005368005368005368005368005368005369005369005369006 = true := by decide +kernel
  have replay41_5 : fastPacked 1667 (candidateList 1667 1280 256)
      0x35b00235b00235b00235b00235b00235b00235b00235b00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235c00235d00235d00235d00235d00235d00235d00235d00235d00235d00235d00235d00235d00335d00335d00335d00335d00335d00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335e00335f00335f00335f00335f00335f00335f00335f00335f00335f00335f00335f00335f00335f003360003360003360003360003360003360003360003360003360003360003360003360003360003361003 = true := by decide +kernel
  have replay41_6 : fastPacked 1667 (candidateList 1667 1536 256)
      0x35700135800135800135800135800135800135800135800135800135800135800135800135800235800235800235800235800235800235800235800235800235800235800235800235800235800235800235800235900235900235900235900235900235900235900235900235900235900235900235900235900235900235900235900235900235900235900235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235a00235b00235b00235b00235b00235b00235b00235b00235b00235b00235b00235b00235b00235b00235b002 = true := by decide +kernel
  have replay41_7 : fastPacked 1667 (candidateList 1667 1792 256)
      0x355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001355001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001356001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001357001 = true := by decide +kernel
  have replay41_8 : fastPacked 1667 (candidateList 1667 2048 256)
      0x352001352001352001352001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001353001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001354001355001355001 = true := by decide +kernel
  have replay41_9 : fastPacked 1667 (candidateList 1667 2304 256)
      0x351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351001351001351001351001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001352001 = true := by decide +kernel
  have replay41_10 : fastPacked 1667 (candidateList 1667 2560 256)
      0x34f00034f00034f00034f000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000350000351000351000351000351000351000351000351000351000351000351000351000351000351000351000351000 = true := by decide +kernel
  have replay41_11 : fastPacked 1667 (candidateList 1667 2816 256)
      0x34e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f00034f000 = true := by decide +kernel
  have replay41_12 : fastPacked 1667 (candidateList 1667 3072 256)
      0x34d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e00034e000 = true := by decide +kernel
  have replay41_13 : fastPacked 1667 (candidateList 1667 3328 76)
      0x34d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d00034d000 = true := by decide +kernel
  have hs : p*p ≤ 1667^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3404 := by
    have hc : (1667^3 : ℕ).sqrt = 68061 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 14 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay41_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay41_13 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked43 {p : ℕ} (hp : p.Prime) (hlo : 2*1747 < p)
    (hhi : p^2 < 1747^3) (hmod : p%3 ≠ 1747%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1747 d = true := by
  have replay43_0 : fastPacked 1747 (candidateList 1747 0 256)
      0x4bd0d24cc0df4d30e54d80ea4fc10a51412052713253d14654c15455615e57417a6072080002a500026700024800023b00021c0001fd0001eb0001a000016e = true := by decide +kernel
  have replay43_1 : fastPacked 1747 (candidateList 1747 256 256)
      0x3cf0203d00203d10203d10213d20213d30213d30223d40223d50233d60233d60233d80243d90253d90253db0263dd0273df0283df0283e00293e202a3e402b3e402b3e602c3e702d3e702d3e802e3ea02f3eb02f3ec0303ef0323ef0323f00333f10333f40353f60363f70373f80373fc03b3fd03b3ff03c40203e40303f40404040604140604140804240804240a04341004841104841204941404b41704c41804d41a04f41d05141e05242105442205442405642505642705843105f43f06a44106b44206d44607044a07345107845607c45807d45b07f45d0814600834620854650874670894820a04850a24910ac49c0b54ad0c44b30c9 = true := by decide +kernel
  have replay43_2 : fastPacked 1747 (candidateList 1747 512 256)
      0x3a700c3a700d3a700d3a700d3a800d3a800d3a800d3a900d3a900d3a900e3a900e3aa00e3aa00e3ab00e3ab00e3ab00e3ab00e3ab00e3ac00f3ac00f3ac00f3ac00f3ad00f3ae00f3ae00f3ae0103ae0103af0103af0103b00103b10113b10113b10113b20113b30123b30123b30123b30123b40123b40123b40123b40123b50123b50133b60133b60133b70133b80143b80143b90143b90143ba0153ba0153ba0153bb0153bb0153bc0163bd0163bd0163bd0163be0173be0173bf0173c10183c10183c10183c30193c30193c401a3c501a3c601a3c601b3c701b3c801b3c801c3ca01d3ca01d3cc01e3cc01e3cd01e3cd01e3ce01f3cf01f = true := by decide +kernel
  have replay43_3 : fastPacked 1747 (candidateList 1747 768 256)
      0x39600739600739600739600739600739600739600739700739700739700739700739800739800739800739800739800739900839900839900839900839900839a00839a00839a00839a00839a00839b00839b00839b00839b00839b00839b00839c00939c00939c00939c00939c00939d00939d00939d00939d00939e00939e00939e00939e00939e00939f00a39f00a39f00a39f00a3a000a3a000a3a000a3a000a3a000a3a000a3a100a3a100a3a100b3a200b3a200b3a200b3a300b3a300b3a300b3a300b3a300b3a400b3a400b3a400c3a400c3a500c3a500c3a500c3a500c3a600c3a600c3a600c3a600c3a600c = true := by decide +kernel
  have replay43_4 : fastPacked 1747 (candidateList 1747 1024 256)
      0x38c00438c00438c00438c00438c00438c00438c00438c00438c00438c00438c00438d00438d00438d00438d00438d00438d00438d00438d00438d00438e00438e00438e00438e00438e00438e00438e00538e00538e00538e00538f00538f00538f00538f00538f00538f00538f00538f005390005390005390005390005390005390005390005390005390005390005391005391005391005391005391005391005391005391005391005391005392005392006392006392006393006393006393006393006393006393006393006393006393006393006394006394006394006394006394006394006394006395006395006395006395006395006395006395006395007 = true := by decide +kernel
  have replay43_5 : fastPacked 1747 (candidateList 1747 1280 256)
      0x38600338600338600338600338600338600338600338600338600338600338600338600338600338700338700338700338700338700338700338700338700338700338700338700338700338700338700338700338700338700338700338700338800338800338800338800338800338800338800338800338800338800338800338800338800338800338900338900338900338900338900338900338900338900338900338900338900338900338900338900338a00338a00338a00338a00338a00338a00338a00338a00438a00438a00438a00438b00438b00438b00438b00438b00438b00438b00438b00438b00438b00438b00438b00438c00438c00438c004 = true := by decide +kernel
  have replay43_6 : fastPacked 1747 (candidateList 1747 1536 256)
      0x382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002382002383002383002383002383002383002383002383002383002383002383002383002383002383002383002383002383002383002383002383002383002384002384002384002384002384002384002384002384002384002384002384002384002384002384002384002384002384002384002384002384002385002385002385002385002385002385002385002385002385002385002385002385002385002385002385002385002386002386003 = true := by decide +kernel
  have replay43_7 : fastPacked 1747 (candidateList 1747 1792 256)
      0x37e00137e00137e00137e00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f00137f001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380001380002380002380002381002381002381002381002381002381002381002381002381002381002381002381002381002381002381002381002381002381002381002381002381002 = true := by decide +kernel
  have replay43_8 : fastPacked 1747 (candidateList 1747 2048 256)
      0x37c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137d00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e00137e001 = true := by decide +kernel
  have replay43_9 : fastPacked 1747 (candidateList 1747 2304 256)
      0x37a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137b00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c00137c001 = true := by decide +kernel
  have replay43_10 : fastPacked 1747 (candidateList 1747 2560 256)
      0x37900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037900037a00037a00037a00037a00037a00037a00037a00037a00037a00037a00037a00037a00037a00037a00037a00037a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a00137a001 = true := by decide +kernel
  have replay43_11 : fastPacked 1747 (candidateList 1747 2816 256)
      0x377000377000377000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000378000379000379000379000379000379000379000379000379000379000379000379000379000379000379000 = true := by decide +kernel
  have replay43_12 : fastPacked 1747 (candidateList 1747 3072 256)
      0x376000376000376000376000376000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000377000 = true := by decide +kernel
  have replay43_13 : fastPacked 1747 (candidateList 1747 3328 256)
      0x376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000376000 = true := by decide +kernel
  have replay43_14 : fastPacked 1747 (candidateList 1747 3584 67)
      0x375000375000375000375000375000375000375000375000375000375000375000375000375000375000375000375000376000376000376000376000 = true := by decide +kernel
  have hs : p*p ≤ 1747^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3651 := by
    have hc : (1747^3 : ℕ).sqrt = 73019 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 15 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay43_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay43_14 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked44 {p : ℕ} (hp : p.Prime) (hlo : 2*1787 < p)
    (hhi : p^2 < 1787^3) (hmod : p%3 ≠ 1787%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1787 d = true := by
  have replay44_0 : fastPacked 1787 (candidateList 1787 0 256)
      0x4ea0e64fb0f55030fd51810f53a12f54f1415661575801705931825b61a35c71b35e31cf5fa1e464522f69b2830002bf0002500002430002310002240002120001f30001e60001b500018900017600016a = true := by decide +kernel
  have replay44_1 : fastPacked 1787 (candidateList 1787 256 256)
      0x3ea0233ed0243ee0253ee0253ef0263f00263f20273f30283f40283f50293f60293f702a3f802b3fa02c3fb02d3fc02d3fc02d3fd02e3fe02e3ff02f40003040103040203140403240503340603340703440803540a03540a03640c03740e03840f03941203a41603d41703e41903f41a04041f04342004442104542304642604842b04c42e04e43104f43205143a05643d05844005a44105b44405d44706044a06244f06645306845a06e45e07146007246607746c07c47408247608447908648008c48909348f09849109a49709f49b0a249e0a44a50aa4a90ae4ac0b14b40b74b90bb4c20c34c50c64d40d34df0dc = true := by decide +kernel
  have replay44_2 : fastPacked 1787 (candidateList 1787 512 256)
      0x3be00d3be00e3be00e3be00e3bf00e3c000e3c000e3c000e3c000e3c000f3c000f3c100f3c100f3c100f3c200f3c200f3c200f3c300f3c30103c30103c40103c40103c50103c50113c50113c60113c60113c60113c70113c70113c80123c80123c90123ca0123ca0133cb0133cb0133cc0133cc0143cc0143cd0143cd0143ce0143ce0153cf0153d00153d00153d10163d10163d10163d20163d30173d30173d40173d40173d50183d50183d60183d60183d70193d80193d901a3d901a3da01a3da01a3db01a3dc01b3dc01b3de01c3de01c3df01d3df01d3e001d3e001d3e101e3e201e3e301f3e301f3e301f3e401f3e80213e80223e9022 = true := by decide +kernel
  have replay44_3 : fastPacked 1787 (candidateList 1787 768 256)
      0x3ab0073ab0073ac0073ac0073ac0073ac0073ac0073ac0073ac0073ac0073ac0073ad0073ad0073ad0073ad0083ad0083ad0083ad0083ae0083ae0083ae0083ae0083ae0083ae0083ae0083af0083af0083af0083af0083af0083b00093b10093b10093b10093b10093b10093b20093b20093b20093b20093b30093b30093b30093b300a3b300a3b300a3b400a3b400a3b400a3b500a3b500a3b500a3b600a3b600a3b600b3b600b3b600b3b600b3b700b3b700b3b700b3b700b3b700b3b800b3b800b3b800b3b900c3b900c3b900c3ba00c3ba00c3ba00c3ba00c3bb00c3bb00c3bb00d3bb00d3bc00d3bc00d3bc00d3bc00d3bc00d3bd00d3bd00d = true := by decide +kernel
  have replay44_4 : fastPacked 1787 (candidateList 1787 1024 256)
      0x3a20043a20043a20043a20043a20043a20043a20043a20043a20043a20043a20043a20043a30053a30053a30053a30053a30053a30053a30053a40053a40053a40053a40053a40053a40053a40053a40053a40053a40053a40053a50053a50053a50053a50053a50053a50053a50053a50053a50053a60053a60053a60053a60053a60053a60063a60063a70063a70063a70063a70063a70063a70063a70063a80063a80063a80063a80063a80063a80063a80063a80063a80063a80063a90063a90063a90063a90063aa0063aa0063aa0073aa0073aa0073aa0073aa0073ab0073ab0073ab0073ab007 = true := by decide +kernel
  have replay44_5 : fastPacked 1787 (candidateList 1787 1280 256)
      0x39b00339b00339b00339b00339b00339b00339b00339b00339b00339c00339c00339c00339c00339c00339c00339c00339c00339c00339c00339c00339c00339c00339c00339c00339d00339d00339d00339d00339d00339d00339d00339d00339d00339d00339d00339d00339d00339d00339d00339d00339e00339e00339e00339e00339e00339e00339e00339e00339e00339e00339e00339e00339e00339e00439f00439f00439f00439f00439f00439f00439f00439f00439f00439f00439f00439f0043a00043a00043a00043a00043a00043a00043a00043a00043a00043a00043a00043a00043a00043a10043a10043a10043a10043a10043a10043a1004 = true := by decide +kernel
  have replay44_6 : fastPacked 1787 (candidateList 1787 1536 256)
      0x39700239700239700239700239700239700239700239700239700239700239700239700239700239700239700239700239800239800239800239800239800239800239800239800239800239800239800239800239800239800239800239800239800239800239800239800239800239900239900239900239900239900239900239900239900239900239900239900239900239900239900239900239900239900239900239900239a00239a00239a00239a00239a00239a00239a00339a00339a00339a00339a00339a00339a00339a00339a00339a00339a00339b00339b00339b00339b00339b00339b00339b00339b00339b003 = true := by decide +kernel
  have replay44_7 : fastPacked 1787 (candidateList 1787 1792 256)
      0x393001393001393001393001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001394001395001395001395001395002395002395002395002395002395002395002395002395002395002395002395002395002395002395002395002395002395002395002395002395002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002396002397002397002397002 = true := by decide +kernel
  have replay44_8 : fastPacked 1787 (candidateList 1787 2048 256)
      0x391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001392001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001393001 = true := by decide +kernel
  have replay44_9 : fastPacked 1787 (candidateList 1787 2304 256)
      0x38f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001390001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001391001 = true := by decide +kernel
  have replay44_10 : fastPacked 1787 (candidateList 1787 2560 256)
      0x38d00038d00038d00038d00038d00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00038e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138e00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f00138f001 = true := by decide +kernel
  have replay44_11 : fastPacked 1787 (candidateList 1787 2816 256)
      0x38c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d00038d000 = true := by decide +kernel
  have replay44_12 : fastPacked 1787 (candidateList 1787 3072 256)
      0x38b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c00038c000 = true := by decide +kernel
  have replay44_13 : fastPacked 1787 (candidateList 1787 3328 256)
      0x38a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b00038b000 = true := by decide +kernel
  have replay44_14 : fastPacked 1787 (candidateList 1787 3584 194)
      0x38900038900038900038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a00038a000 = true := by decide +kernel
  have hs : p*p ≤ 1787^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3778 := by
    have hc : (1787^3 : ℕ).sqrt = 75541 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 15 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay44_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay44_14 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked46 {p : ℕ} (hp : p.Prime) (hlo : 2*1867 < p)
    (hhi : p^2 < 1867^3) (hmod : p%3 ≠ 1867%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1867 d = true := by
  have replay46_0 : fastPacked 1867 (candidateList 1867 0 256)
      0x55c12457413a58014558814d5ca18b5fc1ba6291e66692246a225c6de2970002ee0002910002410002030001e40001d70001b8000199000186 = true := by decide +kernel
  have replay46_1 : fastPacked 1867 (candidateList 1867 256 256)
      0x41d02741e02841f02941f02942002942102a42202a42202b42402c42402c42502c42702e42802e42802e42a02f42d03142f03243003343103343303543503643603743703843903943a03943a03943d03b43e03b44003d44303f44303f44404044504044904344c04544c04544e04645404a45504b45704c45a04f45b04f45e05145f05246005346105446205446405546c05b46d05c46f05d47205f47506147606247906547c06747e06948206b48306c48506e48606f48907049607b4a80894ab08b4ad08d4b20914b70954c109d4c70a24c90a44cd0a74d00a94d40ad4d60af4db0b24de0b55040d65080d95190e85290f654310e54c116 = true := by decide +kernel
  have replay46_2 : fastPacked 1867 (candidateList 1867 512 256)
      0x3ec0103ec0103ed0103ed0103ed0103ee0103ee0103ef0113ef0113ef0113f00113f00113f00113f10123f10123f10123f20123f20123f20123f20123f30123f30123f40133f50133f50133f50133f50133f60143f70143f70143f80153f80153f80153f90153fb0163fb0163fb0163fb0163fc0163fc0163fc0173fc0173fd0173fe0173fe0183ff0183ff01840001940101940201940201a40301a40301a40301a40401a40401b40601b40601c40701c40701c40801c40801c40901d40b01e40c01e40c01e40d01f40e02040f02041002141102141102141302241302241402241602441702441802541902541902641a02641b02641c027 = true := by decide +kernel
  have replay46_3 : fastPacked 1867 (candidateList 1867 768 256)
      0x3d80083d80083d90083d90083d90083d90093d90093da0093da0093da0093da0093da0093db0093db0093db0093db0093dc0093dc00a3dc00a3dd00a3dd00a3dd00a3dd00a3dd00a3de00a3de00a3de00a3de00a3de00a3df00a3df00a3df00b3df00b3e000b3e000b3e000b3e000b3e100b3e100b3e100b3e100b3e200c3e200c3e200c3e200c3e300c3e300c3e300c3e300c3e400c3e400c3e400c3e400d3e500d3e500d3e500d3e500d3e600d3e600d3e600d3e600d3e700d3e700e3e800e3e800e3e800e3e800e3e900e3e900e3e900e3ea00f3ea00f3ea00f3ea00f3ea00f3eb00f3eb00f3eb00f3ec00f3ec00f = true := by decide +kernel
  have replay46_4 : fastPacked 1867 (candidateList 1867 1024 256)
      0x3cd0053cd0053cd0053cd0053cd0053cd0053cd0053cd0053cd0053cd0053ce0053ce0053ce0053ce0053ce0053ce0053ce0053cf0053cf0053cf0053cf0053cf0053cf0063cf0063cf0063cf0063d00063d00063d00063d00063d00063d00063d00063d00063d00063d00063d10063d10063d10063d10063d10063d20063d20063d20063d20063d20063d20063d20063d20063d20063d30073d30073d30073d30073d30073d30073d30073d30073d40073d40073d40073d40073d50073d50073d50073d50073d50073d50073d50073d50073d60073d60073d60073d60083d60083d60083d70083d70083d70083d70083d70083d70083d70083d80083d80083d80083d8008 = true := by decide +kernel
  have replay46_5 : fastPacked 1867 (candidateList 1867 1280 256)
      0x3c60033c60033c60033c60033c60033c60033c60033c60033c60033c60033c60033c70033c70033c70033c70033c70033c70033c70033c70043c70043c70043c70043c70043c70043c70043c80043c80043c80043c80043c80043c80043c80043c80043c80043c80043c80043c80043c80043c80043c80043c90043c90043c90043c90043c90043c90043c90043c90043c90043c90043c90043c90043c90043c90043ca0043ca0043ca0043ca0043ca0043ca0043ca0043ca0043cb0043cb0043cb0043cb0043cb0043cb0043cb0043cb0043cb0053cb0053cb0053cc0053cc0053cc0053cc0053cc0053cc0053cc0053cc0053cc0053cc0053cd0053cd0053cd005 = true := by decide +kernel
  have replay46_6 : fastPacked 1867 (candidateList 1867 1536 256)
      0x3c10023c10023c10023c10023c10023c10023c10023c10023c10023c10023c10023c10023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c20023c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c30033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c40033c50033c50033c50033c50033c50033c50033c50033c50033c50033c50033c50033c50033c50033c60033c60033c6003 = true := by decide +kernel
  have replay46_7 : fastPacked 1867 (candidateList 1867 1792 256)
      0x3bd0023bd0023bd0023bd0023bd0023bd0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023be0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023bf0023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c00023c10023c10023c10023c10023c10023c1002 = true := by decide +kernel
  have replay46_8 : fastPacked 1867 (candidateList 1867 2048 256)
      0x3bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bb0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bc0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0013bd0023bd0023bd0023bd0023bd0023bd0023bd002 = true := by decide +kernel
  have replay46_9 : fastPacked 1867 (candidateList 1867 2304 256)
      0x3b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013b90013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013ba0013bb0013bb0013bb0013bb0013bb0013bb001 = true := by decide +kernel
  have replay46_10 : fastPacked 1867 (candidateList 1867 2560 256)
      0x3b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b80013b9001 = true := by decide +kernel
  have replay46_11 : fastPacked 1867 (candidateList 1867 2816 256)
      0x3b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60003b60013b60013b60013b60013b60013b60013b60013b60013b60013b60013b60013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b70013b7001 = true := by decide +kernel
  have replay46_12 : fastPacked 1867 (candidateList 1867 3072 256)
      0x3b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b50003b5000 = true := by decide +kernel
  have replay46_13 : fastPacked 1867 (candidateList 1867 3328 256)
      0x3b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b40003b4000 = true := by decide +kernel
  have replay46_14 : fastPacked 1867 (candidateList 1867 3584 256)
      0x3b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b30003b3000 = true := by decide +kernel
  have replay46_15 : fastPacked 1867 (candidateList 1867 3840 194)
      0x3b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b20003b2000 = true := by decide +kernel
  have hs : p*p ≤ 1867^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4034 := by
    have hc : (1867^3 : ℕ).sqrt = 80670 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 16 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay46_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay46_15 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked47 {p : ℕ} (hp : p.Prime) (hlo : 2*1907 < p)
    (hhi : p^2 < 1907^3) (hmod : p%3 ≠ 1907%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1907 d = true := by
  have replay47_0 : fastPacked 1907 (candidateList 1907 0 256)
      0x5931425b015d5be16a5e318d62b1d165d2026a62490003150003030002e40002d70002c50002b800029900028700025c0001ec0001df0001cd0001c00001ad00018e000182 = true := by decide +kernel
  have replay47_1 : fastPacked 1907 (candidateList 1907 256 256)
      0x43802b43b02d43c02e43d02e43f02f44003044203144403244403244503344703444803544903544b03744d03844d03844e03944f03945003a45203b45303b45403c45503d45803f45904045a04045c04145d04245f04345f04446104546404746504746804a46d04d47004f47104f47305147905547a05647b05747e05948205c48806048c06348f06549106649b06e49e0704a20734a30744a70774ab07a4af07d4b60834bb0864c408e4c90924cb0944d409b4dc0a14e60a94e90ac4ed0af4f60b75020c150b0c850e0cb5170d351c0d85200db52a0e35300e95350ed5400f75470fd55410955910d571123581132 = true := by decide +kernel
  have replay47_2 : fastPacked 1907 (candidateList 1907 512 256)
      0x40301140401140401140401140601240601240601240601240601240701240701240701240801240801240801340901340901340901340a01340a01340b01440b01440c01440c01540d01540d01540d01540e01540e01540f01640f01641001641001641201741201741301741301841401841401841501841501941601941701941701a41801a41901a41901b41a01b41a01b41b01b41b01c41d01c41d01c41e01d41e01d41f01e42001e42001e42001e42101f42302042402042402042502042502142602142702242802242a02342a02342a02342b02442c02442d02542d02542f02642f02643002643002743102743502a43602a43602a = true := by decide +kernel
  have replay47_3 : fastPacked 1907 (candidateList 1907 768 256)
      0x3ee0093ee0093ee0093ef0093ef0093ef0093ef0093ef0093ef0093ef0093ef0093f00093f00093f00093f00093f00093f00093f100a3f100a3f100a3f100a3f100a3f100a3f100a3f200a3f200a3f200a3f200a3f200a3f300a3f400b3f400b3f400b3f500b3f500b3f500b3f500b3f600b3f600b3f600b3f600c3f700c3f700c3f700c3f700c3f800c3f800c3f800c3f800c3f900c3f900c3f900d3fa00d3fa00d3fa00d3fb00d3fb00d3fb00d3fb00d3fb00d3fb00d3fc00e3fc00e3fd00e3fd00e3fd00e3fd00e3fe00e3fe00f3ff00f3ff00f3ff00f3ff00f40000f40000f401010401010401010402010402010402010402010403010403011 = true := by decide +kernel
  have replay47_4 : fastPacked 1907 (candidateList 1907 1024 256)
      0x3e30053e30053e30053e30053e30053e30053e30063e30063e40063e40063e40063e40063e40063e40063e40063e40063e40063e40063e50063e50063e50063e50063e50063e50063e60063e60063e60063e60063e60063e60063e60063e60063e60063e70063e70063e70063e70073e70073e70073e70073e80073e80073e80073e80073e80073e80073e90073e90073e90073e90073e90073e90073e90073ea0073ea0073ea0073ea0073ea0073ea0073ea0083ea0083eb0083eb0083eb0083eb0083eb0083ec0083ec0083ec0083ec0083ec0083ed0083ed0083ed0083ed0083ed0083ed0083ee009 = true := by decide +kernel
  have replay47_5 : fastPacked 1907 (candidateList 1907 1280 256)
      0x3db0033db0033db0033db0033db0043dc0043dc0043dc0043dc0043dc0043dc0043dc0043dc0043dc0043dc0043dc0043dc0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043dd0043de0043de0043de0043de0043de0043de0043de0043de0043de0043de0043de0043de0043de0043df0043df0043df0043df0043df0043df0043df0043df0043df0043df0043df0043e00043e00043e00053e00053e00053e00053e00053e00053e00053e00053e00053e00053e10053e10053e10053e10053e10053e10053e10053e10053e10053e10053e20053e20053e20053e20053e20053e20053e20053e2005 = true := by decide +kernel
  have replay47_6 : fastPacked 1907 (candidateList 1907 1536 256)
      0x3d60023d60023d60023d70023d70023d70023d70023d70023d70023d70023d70023d70033d70033d70033d70033d70033d70033d70033d70033d70033d70033d70033d70033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d80033d90033d90033d90033d90033d90033d90033d90033d90033d90033d90033d90033d90033d90033d90033d90033d90033da0033da0033da0033da0033da0033da0033da0033da0033da0033da0033da0033da0033da0033da0033db0033db0033db0033db0033db0033db0033db0033db0033db0033db0033db003 = true := by decide +kernel
  have replay47_7 : fastPacked 1907 (candidateList 1907 1792 256)
      0x3d20023d20023d20023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d30023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d40023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d50023d60023d60023d60023d60023d60023d60023d60023d60023d60023d60023d60023d60023d6002 = true := by decide +kernel
  have replay47_8 : fastPacked 1907 (candidateList 1907 2048 256)
      0x3d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d00013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10013d10023d10023d10023d10023d10023d10023d10023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d20023d2002 = true := by decide +kernel
  have replay47_9 : fastPacked 1907 (candidateList 1907 2304 256)
      0x3cd0013cd0013cd0013cd0013cd0013cd0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013ce0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013cf0013d0001 = true := by decide +kernel
  have replay47_10 : fastPacked 1907 (candidateList 1907 2560 256)
      0x3cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cc0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd0013cd001 = true := by decide +kernel
  have replay47_11 : fastPacked 1907 (candidateList 1907 2816 256)
      0x3ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0013ca0013ca0013ca0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cb0013cc001 = true := by decide +kernel
  have replay47_12 : fastPacked 1907 (candidateList 1907 3072 256)
      0x3c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca0003ca000 = true := by decide +kernel
  have replay47_13 : fastPacked 1907 (candidateList 1907 3328 256)
      0x3c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c90003c9000 = true := by decide +kernel
  have replay47_14 : fastPacked 1907 (candidateList 1907 3584 256)
      0x3c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c80003c8000 = true := by decide +kernel
  have replay47_15 : fastPacked 1907 (candidateList 1907 3840 256)
      0x3c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c70003c7000 = true := by decide +kernel
  have replay47_16 : fastPacked 1907 (candidateList 1907 4096 68)
      0x3c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c60003c6000 = true := by decide +kernel
  have hs : p*p ≤ 1907^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4164 := by
    have hc : (1907^3 : ℕ).sqrt = 83277 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 17 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay47_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay47_16 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked49 {p : ℕ} (hp : p.Prime) (hlo : 2*1987 < p)
    (hhi : p^2 < 1987^3) (hmod : p%3 ≠ 1987%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 1987 d = true := by
  have replay49_0 : fastPacked 1987 (candidateList 1987 0 256)
      0x62e1a865f1d867a1f168d2040003320003060002e70002c80002b60002aa00028b00022d0001dd00019e = true := by decide +kernel
  have replay49_1 : fastPacked 1987 (candidateList 1987 256 256)
      0x46c03146d03146e03246f03347003347103447203447303547403647503647603747803847903947a03947c03b48003d48203f48303f48404048704248904348a04448c04548e04648f04749004849204949404a49604c49a04e49b04f49c05049d0504a10534a50564a60564a70574af05d4b005e4b20604b70634b80644bb0664bd0674be0684c00694c106a4c306c4cd0734ce0744d00764d40784d807b4d907d4dd0804e10834e40854e80884ea0894ed08c4ef08d4f208f50309d51a0b051e0b45210b65280bc52f0c253b0cc5440d35470d654c0db5500de5560e355a0e65600eb5640ef59c1215a21265bb13e5d515560117e61118d = true := by decide +kernel
  have replay49_2 : fastPacked 1987 (candidateList 1987 512 256)
      0x43201343301343301343301343401443401443501443601443601543601543701543701543701543801543801643901643901643901643a01643a01643a01743b01743c01743d01843d01843d01843d01843e01843f01943f01944001944101a44101a44201a44301b44401b44401b44401b44501b44501c44501c44501c44601c44701d44801d44801d44901e44a01e44a01e44c01f44d01f44d02044e02044e02044f02044f02145102145102245202245202245302345302345502445702545802545802545a02645b02745c02845d02845e02945e02946002a46102a46102b46402c46502d46702e46702e46802e46802f46902f46b030 = true := by decide +kernel
  have replay49_3 : fastPacked 1987 (candidateList 1987 768 256)
      0x41b00a41c00a41c00a41c00a41c00a41c00a41d00b41d00b41d00b41d00b41e00b41e00b41e00b41f00b41f00b41f00b42000c42000c42000c42000c42000c42100c42100c42100c42200c42200c42200d42200d42300d42300d42300d42300d42400d42400d42400d42400d42500d42500e42500e42500e42600e42700e42700e42700e42700e42700e42800f42800f42800f42900f42900f42900f42a00f42a00f42a01042a01042b01042b01042b01042c01042c01042c01042d01142d01142e01142e01142e01142e01142f01242f012430012430012430012430012431012431012431013432013432013432013 = true := by decide +kernel
  have replay49_4 : fastPacked 1987 (candidateList 1987 1024 256)
      0x40e00640e00640e00640f00640f00640f00640f00640f00640f00640f00640f00640f00640f00641000741000741000741000741000741000741100741100741100741100741100741100741100741100741100741200741200741200741200741200741200741200741200741300741300741300841300841400841400841400841400841400841400841400841500841500841500841500841500841500841600841600841600841600841600841600841700941700941700941700941700941800941800941800941800941800941800941800941800941900941900941900941900941900941a00a41a00a41a00a41a00a41a00a41a00a41b00a41b00a41b00a41b00a = true := by decide +kernel
  have replay49_5 : fastPacked 1987 (candidateList 1987 1280 256)
      0x40600440600440600440600440700440700440700440700440700440700440700440700440700440700440700440700440700440800440800440800440800440800440800440800440800440800440800440800440800540800540800540900540900540900540900540900540900540900540900540900540900540900540a00540a00540a00540a00540a00540a00540a00540a00540a00540a00540a00540a00540b00540b00540b00540b00540b00540b00540b00540b00540c00540c00540c00540c00540c00540c00540c00540c00640d00640d00640d00640d00640d00640d00640d00640d00640d00640d00640e00640e00640e00640e00640e00640e006 = true := by decide +kernel
  have replay49_6 : fastPacked 1987 (candidateList 1987 1536 256)
      0x401003401003401003401003401003401003401003401003401003401003401003401003401003401003401003401003401003401003402003402003402003402003402003402003402003402003402003402003402003402003402003402003402003402003402003402003403003403003403003403003403003403003403003403003403003403003403003403003403003403003403003404003404003404003404003404003404003404003404003404004404004404004404004404004404004404004405004405004405004405004405004405004405004405004405004405004405004405004405004405004406004406004406004406004406004 = true := by decide +kernel
  have replay49_7 : fastPacked 1987 (candidateList 1987 1792 256)
      0x3fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fd0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023fe0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0023ff0033ff0033ff003400003400003400003400003400003400003400003400003400003400003400003400003400003400003400003400003400003401003 = true := by decide +kernel
  have replay49_8 : fastPacked 1987 (candidateList 1987 2048 256)
      0x3fa0013fa0013fa0013fa0013fa0013fa0013fa0013fa0013fa0013fa0013fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fa0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fb0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc0023fc002 = true := by decide +kernel
  have replay49_9 : fastPacked 1987 (candidateList 1987 2304 256)
      0x3f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f80013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f90013f9001 = true := by decide +kernel
  have replay49_10 : fastPacked 1987 (candidateList 1987 2560 256)
      0x3f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f60013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f70013f7001 = true := by decide +kernel
  have replay49_11 : fastPacked 1987 (candidateList 1987 2816 256)
      0x3f30013f30013f30013f30013f30013f30013f30013f30013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f40013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f50013f5001 = true := by decide +kernel
  have replay49_12 : fastPacked 1987 (candidateList 1987 3072 256)
      0x3f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30003f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f30013f3001 = true := by decide +kernel
  have replay49_13 : fastPacked 1987 (candidateList 1987 3328 256)
      0x3f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f20003f2000 = true := by decide +kernel
  have replay49_14 : fastPacked 1987 (candidateList 1987 3584 256)
      0x3f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f10003f1000 = true := by decide +kernel
  have replay49_15 : fastPacked 1987 (candidateList 1987 3840 256)
      0x3ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f00003f0000 = true := by decide +kernel
  have replay49_16 : fastPacked 1987 (candidateList 1987 4096 256)
      0x3ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef0003ef000 = true := by decide +kernel
  have replay49_17 : fastPacked 1987 (candidateList 1987 4352 77)
      0x3ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee0003ee000 = true := by decide +kernel
  have hs : p*p ≤ 1987^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4429 := by
    have hc : (1987^3 : ℕ).sqrt = 88572 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 18 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay49_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay49_17 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked50 {p : ℕ} (hp : p.Prime) (hlo : 2*2027 < p)
    (hhi : p^2 < 2027^3) (hmod : p%3 ≠ 2027%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 2027 d = true := by
  have replay50_0 : fastPacked 2027 (candidateList 2027 0 256)
      0x67e1df6c12206e72457932ee00030e0002ef0002d10002b200029f0002800002740002610002550002350002230001f7 = true := by decide +kernel
  have replay50_1 : fastPacked 2027 (candidateList 2027 256 256)
      0x48803548c03748d03848e03949003a49203b49403c49603e49703e49803f49a04049b04149d0424a00444a10454a20454a30464a40474a50474a70494a804a4a904a4ab04c4ae04e4b004f4b10504b30514b50524b70534b80544ba0564be0584bf0594c305c4c90604cb0624cd0634d00654d706a4d906c4da06d4dd06f4e30734ea0784ef07c4f307f4f508150208b50608e50b09250d09351109751709b51c0a05250a752b0ac5370b653e0bc5410be54c0c85570d15650dd5680e056e0e457b0f058c0ff59810a59d10e5aa1195b21215b71265c61335d013c5d71425e81525f415d60917061217963b19f6591bc = true := by decide +kernel
  have replay50_2 : fastPacked 2027 (candidateList 2027 512 256)
      0x44a01444a01444b01544b01544d01544d01644d01644d01644e01644e01644e01644e01644f01644f01745001745001745001745101745201845201845301845401945401945501945501945501945601a45601a45701a45701a45801b45801b45901b45b01c45b01c45c01d45c01d45d01d45e01e45e01e45f01e46001f46001f46101f46302046302046402146502146502146502146602246802346802346902346a02446b02446b02446b02546c02546d02646f02747002747002747102847102847202847402947502a47702b47802b47802c47802c47a02d47b02d47c02e47d02f47e02f47e02f47f030480030485033486034486034 = true := by decide +kernel
  have replay50_3 : fastPacked 2027 (candidateList 2027 768 256)
      0x43100b43200b43200b43200b43200b43200b43200b43200b43300b43300b43300b43300b43300b43300b43400b43400b43400c43400c43500c43500c43500c43500c43500c43500c43500c43600c43600c43600c43600c43700c43800d43800d43900d43900d43900d43a00e43a00e43a00e43a00e43b00e43b00e43b00e43c00e43c00e43c00f43c00f43d00f43d00f43d00f43e00f43e00f43e00f43f01043f01044001044001044001044001044101044101044101044101044201144201144301144301144301144401244401244501244501244501244501244601344601344701344701344801344801344801344801444901444a01444a014 = true := by decide +kernel
  have replay50_4 : fastPacked 2027 (candidateList 2027 1024 256)
      0x42400742400742500742500742500742500742500742500742500742500742500742600742600742600742600742600742600742600742700742700742700742700742700742700742800742800842800842800842800842800842800842900842900842900842900842900842900842900842a00842a00842a00842a00842a00842a00842b00842b00842b00942b00942b00942b00942b00942c00942c00942c00942c00942d00942d00942d00942d00942d00942d00942d00942d00942e00942e00a42e00a42f00a42f00a42f00a42f00a43000a43000a43000a43000a43000a43100a43100a43100b = true := by decide +kernel
  have replay50_5 : fastPacked 2027 (candidateList 2027 1280 256)
      0x41c00441c00441c00441c00441c00441c00441c00441c00441c00441c00441c00441d00441d00441d00541d00541d00541d00541d00541d00541d00541d00541d00541e00541e00541e00541e00541e00541e00541e00541e00541e00541e00541e00541e00541f00541f00541f00541f00541f00541f00541f00541f00541f00541f00541f005420005420005420005420005420005420005420005420005420005420005421005421006421006421006421006421006421006421006421006421006421006422006422006422006422006422006422006422006423006423006423006423006423006423006423006423006423006424006424006424006424006 = true := by decide +kernel
  have replay50_6 : fastPacked 2027 (candidateList 2027 1536 256)
      0x41600341600341600341600341600341600341700341700341700341700341700341700341700341700341700341700341700341700341700341700341700341700341700341700341700341800341800341800341800341800341800341800341800341800341800341800341800341800441800441900441900441900441900441900441900441900441900441900441900441900441900441900441900441900441a00441a00441a00441a00441a00441a00441a00441a00441a00441a00441a00441a00441b00441b00441b00441b00441b00441b00441b00441b00441b00441b00441b00441b00441b00441b00441c00441c004 = true := by decide +kernel
  have replay50_7 : fastPacked 2027 (candidateList 2027 1792 256)
      0x412002412002412002412002412002412002412002412002412002412002412002412002412002412002412002412002412002412002412002413002413002413002413002413002413002413002413002413002413002413002413002413002413002413002413002413002413002413002414002414002414003414003414003414003414003414003414003414003414003414003414003414003414003414003414003414003414003414003415003415003415003415003415003415003415003415003415003415003415003415003415003415003415003415003415003415003416003416003416003416003416003416003416003 = true := by decide +kernel
  have replay50_8 : fastPacked 2027 (candidateList 2027 2048 256)
      0x40e00240e00240e00240e00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f00240f002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002410002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002411002412002412002 = true := by decide +kernel
  have replay50_9 : fastPacked 2027 (candidateList 2027 2304 256)
      0x40c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140d00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00140e00240e00240e00240e00240e00240e00240e00240e00240e00240e002 = true := by decide +kernel
  have replay50_10 : fastPacked 2027 (candidateList 2027 2560 256)
      0x40a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140b00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c00140c001 = true := by decide +kernel
  have replay50_11 : fastPacked 2027 (candidateList 2027 2816 256)
      0x40800140800140800140800140800140800140800140800140800140800140800140800140800140800140800140800140800140800140800140800140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140900140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a00140a001 = true := by decide +kernel
  have replay50_12 : fastPacked 2027 (candidateList 2027 3072 256)
      0x407000407000407000407000407000407000407000407000407000407000407000407000407000407000407000407000407000407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001407001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001408001 = true := by decide +kernel
  have replay50_13 : fastPacked 2027 (candidateList 2027 3328 256)
      0x405000405000405000405000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000406000407000407000407000407000407000407000407000407000407000407000407000 = true := by decide +kernel
  have replay50_14 : fastPacked 2027 (candidateList 2027 3584 256)
      0x404000404000404000404000404000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000405000 = true := by decide +kernel
  have replay50_15 : fastPacked 2027 (candidateList 2027 3840 256)
      0x404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000404000 = true := by decide +kernel
  have replay50_16 : fastPacked 2027 (candidateList 2027 4096 256)
      0x403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000404000404000404000 = true := by decide +kernel
  have replay50_17 : fastPacked 2027 (candidateList 2027 4352 212)
      0x402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000402000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000403000 = true := by decide +kernel
  have hs : p*p ≤ 2027^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4564 := by
    have hc : (2027^3 : ℕ).sqrt = 91260 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 18 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay50_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay50_17 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked56 {p : ℕ} (hp : p.Prime) (hlo : 2*2267 < p)
    (hhi : p^2 < 2267^3) (hmod : p%3 ≠ 2267%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 2267 d = true := by
  have replay56_0 : fastPacked 2267 (candidateList 2267 0 256)
      0x2ee0002c30002b00002850002460002270002080001e90001d6 = true := by decide +kernel
  have replay56_1 : fastPacked 2267 (candidateList 2267 256 256)
      0x52f04e53505253705353705453a05653c05753f05954305b54405c54605e54805f54a06154d06255106555306755406755606955706955806a55c06d55e06e55f06f56107156607556907756a07856d07a56f07b57307e57407f57708157d08557e08758408b58e09259209559409759909b5a30a35a60a65a80a75ad0ab5b60b25c10bb5c90c25cf0c75d30ca5e80db5ef0e25f70e85fa0eb6030f260b0fa61510262410f62f11964612d65313865813d66f1526851666a21806aa1876b61936d61b07011d97201f772f20575722b77324778825b7cb29c8022d283630500039b00038900036a00035d00032c00030d = true := by decide +kernel
  have replay56_2 : fastPacked 2267 (candidateList 2267 512 256)
      0x4da01d4db01e4db01e4dc01e4de01f4de01f4de01f4df01f4df0204df0204e00204e00204e10204e10214e20214e20214e30214e40224e40224e50224e70234e70244e70244e80244e90244e90254ea0254ea0254eb0264ec0264ed0274ed0274ee0284f00294f10294f202a4f302a4f402b4f502b4f502b4f602c4f802c4f802d4f902d4fb02e4fc02f4fd02f4fe0304ff0304ff03150003150203250303350403450503450603550703550703550803650a03750d03950e03950e03a50f03a50f03a51103b51303c51403d51703f51803f51904051904051b04251c04251e04352004452104552104552204652404752b04b52c04c52c04c = true := by decide +kernel
  have replay56_3 : fastPacked 2267 (candidateList 2267 768 256)
      0x4ba00f4ba00f4ba00f4ba0104ba0104bb0104bb0104bb0104bb0104bb0104bc0104bc0104bc0104bc0104bd0104bd0104bd0114bd0114be0114be0114be0114be0114bf0114bf0114bf0114bf0124c00124c00124c00124c10124c20134c30134c30134c40134c40134c40144c50144c50144c50144c60144c60144c70154c70154c70154c80154c80154c80154c90154c90154ca0164ca0164cb0164cc0174cc0174cc0174cd0174cd0174cd0174ce0184ce0184ce0184ce0184cf0184d00194d00194d00194d10194d20194d301a4d301a4d401a4d401a4d401a4d501b4d501b4d601b4d601c4d701c4d701c4d801c4d801c4d801c4da01d4da01d = true := by decide +kernel
  have replay56_4 : fastPacked 2267 (candidateList 2267 1024 256)
      0x4a90094a90094a900a4a900a4aa00a4aa00a4aa00a4aa00a4aa00a4aa00a4aa00a4aa00a4aa00a4ab00a4ab00a4ab00a4ab00a4ab00a4ac00a4ac00b4ac00b4ac00b4ad00b4ad00b4ad00b4ad00b4ad00b4ae00b4ae00b4ae00b4ae00b4ae00b4ae00b4af00b4af00b4af00b4af00c4af00c4b000c4b000c4b000c4b000c4b000c4b100c4b100c4b100c4b200c4b200c4b200c4b200c4b200d4b200d4b300d4b300d4b300d4b300d4b400d4b400d4b400d4b400d4b400d4b400d4b500d4b500e4b500e4b600e4b600e4b700e4b700e4b700e4b700e4b800f4b800f4b800f4b800f4b900f4b900f4b900f = true := by decide +kernel
  have replay56_5 : fastPacked 2267 (candidateList 2267 1280 256)
      0x49e00649e00649e00649e00649e00649e00649e00649e00649e00649e00649f00649f00749f00749f00749f00749f00749f0074a00074a00074a00074a00074a00074a00074a00074a00074a00074a00074a10074a10074a10074a10074a10074a10074a10074a10074a10074a10074a10074a10074a20074a20074a20074a20084a20084a20084a30084a30084a30084a30084a30084a30084a30084a30084a30084a40084a40084a40084a40084a40084a40084a50084a50084a50084a50084a50084a50084a50084a50084a60094a60094a60094a60094a60094a70094a70094a70094a70094a70094a70094a70094a70094a80094a80094a80094a80094a8009 = true := by decide +kernel
  have replay56_6 : fastPacked 2267 (candidateList 2267 1536 256)
      0x49600449600449700449700549700549700549700549700549700549700549700549700549700549700549700549800549800549800549800549800549800549800549800549800549800549800549800549800549900549900549900549900549900549900549900549900549900549900549a00549a00549a00549a00549a00549a00549a00549a00549a00549a00549a00549b00549b00549b00549b00549b00549b00649b00649b00649b00649b00649b00649b00649b00649c00649c00649c00649c00649c00649c00649c00649c00649d00649d00649d00649d00649d00649d00649d00649d00649d00649d00649d00649e006 = true := by decide +kernel
  have replay56_7 : fastPacked 2267 (candidateList 2267 1792 256)
      0x491003491003491003491003491003491003491003491003491003491003491003491003491003491003492003492003492003492003492003492003492003492003492003492003492003492004492004492004492004492004492004493004493004493004493004493004493004493004493004493004493004493004493004494004494004494004494004494004494004494004494004494004494004494004494004494004494004494004494004494004495004495004495004495004495004495004495004495004495004495004495004495004496004496004496004496004496004496004496004496004496004496004496004 = true := by decide +kernel
  have replay56_8 : fastPacked 2267 (candidateList 2267 2048 256)
      0x48d00248d00248d00248d00248d00248d00248d00248d00248d00248d00248d00248d00248d00248d00348d00348d00348d00348d00348d00348d00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348e00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f00348f003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003490003491003491003491003 = true := by decide +kernel
  have replay56_9 : fastPacked 2267 (candidateList 2267 2304 256)
      0x48900248900248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248a00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248b00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248c00248d00248d002 = true := by decide +kernel
  have replay56_10 : fastPacked 2267 (candidateList 2267 2560 256)
      0x487001487001487001487001487001487001487001487001487001487001487001487001487001487001487001487001487001487001487001487001487002487002487002487002487002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002488002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002489002 = true := by decide +kernel
  have replay56_11 : fastPacked 2267 (candidateList 2267 2816 256)
      0x485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001485001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001486001487001487001487001487001487001487001487001487001487001487001487001487001487001 = true := by decide +kernel
  have replay56_12 : fastPacked 2267 (candidateList 2267 3072 256)
      0x483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001484001485001485001485001485001485001485001485001 = true := by decide +kernel
  have replay56_13 : fastPacked 2267 (candidateList 2267 3328 256)
      0x481001481001481001481001481001481001481001481001481001481001481001481001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001482001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001483001 = true := by decide +kernel
  have replay56_14 : fastPacked 2267 (candidateList 2267 3584 256)
      0x480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001480001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001481001 = true := by decide +kernel
  have replay56_15 : fastPacked 2267 (candidateList 2267 3840 256)
      0x47f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480000480001480001480001480001480001480001480001480001480001480001480001 = true := by decide +kernel
  have replay56_16 : fastPacked 2267 (candidateList 2267 4096 256)
      0x47e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f00047f000 = true := by decide +kernel
  have replay56_17 : fastPacked 2267 (candidateList 2267 4352 256)
      0x47d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e00047e000 = true := by decide +kernel
  have replay56_18 : fastPacked 2267 (candidateList 2267 4608 256)
      0x47c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d00047d000 = true := by decide +kernel
  have replay56_19 : fastPacked 2267 (candidateList 2267 4864 256)
      0x47b00047b00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c00047c000 = true := by decide +kernel
  have replay56_20 : fastPacked 2267 (candidateList 2267 5120 256)
      0x47b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b00047b000 = true := by decide +kernel
  have replay56_21 : fastPacked 2267 (candidateList 2267 5376 21)
      0x47b00047b00047b00047b00047b00047b00047b00047b00047b000 = true := by decide +kernel
  have hs : p*p ≤ 2267^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 5397 := by
    have hc : (2267^3 : ℕ).sqrt = 107938 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 22 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay56_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay56_21 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked58 {p : ℕ} (hp : p.Prime) (hlo : 2*2347 < p)
    (hhi : p^2 < 2347^3) (hmod : p%3 ≠ 2347%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 2347 d = true := by
  have replay58_0 : fastPacked 2347 (candidateList 2347 0 256)
      0x2a10002760002630002560002050001da = true := by decide +kernel
  have replay58_1 : fastPacked 2347 (candidateList 2347 256 256)
      0x56705756905856b05956c05a56e05c56f05c57105e57205f57506157606257706257c06557d06657e06758206a58806e58d07158e07259007359507759907b59b07c59e07e5a20815a30825a50835aa0875ac0885b108c5b70905b80925ba0935bc0955c409b5cb0a05cd0a25cf0a45de0af5e00b05e50b55ed0bc5ef0bd5f50c25f90c55fb0c75ff0ca6010cc6050cf6190e061c0e26200e66280ec6300f36330f663c0fd64510564a10a65411265811665e11b66211f6691246921496d11826dc18c6e31936f81a670f1bc7391e375820076520d77b22278b2327a624b7b925e7da27e7f429700037a00036e00033c0003110002d30002c0 = true := by decide +kernel
  have replay58_2 : fastPacked 2347 (candidateList 2347 512 256)
      0x50b02150c02150c02150c02250e02250e02250f02351002351102451102451202451202451302551402551402551502651502651602651602751702751702751802751902851b02951b02951c02951c02951e02a51e02b51f02b52102c52102c52202d52302d52602f52602f52702f52702f52703052803052803052903152a03152b03252d03352d03352e03453003553103553403753403753503853603853603853703953803953a03b53b03b53c03c53d03c53e03d53e03d54103f54504154604254604254904454a04554d04654e04755004855004855304a55404b55504b55904e55b04f55f05155f052560053561053563054566056 = true := by decide +kernel
  have replay58_3 : fastPacked 2347 (candidateList 2347 768 256)
      0x4e90114e90124e90124e90124ea0124ea0124ea0124eb0124eb0134ec0134ec0134ec0134ed0134ed0134ed0134ee0134ef0144ef0144f00144f00144f00154f10154f10154f10154f20154f20164f30164f30164f30164f40164f40164f40164f50174f50174f60174f60174f60174f70184f70184f70184f80184f90184fa0194fa0194fa0194fa0194fb0194fb0194fc01a4fc01a4fd01a4fd01a4fe01b4fe01b4ff01b4ff01b4ff01b50001c50001c50101c50101c50101c50301d50301d50401d50401d50501e50501e50601e50601e50701f50701f50801f50801f50801f50902050a02050a02050a02050b021 = true := by decide +kernel
  have replay58_4 : fastPacked 2347 (candidateList 2347 1024 256)
      0x4d500a4d500b4d500b4d600b4d600b4d600b4d600b4d600b4d600b4d600b4d600b4d700b4d700b4d700b4d700b4d800b4d800b4d800c4d800c4d800c4d800c4d900c4d900c4d900c4d900c4da00c4da00c4da00c4da00c4da00c4db00c4db00c4db00c4db00d4db00d4db00d4dc00d4dc00d4dd00d4dd00d4dd00d4dd00d4dd00d4dd00d4dd00d4de00d4de00e4de00e4de00e4df00e4df00e4df00e4e000e4e000e4e000e4e000e4e000e4e000e4e100f4e200f4e200f4e200f4e200f4e300f4e300f4e300f4e300f4e300f4e40104e40104e40104e40104e40104e50104e50104e50104e60104e60104e60114e70114e70114e70114e70114e70114e70114e80114e8011 = true := by decide +kernel
  have replay58_5 : fastPacked 2347 (candidateList 2347 1280 256)
      0x4c90074c90074c90074ca0074ca0074ca0074ca0074ca0074ca0074ca0074ca0074cb0074cb0074cb0074cb0074cb0084cb0084cb0084cc0084cc0084cc0084cc0084cc0084cc0084cc0084cc0084cc0084cc0084cc0084cd0084cd0084cd0084cd0084cd0084cd0084cd0084cd0084cd0084ce0084ce0084ce0084ce0084ce0084ce0084ce0084cf0094cf0094cf0094cf0094cf0094cf0094cf0094cf0094cf0094d00094d00094d00094d00094d00094d10094d10094d10094d10094d10094d10094d20094d20094d200a4d200a4d200a4d200a4d300a4d300a4d300a4d300a4d300a4d300a4d400a4d400a4d400a4d400a4d400a4d400a4d500a4d500a4d500a = true := by decide +kernel
  have replay58_6 : fastPacked 2347 (candidateList 2347 1536 256)
      0x4c10054c10054c10054c10054c20054c20054c20054c20054c20054c20054c20054c20054c20054c20054c20054c20054c20054c20054c30054c30054c30054c30054c30054c30054c30054c30054c30054c30054c30054c30054c30054c40054c40064c40064c40064c40064c40064c40064c40064c40064c40064c40064c40064c50064c50064c50064c50064c50064c50064c50064c50064c50064c60064c60064c60064c60064c60064c60064c60064c60064c60064c60064c60064c70064c70064c70064c70064c70064c70064c70064c70064c70074c70074c80074c80074c80074c80074c80074c80074c80074c90074c90074c90074c90074c9007 = true := by decide +kernel
  have replay58_7 : fastPacked 2347 (candidateList 2347 1792 256)
      0x4bb0044bb0044bb0044bb0044bb0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bc0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044bd0044be0044be0044be0044be0044be0044be0044be0044be0044be0044be0044be0044be0044be0044be0044bf0044bf0044bf0044bf0044bf0044bf0044bf0044bf0044bf0044bf0044bf0044bf0054bf0054c00054c00054c00054c00054c00054c00054c00054c00054c00054c00054c00054c00054c00054c10054c10054c10054c10054c10054c1005 = true := by decide +kernel
  have replay58_8 : fastPacked 2347 (candidateList 2347 2048 256)
      0x4b70034b70034b70034b70034b70034b70034b70034b70034b70034b70034b70034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b80034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034b90034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034ba0034bb0034bb0034bb0034bb0034bb0034bb0034bb0034bb0044bb0044bb0044bb0044bb0044bb0044bb0044bb004 = true := by decide +kernel
  have replay58_9 : fastPacked 2347 (candidateList 2347 2304 256)
      0x4b30024b30024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b40024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b50024b60024b60024b60024b60024b60024b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b60034b70034b70034b70034b70034b70034b70034b70034b70034b7003 = true := by decide +kernel
  have replay58_10 : fastPacked 2347 (candidateList 2347 2560 256)
      0x4b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b10024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b20024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b30024b3002 = true := by decide +kernel
  have replay58_11 : fastPacked 2347 (candidateList 2347 2816 256)
      0x4ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014af0014b00014b00014b00014b00014b00014b00014b00014b00014b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b00024b10024b1002 = true := by decide +kernel
  have replay58_12 : fastPacked 2347 (candidateList 2347 3072 256)
      0x4ac0014ac0014ac0014ac0014ac0014ac0014ac0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ad0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae0014ae001 = true := by decide +kernel
  have replay58_13 : fastPacked 2347 (candidateList 2347 3328 256)
      0x4ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac0014ac001 = true := by decide +kernel
  have replay58_14 : fastPacked 2347 (candidateList 2347 3584 256)
      0x4a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014aa0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab0014ab001 = true := by decide +kernel
  have replay58_15 : fastPacked 2347 (candidateList 2347 3840 256)
      0x4a80004a80004a80004a80004a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a80014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a90014a9001 = true := by decide +kernel
  have replay58_16 : fastPacked 2347 (candidateList 2347 4096 256)
      0x4a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a80004a8000 = true := by decide +kernel
  have replay58_17 : fastPacked 2347 (candidateList 2347 4352 256)
      0x4a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a70004a7000 = true := by decide +kernel
  have replay58_18 : fastPacked 2347 (candidateList 2347 4608 256)
      0x4a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a60004a6000 = true := by decide +kernel
  have replay58_19 : fastPacked 2347 (candidateList 2347 4864 256)
      0x4a40004a40004a40004a40004a40004a40004a40004a40004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a50004a5000 = true := by decide +kernel
  have replay58_20 : fastPacked 2347 (candidateList 2347 5120 256)
      0x4a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a4000 = true := by decide +kernel
  have replay58_21 : fastPacked 2347 (candidateList 2347 5376 256)
      0x4a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a40004a4000 = true := by decide +kernel
  have replay58_22 : fastPacked 2347 (candidateList 2347 5632 54)
      0x4a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a30004a3000 = true := by decide +kernel
  have hs : p*p ≤ 2347^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 5686 := by
    have hc : (2347^3 : ℕ).sqrt = 113702 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 23 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay58_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay58_22 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked61 {p : ℕ} (hp : p.Prime) (hlo : 2*2467 < p)
    (hhi : p^2 < 2467^3) (hmod : p%3 ≠ 2467%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 2467 d = true := by
  have replay61_0 : fastPacked 2467 (candidateList 2467 0 256)
      0x23d0002110001fe0001f2 = true := by decide +kernel
  have replay61_1 : fastPacked 2467 (candidateList 2467 256 256)
      0x5c00685c20695c406b5c606c5c806e5c906e5cc0705cd0715d10745d20755d30765d907a5db07b5dc07c5e007f5e80855ed0885ee0895f008b5f70905fc0945fe09560209860609b60709d60a09e6100a36120a56180aa61f0af6210b16240b36260b46300bc6380c363b0c563e0c86500d66520d86590de6630e76660e966d0ef6720f36750f567a0f967d0fc68210069c1176a011a6a511f6b01286ba1316be1356ca13f6d614a6de1516eb15c6f01616f91696ff16e7081777441ae7a820b7bb21e7c922b7ef24f81d27c8842e08f334d94e3a80003ef0003e20003d00003c30003b10003a500031600030a0002d80002ad00026e00025c = true := by decide +kernel
  have replay61_2 : fastPacked 2467 (candidateList 2467 512 256)
      0x55602755602755702755702855802855902855902955b02a55c02a55c02a55d02b55d02b55e02b55f02c56002c56102d56102d56102d56202e56302e56302e56402e56602f56703056803156803156903156a03256b03356c03356e03456f03456f03557103657403757403857503857503857603957603957703957703957903a57a03b57c03c57d03c57e03d58003f58103f58404158404158604258604258704358804358904458c04658d04658e04758e04759004859004959304a59804d59904e59a04e59d05059e0525a10535a30545a50565a50565a90585aa0595ab05a5b005d5b205e5b60615b70625b80635b90635bb0655bf067 = true := by decide +kernel
  have replay61_3 : fastPacked 2467 (candidateList 2467 768 256)
      0x52e01552e01552f01552f01552f01553001553001553101653101653201653201653201653301753301753401753401753501753601853601853601853701853701853701853801953901953901953901953a01a53a01a53b01a53b01a53c01a53c01b53d01b53d01b53d01b53e01b53f01c53f01c53f01c54001c54101d54101d54201d54201d54201d54301e54401e54401e54501e54501f54601f54601f54701f54702054702054802054902054902154a02154a02154a02154c02254d02254d02354e02354e02354f02354f024550024551024551024552025552025552025553026554026554026555026555027 = true := by decide +kernel
  have replay61_4 : fastPacked 2467 (candidateList 2467 1024 256)
      0x51800c51800c51800c51900d51900d51900d51900d51900d51900d51900d51a00d51a00d51a00d51b00d51b00d51b00d51b00d51c00e51c00e51c00e51c00e51c00e51c00e51d00e51d00e51d00e51d00e51d00e51e00e51e00e51e00f51f00f51f00f51f00f51f00f51f00f52000f52000f52100f52100f52100f52101052101052101052201052201052201052301052301052301052301052401052401152401152401152401152501152501152501152601152701252701252701252701252801252801252801252801252901252901252901252901252901352a01352a01352a01352b01352b01352c01452c01452c01452c01452d01452d01452d01452d01452d014 = true := by decide +kernel
  have replay61_5 : fastPacked 2467 (candidateList 2467 1280 256)
      0x50b00850b00850b00850b00850c00850c00850c00950c00950c00950c00950c00950c00950d00950d00950d00950d00950d00950d00950e00950e00950e00950e00950e00950e00950e00950e00950e00950e00950f00950f00950f00950f00950f00950f00a50f00a51000a51000a51000a51000a51000a51000a51000a51000a51100a51100a51100a51100a51100a51100a51200a51200a51200a51200a51200a51200a51200a51300b51300b51300b51300b51300b51400b51400b51400b51400b51400b51400b51500b51500b51500b51500b51500b51600c51600c51600c51600c51600c51700c51700c51700c51700c51700c51800c51800c51800c51800c = true := by decide +kernel
  have replay61_6 : fastPacked 2467 (candidateList 2467 1536 256)
      0x50200650200650200650200650200650200650200650200650300650300650300650300650300650300650300650300650300650300650300650300650400650400650400650400650400650400650400650400650400650400650400650500650500650500750500750500750500750500750500750500750500750500750600750600750600750600750600750600750600750600750600750700750700750700750700750700750700750700750700750800750800750800750800750800750800750800750800750800850900850900850900850900850900850900850900850900850900850a00850a00850a00850a00850a00850a00850b00850b008 = true := by decide +kernel
  have replay61_7 : fastPacked 2467 (candidateList 2467 1792 256)
      0x4fb0044fb0044fb0044fc0044fc0044fc0044fc0044fc0044fc0044fc0044fc0044fc0044fc0044fc0044fc0044fc0054fc0054fd0054fd0054fd0054fd0054fd0054fd0054fd0054fd0054fd0054fd0054fd0054fd0054fd0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054fe0054ff0054ff0054ff0054ff0054ff0054ff0054ff0054ff0054ff0054ff0054ff005500005500005500005500005500005500005500005500005500005500005500005501005501006501006501006501006501006501006501006501006501006501006501006502006502006 = true := by decide +kernel
  have replay61_8 : fastPacked 2467 (candidateList 2467 2048 256)
      0x4f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f70034f80034f80044f80044f80044f80044f80044f80044f80044f80044f80044f80044f80044f80044f80044f80044f80044f80044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044f90044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fa0044fb0044fb0044fb0044fb0044fb0044fb0044fb0044fb0044fb0044fb0044fb0044fb0044fb0044fb004 = true := by decide +kernel
  have replay61_9 : fastPacked 2467 (candidateList 2467 2304 256)
      0x4f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f30034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f40034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f50034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f60034f6003 = true := by decide +kernel
  have replay61_10 : fastPacked 2467 (candidateList 2467 2560 256)
      0x4ef0024ef0024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f00024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f10024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20024f20034f20034f3003 = true := by decide +kernel
  have replay61_11 : fastPacked 2467 (candidateList 2467 2816 256)
      0x4ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ee0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef0024ef002 = true := by decide +kernel
  have replay61_12 : fastPacked 2467 (candidateList 2467 3072 256)
      0x4eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0014ec0024ec0024ec0024ec0024ec0024ec0024ec0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed0024ed002 = true := by decide +kernel
  have replay61_13 : fastPacked 2467 (candidateList 2467 3328 256)
      0x4e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014ea0014eb0014eb0014eb0014eb0014eb0014eb0014eb0014eb001 = true := by decide +kernel
  have replay61_14 : fastPacked 2467 (candidateList 2467 3584 256)
      0x4e70014e70014e70014e70014e70014e70014e70014e70014e70014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e80014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e90014e9001 = true := by decide +kernel
  have replay61_15 : fastPacked 2467 (candidateList 2467 3840 256)
      0x4e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e70014e7001 = true := by decide +kernel
  have replay61_16 : fastPacked 2467 (candidateList 2467 4096 256)
      0x4e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e60014e6001 = true := by decide +kernel
  have replay61_17 : fastPacked 2467 (candidateList 2467 4352 256)
      0x4e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e50004e50004e50004e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e50014e5001 = true := by decide +kernel
  have replay61_18 : fastPacked 2467 (candidateList 2467 4608 256)
      0x4e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e40004e4000 = true := by decide +kernel
  have replay61_19 : fastPacked 2467 (candidateList 2467 4864 256)
      0x4e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e30004e3000 = true := by decide +kernel
  have replay61_20 : fastPacked 2467 (candidateList 2467 5120 256)
      0x4e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e20004e2000 = true := by decide +kernel
  have replay61_21 : fastPacked 2467 (candidateList 2467 5376 256)
      0x4e00004e00004e00004e00004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e10004e1000 = true := by decide +kernel
  have replay61_22 : fastPacked 2467 (candidateList 2467 5632 256)
      0x4e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e0000 = true := by decide +kernel
  have replay61_23 : fastPacked 2467 (candidateList 2467 5888 239)
      0x4df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004df0004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e00004e0000 = true := by decide +kernel
  have hs : p*p ≤ 2467^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 6127 := by
    have hc : (2467^3 : ℕ).sqrt = 122533 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 24 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay61_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay61_23 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked67 {p : ℕ} (hp : p.Prime) (hlo : 2*2707 < p)
    (hhi : p^2 < 2707^3) (hmod : p%3 ≠ 2707%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 2707 d = true := by
  have replay67_0 : fastPacked 2707 (candidateList 2707 0 256)
      0 = true := by decide +kernel
  have replay67_1 : fastPacked 2707 (candidateList 2707 256 256)
      0x67b09267e09468109768309868709b68809c68c09e68e0a06930a46950a56970a769e0ad6a10ae6a20b06a90b56b40bd6bb0c36bd0c46c00c76ca0cf6d10d56d40d76da0dc6e00e06e20e26e60e56ee0ec6f20ef6fb0f770610070910370d10671010972011672d12173112473612975214275614576114e77315e77816378416d78c17479117979918079f1857a718d7d81b97df1c07ea1ca7fe1dd8141f181d1f983521085022986223a8822598902668a727c8b728b8d22a59e43b10003f40003e10003d50003b600039700036500034600033a00032700031b0003080002fc0002e90002dd00024d000241 = true := by decide +kernel
  have replay67_2 : fastPacked 2707 (candidateList 2707 512 256)
      0x5ee0355ee0355ef0365ef0365f10375f20375f20385f50395f50395f603a5f703a5f703a5f903b5fa03c5fb03c5fc03d5fc03d5fd03e5fe03e5fe03e60003f60003f60204160504260504260604360604360904460a04560b04660e04760e04860f04861104961504c61504c61604d61704d61804e61804e61904f61a04f61b05061d05162005362005362205462505662605762a05962b05a62c05b62d05b62e05c63005d63105e63406063606163706263806363a06463b06463f06764506b64606c64706d64b07064e07165107465407565607765707865c07b65e07c65f07d66508266808466e08866f08967108a67208b67508d67a091 = true := by decide +kernel
  have replay67_3 : fastPacked 2707 (candidateList 2707 768 256)
      0x5bb01c5bb01c5bc01c5bd01c5bd01c5bd01d5be01d5bf01d5bf01e5c001e5c001e5c101e5c201f5c201f5c201f5c201f5c40205c50205c50205c60215c60215c70215c70215c80215c90225c90225ca0225ca0235cb0235cb0235cc0235cc0245cd0245ce0245ce0255ce0255cf0255d00265d00265d10265d20265d30275d40275d40285d50285d50285d60295d70295d70295d80295d802a5d902a5da02a5db02b5db02b5db02b5dc02b5dd02c5de02c5de02d5df02d5df02d5e202e5e202f5e302f5e302f5e40305e40305e60315e60315e70315e80325e80325e90325e90335ea0335eb0335ec0345ec0345ed035 = true := by decide +kernel
  have replay67_4 : fastPacked 2707 (candidateList 2707 1024 256)
      0x5a00115a00115a00115a10115a10115a10115a10115a10115a10115a10115a20115a20115a20125a30125a30125a30125a40125a40125a40125a40125a50135a50135a50135a60135a60135a60135a60135a60135a70135a70135a80145a80145a80145a80145a80145a90145a90145aa0145aa0155ab0155ab0155ab0155ab0155ab0155ac0155ac0155ac0165ad0165ad0165ad0165ae0165ae0165af0165af0175af0175af0175af0175af0175b00175b20185b20185b20185b30185b30185b30185b30185b40195b40195b40195b40195b50195b50195b50195b60195b601a5b701a5b701a5b701a5b801a5b801b5b901b5b901b5b901b5ba01b5ba01b5ba01b5ba01b = true := by decide +kernel
  have replay67_5 : fastPacked 2707 (candidateList 2707 1280 256)
      0x58f00b58f00b59000b59000b59000b59000b59100c59100c59100c59100c59100c59100c59100c59200c59200c59200c59200c59200c59300c59300c59300c59300c59300c59300c59300c59300c59400d59400d59400d59400d59400d59400d59400d59500d59500d59500d59500d59500d59500d59600d59600d59600d59600d59600d59700d59700e59700e59700e59700e59800e59800e59800e59800e59800e59800e59900e59900e59900e59900e59a00e59a00f59a00f59a00f59b00f59b00f59b00f59b00f59b00f59c00f59c00f59c00f59c01059d01059d01059d01059d01059e01059e01059e01059e01059f01059f01059f01059f01159f01159f011 = true := by decide +kernel
  have replay67_6 : fastPacked 2707 (candidateList 2707 1536 256)
      0x58400858400858400858500858500858500858500858500858500858500858500858500858600858600858600858600858600858600858600858600858600858600958600958700958700958700958700958700958700958700958700958700958700958800958800958800958800958800958800958800958900958900958900958900958900958900958900958a00958a00958a00958a00a58a00a58a00a58b00a58b00a58b00a58b00a58b00a58b00a58b00a58b00a58b00a58b00a58c00a58c00a58c00a58c00a58c00a58c00a58c00a58d00a58d00a58d00a58d00a58d00a58d00a58d00b58e00b58e00b58e00b58f00b58f00b58f00b58f00b58f00b = true := by decide +kernel
  have replay67_7 : fastPacked 2707 (candidateList 2707 1792 256)
      0x57c00657c00657c00657c00657c00657c00657d00657d00657d00657d00657d00657d00657d00657d00657d00657d00657e00657e00657e00657e00657e00657e00657e00657e00657e00657e00657e00657f00657f00657f00757f00757f00757f00757f00757f00757f00757f00757f007580007580007580007580007580007580007580007580007580007581007581007581007581007581007581007581007581007581007581007582007582007582007582007582007582007582007582007582007583007583008583008583008583008583008583008583008583008583008584008584008584008584008 = true := by decide +kernel
  have replay67_8 : fastPacked 2707 (candidateList 2707 2048 256)
      0x57600557600557600557600557600557600557600557700557700557700557700557700557700557700557700557700557700557700557700557800557800557800557800557800557800557800557800557800557800557800557800557800557800557900557900557900557900557900557900557900557900557900557900557900557900557900557900557a00557a00557a00557a00557a00557a00557a00557a00557a00557a00557a00557b00557b00557b00657b00657b00657b00657b00657b00657b00657b00657b00657b00657b00657b00657b00657c00657c00657c00657c00657c00657c00657c00657c006 = true := by decide +kernel
  have replay67_9 : fastPacked 2707 (candidateList 2707 2304 256)
      0x571004571004572004572004572004572004572004572004572004572004572004572004572004572004572004572004572004572004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004573004574004574004574004574004574004574004574004574004574004574004574004574004574004574004574004574004574004574004575004575004575004575004575004575004575004575004575004575004575004575004575004575004575004575004575004575004576004576004576004576004576004576004576004576004576004576004 = true := by decide +kernel
  have replay67_10 : fastPacked 2707 (candidateList 2707 2560 256)
      0x56e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356e00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f00356f003570003570003570003570003570003570003570003570003570003570003570003570003570003570003570003570003570003570003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571003571004 = true := by decide +kernel
  have replay67_11 : fastPacked 2707 (candidateList 2707 2816 256)
      0x56a00256a00256a00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256b00256c00256c00256c00256c00256c00256c00256c00256c00256c00256c00256c00256c00356c00356c00356c00356c00356c00356c00356c00356c00356c00356c00356c00356c00356c00356c00356c00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356d00356e00356e003 = true := by decide +kernel
  have replay67_12 : fastPacked 2707 (candidateList 2707 3072 256)
      0x56800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256800256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256900256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a00256a002 = true := by decide +kernel
  have replay67_13 : fastPacked 2707 (candidateList 2707 3328 256)
      0x566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002566002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002567002568002568002568002568002568002568002568002568002568002568002 = true := by decide +kernel
  have replay67_14 : fastPacked 2707 (candidateList 2707 3584 256)
      0x564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001564001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001565001566001566001566002 = true := by decide +kernel
  have replay67_15 : fastPacked 2707 (candidateList 2707 3840 256)
      0x562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001563001564001564001564001564001564001564001564001564001564001564001 = true := by decide +kernel
  have replay67_16 : fastPacked 2707 (candidateList 2707 4096 256)
      0x561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001561001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001562001 = true := by decide +kernel
  have replay67_17 : fastPacked 2707 (candidateList 2707 4352 256)
      0x55f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001560001561001561001561001561001561001 = true := by decide +kernel
  have replay67_18 : fastPacked 2707 (candidateList 2707 4608 256)
      0x55e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f00155f001 = true := by decide +kernel
  have replay67_19 : fastPacked 2707 (candidateList 2707 4864 256)
      0x55d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00155d00155d00155d00155d00155d00155d00155d00155d00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e00155e001 = true := by decide +kernel
  have replay67_20 : fastPacked 2707 (candidateList 2707 5120 256)
      0x55c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d00055d000 = true := by decide +kernel
  have replay67_21 : fastPacked 2707 (candidateList 2707 5376 256)
      0x55b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c00055c000 = true := by decide +kernel
  have replay67_22 : fastPacked 2707 (candidateList 2707 5632 256)
      0x55b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b000 = true := by decide +kernel
  have replay67_23 : fastPacked 2707 (candidateList 2707 5888 256)
      0x55a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b00055b000 = true := by decide +kernel
  have replay67_24 : fastPacked 2707 (candidateList 2707 6144 256)
      0x55900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055900055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a00055a000 = true := by decide +kernel
  have replay67_25 : fastPacked 2707 (candidateList 2707 6400 256)
      0x559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000 = true := by decide +kernel
  have replay67_26 : fastPacked 2707 (candidateList 2707 6656 256)
      0x558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000559000 = true := by decide +kernel
  have replay67_27 : fastPacked 2707 (candidateList 2707 6912 131)
      0x558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000558000 = true := by decide +kernel
  have hs : p*p ≤ 2707^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 7043 := by
    have hc : (2707^3 : ℕ).sqrt = 140842 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 28 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay67_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay67_27 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked76 {p : ℕ} (hp : p.Prime) (hlo : 2*3067 < p)
    (hhi : p^2 < 3067^3) (hmod : p%3 ≠ 3067%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3067 d = true := by
  have replay76_0 : fastPacked 3067 (candidateList 3067 0 256)
      0 = true := by decide +kernel
  have replay76_1 : fastPacked 3067 (candidateList 3067 256 256)
      0x7b30ec7b80f07be0f57c10f77c70fc7c90fe7cf1037d31067db10d7df1107e21127ef11d7f31217f612380212d81413d82214882514b82a15083d16084b16c85117185b17a86718486b18887218e88319d88b1a489e1b58b51ca8bb1d08c41d88cb1de8ed1fe90d21b91522292222e96d27597928099829e9d22d59e32e5a11312a31331a48347a7036ea8e38bac43c00004c40004b80004a500048600046700045b00043c00041d00040a0003eb0003df0003cc0003c00003ad0003440002c70002b50002a800028900026a = true := by decide +kernel
  have replay76_2 : fastPacked 3067 (candidateList 3067 512 256)
      0x6db0516dc0516dd0526de0526e00546e10546e20556e60576e60576e70586e80596e90596eb05b6ed05c6ee05d6f005d6f005e6f105e6f305f6f30606f50616f60616f90636fc0666fd0666fe0676ff06770206970406b70506b70906e70b06f70b06f70e07171407571507671607771707771807871907971a07a71b07a71d07c72107e72408072508172808372c08672d08773408b73508c73708e73908f73a09073c09273e09374409774609974709974909b74c09d74d09e7530a275d0a975f0ab7600ac7670b176a0b37700b87740ba7780bd7790bf7810c57830c67850c87900d07940d479d0db79f0dc7a20df7a40e07a90e47b10ea = true := by decide +kernel
  have replay76_3 : fastPacked 3067 (candidateList 3067 768 256)
      0x69402a69502a69602b69602b69602b69702b69802b69902c69a02d69a02d69b02d69c02e69d02e69e02e69e02f69e02f6a10306a20316a20316a30316a30316a40326a50326a50326a70336a80346a80346a90346a90356ab0356ab0356ac0366ad0366ae0376ae0376af0376b00386b10396b20396b20396b403a6b603b6b603c6b703c6b803c6b803c6ba03d6ba03e6bb03e6bc03f6bd03f6be0406bf0406c00416c10416c10416c20426c30436c40436c50446c60446c70456ca0476cb0476cc0486cc0486cd0486ce0496d004a6d004a6d204b6d304c6d404c6d404d6d504d6d704e6d704e6d904f6d904f6da050 = true := by decide +kernel
  have replay76_4 : fastPacked 3067 (candidateList 3067 1024 256)
      0x66f01966f01966f01967001967001a67001a67001a67101a67101a67101a67101a67201a67201a67301b67301b67401b67401b67501b67501c67501c67501c67601c67601c67701c67701d67701d67801d67801d67801d67901d67a01d67a01e67a01e67a01e67a01e67b01e67b01e67c01f67d01f67e01f67e01f67e01f67e02067f02067f02067f02068002068002168102168102168202168202168302268302268402268402268402268402268502368702468702468802468802468902468902568902568a02568a02568b02568b02568b02568b02668c02668d02668d02668e02768f02768f027690028691028691028691028692028692029692029693029693029 = true := by decide +kernel
  have replay76_5 : fastPacked 3067 (candidateList 3067 1280 256)
      0x65901165901165901165901165a01165a01165a01165a01165b01165b01165b01265b01265b01265c01265c01265c01265c01265d01265d01265d01265d01265e01265e01265e01365e01365e01365e01365e01365f01365f01365f01365f01365f01366001366001366001366101466101466101466101466101466201466201466201466201466301466301466301566401566401566401566401566401566401566501566501566601566601566601666601666701666701666801666801666801666801666901766901766901766901766a01766a01766b01766b01866b01866c01866c01866c01866d01866d01866d01866e01966e01966e01966e01966e019 = true := by decide +kernel
  have replay76_6 : fastPacked 3067 (candidateList 3067 1536 256)
      0x64a00c64a00c64a00c64a00c64b00c64b00c64b00c64b00c64b00c64b00c64b00c64b00c64c00d64c00d64c00d64c00d64c00d64c00d64c00d64d00d64d00d64d00d64d00d64d00d64d00d64d00d64d00d64d00d64e00d64e00d64e00d64e00d64e00d64f00d64f00d64f00d64f00d64f00e65000e65000e65000e65000e65000e65000e65100e65100e65100e65100e65100e65100e65100e65200e65200e65200f65200f65300f65300f65300f65300f65300f65300f65300f65300f65400f65400f65400f65400f65500f65500f65500f655010655010656010656010656010656010656010657010657010657010658010658010658010658011659011 = true := by decide +kernel
  have replay76_7 : fastPacked 3067 (candidateList 3067 1792 256)
      0x63f00963f00963f00964000964000964000964000964000964000964000964000964000964000964100964100964100964100964100964100964100964200a64200a64200a64200a64200a64200a64200a64200a64200a64300a64300a64300a64300a64300a64300a64300a64300a64300a64400a64400a64400a64400a64400a64400a64400a64500a64500a64500a64500b64500b64500b64600b64600b64600b64600b64600b64600b64600b64600b64700b64700b64700b64700b64700b64700b64700b64800b64800b64800b64800b64800b64800b64800b64900b64900c64900c64900c64900c64a00c64a00c = true := by decide +kernel
  have replay76_8 : fastPacked 3067 (candidateList 3067 2048 256)
      0x63700763800763800763800763800763800763800763800763800763800763800763900763900763900763900763900763900763900763900763900763900763900763900763a00763a00763a00763a00763a00863a00863a00863a00863a00863a00863a00863b00863b00863b00863b00863b00863b00863b00863b00863b00863b00863b00863c00863c00863c00863c00863c00863c00863c00863c00863c00863d00863d00863d00863d00863d00863d00863d00863d00863e00863e00863e00863e00863e00863e00963e00963e00963e00963e00963e00963e00963f00963f00963f00963f00963f00963f00963f009 = true := by decide +kernel
  have replay76_9 : fastPacked 3067 (candidateList 3067 2304 256)
      0x631005631005631005631005631005631005631005632006632006632006632006632006632006632006632006632006632006632006633006633006633006633006633006633006633006633006633006633006633006633006633006633006633006633006633006633006634006634006634006634006634006634006634006634006634006634006634006634006634006634006635006635006635006635006635006635006635006635006635006635006635006635006635006635006636006636006636006636006636006636006636007636007636007636007636007636007636007637007637007637007637007637007637007637007637007637007 = true := by decide +kernel
  have replay76_10 : fastPacked 3067 (candidateList 3067 2560 256)
      0x62c00462c00462c00462c00462c00462c00462c00462c00462c00462c00462d00462d00462d00462d00562d00562d00562d00562d00562d00562d00562d00562d00562d00562d00562d00562d00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562e00562f00562f00562f00562f00562f00562f00562f00562f00562f00562f00562f00562f00562f00562f00562f005630005630005630005630005630005630005630005630005630005630005630005630005630005630005630005630005630005631005631005631005631005631005631005631005631005631005 = true := by decide +kernel
  have replay76_11 : fastPacked 3067 (candidateList 3067 2816 256)
      0x62800462800462800462800462800462800462800462800462800462800462800462800462800462800462900462900462900462900462900462900462900462900462900462900462900462900462900462900462900462900462900462900462900462900462900462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462a00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462b00462c00462c00462c00462c00462c00462c00462c00462c00462c00462c004 = true := by decide +kernel
  have replay76_12 : fastPacked 3067 (candidateList 3067 3072 256)
      0x624003624003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003625003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003626003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003627003628003628003628004628004628004628004628004628004 = true := by decide +kernel
  have replay76_13 : fastPacked 3067 (candidateList 3067 3328 256)
      0x622002622002622002622002622002622002622002622002622002622002622003622003622003622003622003622003622003622003622003622003622003622003622003622003622003622003622003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003623003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003624003 = true := by decide +kernel
  have replay76_14 : fastPacked 3067 (candidateList 3067 3584 256)
      0x61f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002620002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002621002 = true := by decide +kernel
  have replay76_15 : fastPacked 3067 (candidateList 3067 3840 256)
      0x61d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261e00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f00261f002 = true := by decide +kernel
  have replay76_16 : fastPacked 3067 (candidateList 3067 4096 256)
      0x61b00161b00161b00161b00161b00161b00161b00261b00261b00261b00261b00261b00261b00261b00261b00261b00261b00261b00261b00261b00261b00261b00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261c00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d00261d002 = true := by decide +kernel
  have replay76_17 : fastPacked 3067 (candidateList 3067 4352 256)
      0x61900161900161900161900161900161900161900161900161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161a00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b00161b001 = true := by decide +kernel
  have replay76_18 : fastPacked 3067 (candidateList 3067 4608 256)
      0x618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001619001 = true := by decide +kernel
  have replay76_19 : fastPacked 3067 (candidateList 3067 4864 256)
      0x617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001617001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001618001 = true := by decide +kernel
  have replay76_20 : fastPacked 3067 (candidateList 3067 5120 256)
      0x615001615001615001615001615001615001615001615001615001615001615001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001616001617001617001617001 = true := by decide +kernel
  have replay76_21 : fastPacked 3067 (candidateList 3067 5376 256)
      0x614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001615001 = true := by decide +kernel
  have replay76_22 : fastPacked 3067 (candidateList 3067 5632 256)
      0x613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001614001 = true := by decide +kernel
  have replay76_23 : fastPacked 3067 (candidateList 3067 5888 256)
      0x612000612000612000612000612000612000612000612000612000612000612000612000613000613000613000613000613000613000613000613000613000613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001613001 = true := by decide +kernel
  have replay76_24 : fastPacked 3067 (candidateList 3067 6144 256)
      0x612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000612000 = true := by decide +kernel
  have replay76_25 : fastPacked 3067 (candidateList 3067 6400 256)
      0x611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000612000612000612000 = true := by decide +kernel
  have replay76_26 : fastPacked 3067 (candidateList 3067 6656 256)
      0x610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000611000 = true := by decide +kernel
  have replay76_27 : fastPacked 3067 (candidateList 3067 6912 256)
      0x60f00060f00060f00060f00060f00060f000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000610000 = true := by decide +kernel
  have replay76_28 : fastPacked 3067 (candidateList 3067 7168 256)
      0x60f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f000 = true := by decide +kernel
  have replay76_29 : fastPacked 3067 (candidateList 3067 7424 256)
      0x60e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f00060f000 = true := by decide +kernel
  have replay76_30 : fastPacked 3067 (candidateList 3067 7680 256)
      0x60e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e000 = true := by decide +kernel
  have replay76_31 : fastPacked 3067 (candidateList 3067 7936 256)
      0x60d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e00060e000 = true := by decide +kernel
  have replay76_32 : fastPacked 3067 (candidateList 3067 8192 256)
      0x60d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d000 = true := by decide +kernel
  have replay76_33 : fastPacked 3067 (candidateList 3067 8448 45)
      0x60d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d00060d000 = true := by decide +kernel
  have hs : p*p ≤ 3067^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 8493 := by
    have hc : (3067^3 : ℕ).sqrt = 169851 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 34 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay76_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay76_33 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked79 {p : ℕ} (hp : p.Prime) (hlo : 2*3187 < p)
    (hhi : p^2 < 3187^3) (hmod : p%3 ≠ 3187%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3187 d = true := by
  have replay79_0 : fastPacked 3187 (candidateList 3187 0 256)
      0 = true := by decide +kernel
  have replay79_1 : fastPacked 3187 (candidateList 3187 256 256)
      0x82611482c11983311f83712283e12884012a84713084c13485613c85b14085e14386e15187315587715888516489c1798ad1878b118b8b81918cf1a58e11b58e91bc8f61c89051d590b1db9141e392a1f893420194e21896e23697623e98324a98d2539bf2829ee2af9fb2bba102cfa9534eaac365af03a8ba3458c064ba00050e0004fb0004ef0004dc0004d00004bd0004600004540004410004220004030003f70003d80003b90003a600038700037b00036800035c0003490002df = true := by decide +kernel
  have replay79_2 : fastPacked 3187 (candidateList 3187 512 256)
      0x72d05c72e05d72f05d73005e73306073306073506173906473906473b06573c06673d06673f06874106974206a74406b74506b74606c74806d74806e74a06f74b06f74f07275207475307575407675507675907975b07a75c07b76107e76307f76308076708276e08776e08777008877108977208a77308b77508c77508c77808e77c09177f09378109478409678909a78a09b7910a07930a17950a37970a57980a579b0a879d0a97a40ae7a70b07a80b17aa0b27ad0b57af0b67b60bb7c10c47c30c57c50c77cc0cd7d10d07d70d57dc0d87e00dc7e20dd7eb0e47ee0e77f00e87fc0f28020f780c0ff80f10181210481410681a10a824112 = true := by decide +kernel
  have replay79_3 : fastPacked 3187 (candidateList 3187 768 256)
      0x6de0306df0306e00306e00306e10316e10316e20316e40326e50336e50336e60336e70346e80346e90356e90356e90356ec0366ed0376ee0376ee0386ef0386f00396f00396f10396f303a6f403b6f403b6f503b6f603c6f703c6f703d6f903d6f903e6fb03f6fb03f6fc03f6fd0406fe0416ff0416ff04170104270304370404470504470504470604570804670804670904770a04770b04870d04970e04970f04a70f04a71004a71104b71304c71404d71504d71504e71604e71a05071b05171c05271c05271d05271e05372005472105572305672305672505772505772605872805972905972a05a72b05b72c05c = true := by decide +kernel
  have replay79_4 : fastPacked 3187 (candidateList 3187 1024 256)
      0x6b501c6b501c6b501d6b601d6b601d6b601d6b701d6b701d6b701d6b701d6b701d6b801e6b901e6ba01e6ba01e6ba01f6bb01f6bb01f6bb01f6bc01f6bc01f6bc0206bd0206bd0206be0206be0206bf0206bf0216bf0216c00216c10216c10226c10226c10226c20226c20226c30226c40236c50236c50236c50246c60246c60246c60246c70246c70246c80256c80256c80256c90256ca0266ca0266cb0266cb0266cc0266cc0276cc0276cc0276ce0276d00286d00296d00296d10296d10296d20296d202a6d302a6d302a6d402a6d402a6d402a6d402b6d502b6d602b6d602c6d702c6d802c6d802d6d902d6da02d6db02e6db02e6db02e6dc02e6dc02e6dc02f6dd02f = true := by decide +kernel
  have replay79_5 : fastPacked 3187 (candidateList 3187 1280 256)
      0x69d01369d01369d01369d01369e01369e01369e01469e01469f01469f01469f01469f0146a00146a00146a00146a00146a10146a10156a10156a20156a20156a20156a20156a20156a20156a30156a30156a30156a30156a30156a40156a40166a40166a50166a50166a50166a50166a50166a50166a60166a60166a70176a70176a70176a70176a70176a80176a80176a90176a90176a90186a90186a90186a90186aa0186aa0186ab0186ab0186ab0186ac0196ac0196ac0196ad0196ad0196ad0196ae0196ae01a6ae01a6af01a6af01a6b001a6b001a6b001a6b101b6b101b6b101b6b201b6b201b6b201b6b301b6b301c6b401c6b401c6b401c6b401c6b401c = true := by decide +kernel
  have replay79_6 : fastPacked 3187 (candidateList 3187 1536 256)
      0x68d00e68d00e68d00e68d00e68d00e68d00e68d00e68d00e68e00e68e00e68e00e68e00e68e00e68f00e68f00e68f00e68f00e68f00e68f00e68f00e68f00e69000e69000f69000f69000f69000f69000f69000f69000f69100f69100f69100f69100f69200f69200f69200f69200f69200f69300f69300f69301069301069301069301069401069401069401069401069401069401069501069501069501069601069601169601169601169601169601169701169701169701169701169701169801169801169801169801169801169801169901269901269901269901269901269901269a01269a01269b01269b01269b01369b01369c01369c01369c013 = true := by decide +kernel
  have replay79_7 : fastPacked 3187 (candidateList 3187 1792 256)
      0x68100a68100a68100a68100a68100a68100a68100a68100a68200a68200a68200a68200a68200a68200a68200a68200b68300b68300b68300b68300b68300b68400b68400b68400b68400b68400b68400b68400b68400b68400b68500b68500b68500b68500b68500b68500b68500b68500b68600b68600b68600b68600c68600c68600c68600c68700c68700c68700c68700c68700c68700c68800c68800c68800c68800c68800c68800c68900c68900c68900c68900c68900c68900d68a00d68a00d68a00d68a00d68a00d68a00d68a00d68b00d68b00d68b00d68b00d68b00d68b00d68c00d68c00d68c00d68c00d = true := by decide +kernel
  have replay79_8 : fastPacked 3187 (candidateList 3187 2048 256)
      0x67800867800867800867800867800867900867900867900867900867900867900867a00867a00867a00867a00867a00867a00867a00867a00867a00867a00867a00867a00867b00867b00867b00867b00967b00967b00967b00967b00967b00967b00967c00967c00967c00967c00967c00967c00967c00967c00967c00967c00967c00967d00967d00967d00967d00967d00967d00967d00967d00967d00967e00967e00967e00967e00967e00967e00967e00967f00967f00967f00a67f00a67f00a67f00a67f00a67f00a67f00a67f00a68000a68000a68000a68000a68000a68000a68000a68000a68000a68100a68100a = true := by decide +kernel
  have replay79_9 : fastPacked 3187 (candidateList 3187 2304 256)
      0x671006671006671006672006672006672006672006672006672006672006672006672006672006672006673006673006673006673006673006673007673007673007673007673007673007673007673007673007673007674007674007674007674007674007674007674007674007674007674007674007674007674007674007674007675007675007675007675007675007675007675007675007675007675007675007675007676007676007676007676007676007676007676007676007676007676007676007676007676007677007677007677007677007677007677007677008677008677008677008677008678008678008678008678008678008678008 = true := by decide +kernel
  have replay79_10 : fastPacked 3187 (candidateList 3187 2560 256)
      0x66c00566c00566c00566c00566c00566c00566c00566c00566c00566c00566c00566d00566d00566d00566d00566d00566d00566d00566d00566d00566d00566d00566d00566d00566d00566d00566d00566e00566e00566e00566e00566e00566e00566e00566e00566e00566e00566e00566e00566e00566e00566e00566e00566f00666f00666f00666f00666f00666f00666f00666f00666f00666f00666f00666f00666f00666f006670006670006670006670006670006670006670006670006670006670006670006670006670006670006671006671006671006671006671006671006671006671006671006671006671006671006671006 = true := by decide +kernel
  have replay79_11 : fastPacked 3187 (candidateList 3187 2816 256)
      0x66700466700466700466700466700466700466700466800466800466800466800466800466800466800466800466800466800466800466800466800466800466800466800466800466800466800466900466900466900466900466900466900466900466900466900466900466900466900466900466900466900466900466900466900466900466a00466a00466a00466a00466a00566a00566a00566a00566a00566a00566a00566a00566a00566a00566a00566a00566a00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566b00566c00566c00566c005 = true := by decide +kernel
  have replay79_12 : fastPacked 3187 (candidateList 3187 3072 256)
      0x664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664003664004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004665004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004666004667004667004667004667004667004667004667004667004667004667004667004667004667004667004667004667004667004 = true := by decide +kernel
  have replay79_13 : fastPacked 3187 (candidateList 3187 3328 256)
      0x660003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003661003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003662003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003663003664003664003 = true := by decide +kernel
  have replay79_14 : fastPacked 3187 (candidateList 3187 3584 256)
      0x65e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e00265f00265f00265f00265f00265f00265f00265f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f00365f003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003660003 = true := by decide +kernel
  have replay79_15 : fastPacked 3187 (candidateList 3187 3840 256)
      0x65b00265b00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265c00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265d00265e00265e00265e00265e00265e00265e00265e00265e00265e00265e002 = true := by decide +kernel
  have replay79_16 : fastPacked 3187 (candidateList 3187 4096 256)
      0x65900265900265900265900265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265a00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b00265b002 = true := by decide +kernel
  have replay79_17 : fastPacked 3187 (candidateList 3187 4352 256)
      0x658001658001658001658001658001658001658001658001658001658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002658002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002659002 = true := by decide +kernel
  have replay79_18 : fastPacked 3187 (candidateList 3187 4608 256)
      0x656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001657001658001658001 = true := by decide +kernel
  have replay79_19 : fastPacked 3187 (candidateList 3187 4864 256)
      0x655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001655001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001656001 = true := by decide +kernel
  have replay79_20 : fastPacked 3187 (candidateList 3187 5120 256)
      0x653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001654001655001 = true := by decide +kernel
  have replay79_21 : fastPacked 3187 (candidateList 3187 5376 256)
      0x652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001653001 = true := by decide +kernel
  have replay79_22 : fastPacked 3187 (candidateList 3187 5632 256)
      0x651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001652001 = true := by decide +kernel
  have replay79_23 : fastPacked 3187 (candidateList 3187 5888 256)
      0x650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001651001 = true := by decide +kernel
  have replay79_24 : fastPacked 3187 (candidateList 3187 6144 256)
      0x64f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001650001 = true := by decide +kernel
  have replay79_25 : fastPacked 3187 (candidateList 3187 6400 256)
      0x64e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00064f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f00164f001 = true := by decide +kernel
  have replay79_26 : fastPacked 3187 (candidateList 3187 6656 256)
      0x64e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e00064e000 = true := by decide +kernel
  have replay79_27 : fastPacked 3187 (candidateList 3187 6912 256)
      0x64d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064e00064e000 = true := by decide +kernel
  have replay79_28 : fastPacked 3187 (candidateList 3187 7168 256)
      0x64c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d00064d000 = true := by decide +kernel
  have replay79_29 : fastPacked 3187 (candidateList 3187 7424 256)
      0x64c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c000 = true := by decide +kernel
  have replay79_30 : fastPacked 3187 (candidateList 3187 7680 256)
      0x64b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c00064c000 = true := by decide +kernel
  have replay79_31 : fastPacked 3187 (candidateList 3187 7936 256)
      0x64a00064a00064a00064a00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b00064b000 = true := by decide +kernel
  have replay79_32 : fastPacked 3187 (candidateList 3187 8192 256)
      0x64a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a000 = true := by decide +kernel
  have replay79_33 : fastPacked 3187 (candidateList 3187 8448 256)
      0x64a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a00064a000 = true := by decide +kernel
  have replay79_34 : fastPacked 3187 (candidateList 3187 8704 256)
      0x649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000649000 = true := by decide +kernel
  have replay79_35 : fastPacked 3187 (candidateList 3187 8960 36)
      0x649000649000649000649000649000649000649000649000649000649000649000649000 = true := by decide +kernel
  have hs : p*p ≤ 3187^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 8996 := by
    have hc : (3187^3 : ℕ).sqrt = 179917 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 36 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay79_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_33 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_34 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay79_35 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked82 {p : ℕ} (hp : p.Prime) (hlo : 2*3307 < p)
    (hhi : p^2 < 3307^3) (hmod : p%3 ≠ 3307%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3307 d = true := by
  have replay82_0 : fastPacked 3307 (candidateList 3307 0 256)
      0 = true := by decide +kernel
  have replay82_1 : fastPacked 3307 (candidateList 3307 256 256)
      0x8a01438a81498af1508b41548bc15b8c015e8c81658ce16a8da1758e017a8e417d8f818e8fe1949021989141a79311c19471d494c1d99551e19731fc98a21199421b9a722c9ba23e9c22459cf2519ee26e9fd27ca2229fa522cca5f2d9a742eca832fbad934eb363a8b533c4b853f50005320005260005070004d50004c90004aa00049700048b00047800046c0004590003fc0003f00003dd0003be00039f0003930003740003550003420003230003160003040002f70002e5 = true := by decide +kernel
  have replay82_2 : fastPacked 3307 (candidateList 3307 512 256)
      0x78006978206a78306a78406b78706d78806d78906e78e07178e07279007379107479207479507679707879907879a07a79b07a79c07b79e07c79f07d7a107e7a207f7a60827ab0857ab0857ad0867ae0877b208a7b408b7b608c7bb0907bd0917be0927c20957c909a7ca09b7cc09c7cd09d7cf09e7d009f7d10a07d20a07d50a27da0a67de0a97df0aa7e20ac7e90b17ea0b27f20b87f30b97f70bb7f90bd7fa0be7fe0c18000c28070c880b0ca80c0cc80f0cd8120d08140d281c0d88290e282b0e482d0e58360ec83b0f08430f68480fa84d0fe84f10085a10985d10b85f10d86f11a87511f88112988412b88812f88b13189213789d140 = true := by decide +kernel
  have replay82_3 : fastPacked 3307 (candidateList 3307 768 256)
      0x72903672903672b03772b03772b03772c03772d03872f03973003973003a73103a73203a73403b73403c73503c73503c73803e73a03e73a03f73b03f73b03f73d04073d04073e04174004274104374104374204374304474404474504574604574704674904774904774a04774b04874d04974d04974e04a75004b75204c75304d75404d75404e75504e75704f75805075905075a05175b05175c05275d05375f05475f05476005476105576305676405776605876605876705976b05b76c05c76d05d76e05d76f05d77005e77206077306077506177606277706377806377906477b06577c06677d06777e06777f068 = true := by decide +kernel
  have replay82_4 : fastPacked 3307 (candidateList 3307 1024 256)
      0x6fb0206fc0206fc0206fd0216fd0216fd0216fd0216fd0216fe0216fe0216fe0216ff02170002270102270102270102370202370202370302370302370302370402470402470502470602470602570602570602570702570802570802670902670902670902670902670a02670b02770c02770d02870d02870e02870e02870e02870e02870f02970f02971002971102a71102a71102a71302a71302b71402b71402b71502b71502c71502c71502c71702c71902d71902e71a02e71a02e71b02e71b02f71c02f71c02f71d02f71d03071d03071e03071e03071f031720031720031721032722032723032724033724033725034725034726034726034727034727035727035 = true := by decide +kernel
  have replay82_5 : fastPacked 3307 (candidateList 3307 1280 256)
      0x6e10156e10156e10156e20166e20166e20166e30166e30166e30166e30166e40166e40166e40176e40176e50176e50176e50176e60176e60176e60176e70176e70186e70186e70186e70186e70186e80186e80186e80186e80186e90186e90186e90186ea0196ea0196ea0196ea0196ea0196eb0196eb0196eb0196ec0196ec01a6ec01a6ec01a6ed01a6ed01a6ee01a6ee01a6ee01a6ee01b6ef01b6ef01b6ef01b6ef01b6f001b6f001b6f101b6f101c6f101c6f201c6f201c6f301c6f301c6f301d6f301d6f401d6f401d6f501d6f501d6f601e6f601e6f601e6f701e6f701e6f801e6f801e6f801f6f901f6f901f6fa01f6fa01f6fa01f6fb0206fb0206fb020 = true := by decide +kernel
  have replay82_6 : fastPacked 3307 (candidateList 3307 1536 256)
      0x6cf00f6cf00f6d000f6d000f6d000f6d000f6d00106d00106d00106d10106d10106d10106d10106d20106d20106d20106d20106d20106d20106d20106d20106d30106d30106d30106d30106d30106d30116d30116d40116d40116d40116d40116d40116d50116d50116d50116d50116d50116d60116d60116d60116d60126d60126d70126d70126d70126d70126d80126d80126d80126d80126d90126d90126d90136d90136d90136da0136da0136da0136da0136da0136da0136db0136db0136db0136dc0136dc0136dc0146dc0146dc0146dd0146dd0146dd0146dd0146dd0146dd0146de0146de0146df0146df0156e00156e00156e00156e00156e1015 = true := by decide +kernel
  have replay82_7 : fastPacked 3307 (candidateList 3307 1792 256)
      0x6c300b6c300b6c300b6c300b6c300b6c300b6c300c6c300c6c300c6c400c6c400c6c400c6c400c6c400c6c400c6c400c6c500c6c500c6c500c6c500c6c500c6c600c6c600c6c600c6c600c6c600c6c600c6c600c6c600c6c700d6c700d6c700d6c700d6c700d6c700d6c700d6c700d6c800d6c800d6c800d6c800d6c800d6c800d6c900d6c900d6c900d6c900d6c900d6ca00d6ca00d6ca00d6ca00e6ca00e6ca00e6cb00e6cb00e6cb00e6cb00e6cb00e6cb00e6cc00e6cc00e6cc00e6cc00e6cc00e6cc00e6cd00e6cd00e6cd00e6cd00f6cd00f6cd00f6cd00f6ce00f6ce00f6ce00f6ce00f6ce00f6cf00f6cf00f = true := by decide +kernel
  have replay82_8 : fastPacked 3307 (candidateList 3307 2048 256)
      0x6b90096b90096b90096b90096ba0096ba0096ba0096ba0096ba0096ba0096ba0096bb0096bb0096bb0096bb0096bb0096bb0096bb0096bb0096bb0096bc0096bc0096bc0096bc00a6bc00a6bc00a6bc00a6bc00a6bc00a6bc00a6bd00a6bd00a6bd00a6bd00a6bd00a6bd00a6bd00a6bd00a6bd00a6bd00a6be00a6be00a6be00a6be00a6be00a6be00a6be00a6be00a6bf00a6bf00a6bf00a6bf00a6bf00a6bf00a6bf00a6bf00a6c000a6c000b6c000b6c000b6c000b6c000b6c000b6c100b6c100b6c100b6c100b6c100b6c100b6c100b6c100b6c100b6c100b6c200b6c200b6c200b6c200b6c200b6c200b6c200b6c200b = true := by decide +kernel
  have replay82_9 : fastPacked 3307 (candidateList 3307 2304 256)
      0x6b20076b20076b20076b20076b20076b20076b20076b20076b20076b30076b30076b30076b30076b30076b30076b30076b30076b30076b30076b40076b40076b40076b40076b40076b40076b40076b40076b40076b40076b40086b40086b40086b40086b40086b40086b50086b50086b50086b50086b50086b50086b50086b50086b50086b50086b50086b50086b50086b50086b60086b60086b60086b60086b60086b60086b60086b60086b60086b70086b70086b70086b70086b70086b70086b70086b70086b70086b70086b70086b70086b80086b80086b80086b80086b80086b80086b80086b80096b80096b80096b90096b90096b90096b90096b90096b9009 = true := by decide +kernel
  have replay82_10 : fastPacked 3307 (candidateList 3307 2560 256)
      0x6ac0066ac0066ac0066ac0066ac0066ac0066ac0066ac0066ac0066ac0066ac0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ad0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066ae0066af0066af0066af0066af0066af0066af0066af0066af0066af0066af0066af0066af0066af0066b00066b00066b00066b00066b00066b00076b00076b00076b00076b00076b00076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b10076b20076b20076b2007 = true := by decide +kernel
  have replay82_11 : fastPacked 3307 (candidateList 3307 2816 256)
      0x6a70056a70056a70056a70056a70056a70056a70056a70056a70056a70056a70056a70056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a80056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056a90056aa0056aa0056aa0056aa0056aa0056aa0056aa0056aa0056aa0056aa0056aa0056aa0056aa0056aa0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0056ab0066ac0066ac0066ac006 = true := by decide +kernel
  have replay82_12 : fastPacked 3307 (candidateList 3307 3072 256)
      0x6a30046a30046a30046a30046a30046a30046a30046a30046a30046a30046a30046a30046a30046a30046a30046a30046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a40046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a50046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a60046a70056a70056a70056a70056a70056a70056a70056a7005 = true := by decide +kernel
  have replay82_13 : fastPacked 3307 (candidateList 3307 3328 256)
      0x69f0036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a00036a10036a10036a10036a10036a10036a10036a10036a10036a10036a10036a10036a10036a10036a10036a10036a10046a10046a10046a10046a10046a10046a10046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a20046a30046a30046a30046a30046a30046a30046a30046a3004 = true := by decide +kernel
  have replay82_14 : fastPacked 3307 (candidateList 3307 3584 256)
      0x69d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369d00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369e00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f00369f003 = true := by decide +kernel
  have replay82_15 : fastPacked 3307 (candidateList 3307 3840 256)
      0x69a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00269b00369b00369b00369b00369b00369b00369b00369b00369b00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369c00369d00369d00369d003 = true := by decide +kernel
  have replay82_16 : fastPacked 3307 (candidateList 3307 4096 256)
      0x69800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269800269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269900269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a00269a002 = true := by decide +kernel
  have replay82_17 : fastPacked 3307 (candidateList 3307 4352 256)
      0x696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002697002698002698002698002698002698002698002698002698002698002698002698002698002698002698002698002 = true := by decide +kernel
  have replay82_18 : fastPacked 3307 (candidateList 3307 4608 256)
      0x694001694001694001694001694001694001694001694001694002694002694002694002694002694002694002694002694002694002694002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002695002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002696002 = true := by decide +kernel
  have replay82_19 : fastPacked 3307 (candidateList 3307 4864 256)
      0x693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001693001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001694001 = true := by decide +kernel
  have replay82_20 : fastPacked 3307 (candidateList 3307 5120 256)
      0x691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001692001693001693001693001693001 = true := by decide +kernel
  have replay82_21 : fastPacked 3307 (candidateList 3307 5376 256)
      0x690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001691001 = true := by decide +kernel
  have replay82_22 : fastPacked 3307 (candidateList 3307 5632 256)
      0x68f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001690001 = true := by decide +kernel
  have replay82_23 : fastPacked 3307 (candidateList 3307 5888 256)
      0x68e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f00168f001 = true := by decide +kernel
  have replay82_24 : fastPacked 3307 (candidateList 3307 6144 256)
      0x68d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e00168e001 = true := by decide +kernel
  have replay82_25 : fastPacked 3307 (candidateList 3307 6400 256)
      0x68c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d00168d001 = true := by decide +kernel
  have replay82_26 : fastPacked 3307 (candidateList 3307 6656 256)
      0x68b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00168b00168b00168b00168b00168b00168b00168b00168b00168b00168b00168b00168b00168b00168b00168b00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c00168c001 = true := by decide +kernel
  have replay82_27 : fastPacked 3307 (candidateList 3307 6912 256)
      0x68a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b00068b000 = true := by decide +kernel
  have replay82_28 : fastPacked 3307 (candidateList 3307 7168 256)
      0x68a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a00068a000 = true := by decide +kernel
  have replay82_29 : fastPacked 3307 (candidateList 3307 7424 256)
      0x68900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068900068a00068a00068a00068a00068a00068a000 = true := by decide +kernel
  have replay82_30 : fastPacked 3307 (candidateList 3307 7680 256)
      0x688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000689000 = true := by decide +kernel
  have replay82_31 : fastPacked 3307 (candidateList 3307 7936 256)
      0x688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000 = true := by decide +kernel
  have replay82_32 : fastPacked 3307 (candidateList 3307 8192 256)
      0x687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000688000 = true := by decide +kernel
  have replay82_33 : fastPacked 3307 (candidateList 3307 8448 256)
      0x687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000 = true := by decide +kernel
  have replay82_34 : fastPacked 3307 (candidateList 3307 8704 256)
      0x686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000687000 = true := by decide +kernel
  have replay82_35 : fastPacked 3307 (candidateList 3307 8960 256)
      0x686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000 = true := by decide +kernel
  have replay82_36 : fastPacked 3307 (candidateList 3307 9216 256)
      0x685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000685000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000686000 = true := by decide +kernel
  have replay82_37 : fastPacked 3307 (candidateList 3307 9472 37)
      0x685000685000685000685000685000685000685000685000685000685000685000685000 = true := by decide +kernel
  have hs : p*p ≤ 3307^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 9509 := by
    have hc : (3307^3 : ℕ).sqrt = 190174 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 38 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay82_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_33 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_34 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_35 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_36 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay82_37 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked83 {p : ℕ} (hp : p.Prime) (hlo : 2*3347 < p)
    (hhi : p^2 < 3347^3) (hmod : p%3 ≠ 3347%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3347 d = true := by
  have replay83_0 : fastPacked 3347 (candidateList 3347 0 256)
      0 = true := by decide +kernel
  have replay83_1 : fastPacked 3347 (candidateList 3347 256 256)
      0x8d515d8ef1738f817b8fc17e90b18c9161959251a29371b293c1b79481c29551cd9621d99701e69881fb99820a99f2109a92199b021f9ba2299d52429e124d9ea255a00269a2628da412a6a4c2b1a6a2cea7e2e0aa1302ab1311adb339b2d389b453a0bc541e00054d00052e00051b0004fc0004b200049f0004930004740004420004040003d90003ba0003a700034a00032b00030c0002ff0002e00002c10002a2 = true := by decide +kernel
  have replay83_2 : fastPacked 3347 (candidateList 3347 512 256)
      0x79d06d79e06e79f06f7a10707a70747a80757a90757aa0767ab0767ac0777ac0777ad0787b007a7b107b7b407c7b507d7b607e7b90807bb0817bc0827c20867c30877c40887c808a7c908b7cb08c7cd08e7cf08f7d20917d30927d60947d80957dc0987e209c7e509e7e90a17ea0a27ee0a57f10a77f30a87f60aa7fa0ad7fd0b08000b28060b78080b880b0ba8100be8120c08130c18170c381e0c98200ca8250ce8280d082d0d48300d68310d78340d98390de8450e68490ea84b0eb84e0ed84f0ef8540f385c0f98610fd86d10787110a87310b87610e87e11488211788811c89012389412689612889a12c8a11318c014b8c514f8c8152 = true := by decide +kernel
  have replay83_3 : fastPacked 3347 (candidateList 3347 768 256)
      0x74003774103774103774203874203874303874303874403974403974503974603a74603a74703a74703a74803b74803b74903b74a03c74b03d74c03d74d03d74d03e74d03e74e03e74e03e74f03f75003f75104075104075304175704375904475a04575b04575d04675d04775e04775f04876004876104976304a76404b76504b76604c76704c76804c76904d76904d76a04e76d05076d05076f05177205377305377405477505477605577705577705677805677905777905777b05877e05a77f05a78005b78205c78305d78605f78806078806078a06178a06178d06378e06479006579106679306779406879506879606979606979a06c79b06c = true := by decide +kernel
  have replay83_4 : fastPacked 3347 (candidateList 3347 1024 256)
      0x71402271402271502271502271602271602271602371602371702371702371802371802371802371802371902471902471a02471a02471c02571c02571d02571d02671e02671e02671e02671f02772002772002772002772102772102872202872202872302872302972402972502972502972502972502a72702a72702a72702a72802b72902b72a02c72b02c72b02c72b02c72b02c72c02d72d02d72d02d72e02e72f02e72f02e73002e73002f73002f73102f73202f73203073303073403173503173503173703273803273803373903373a03373b03473b03473c03473d03573d03573e03673f036 = true := by decide +kernel
  have replay83_5 : fastPacked 3347 (candidateList 3347 1280 256)
      0x6f80166f80166f80166f80166f90176f90176f90176f90176fa0176fa0176fa0176fa0176fb0176fb0176fb0186fc0186fc0186fd0186fd0186fd0186fd0186fd0186fe0186fe0186fe0196ff0196ff0196ff0196ff01970001970001970001970001970001a70101a70101a70101a70101a70101a70201a70201a70301a70301b70401b70401b70401b70401b70501b70501b70501b70501b70501c70601c70601c70701c70701c70801c70801c70801d70801d70901d70901d70a01d70a01d70a01d70a01e70b01e70b01e70c01e70c01e70c01e70d01f70e01f70e01f70e01f70f01f70f01f70f01f70f020710020710020711020711020711021712021713021 = true := by decide +kernel
  have replay83_6 : fastPacked 3347 (candidateList 3347 1536 256)
      0x6e60106e60106e70106e70106e70106e70106e80106e80106e80116e80116e80116e80116e80116e90116e90116e90116e90116e90116ea0116ea0116ea0116ea0116ea0116eb0116eb0116eb0126eb0126eb0126eb0126ec0126ec0126ec0126ed0126ed0126ed0126ed0126ed0126ed0126ee0136ee0136ee0136ee0136ef0136ef0136ef0136ef0136f00136f00136f00136f00136f00136f00146f10146f10146f10146f10146f20146f20146f20146f20146f20146f30146f30156f40156f40156f40156f40156f40156f50156f50156f50156f50156f50156f60156f60156f60156f60166f70166f70166f70166f70166f8016 = true := by decide +kernel
  have replay83_7 : fastPacked 3347 (candidateList 3347 1792 256)
      0x6d900c6d900c6d900c6d900c6d900c6d900c6d900c6d900c6da00c6da00c6da00c6da00c6da00c6da00c6da00c6da00c6db00c6db00c6db00c6db00d6db00d6db00d6dc00d6dc00d6dc00d6dc00d6dc00d6dc00d6dd00d6dd00d6dd00d6dd00d6dd00d6dd00d6de00d6de00d6de00d6de00d6de00e6de00e6df00e6df00e6df00e6df00e6df00e6df00e6e000e6e000e6e000e6e000e6e000e6e100e6e100e6e100e6e100e6e100e6e100e6e100e6e100e6e100e6e200f6e200f6e200f6e200f6e300f6e300f6e300f6e300f6e300f6e300f6e300f6e400f6e400f6e400f6e400f6e400f6e50106e50106e50106e50106e50106e50106e5010 = true := by decide +kernel
  have replay83_8 : fastPacked 3347 (candidateList 3347 2048 256)
      0x6cf0096cf0096cf0096cf0096cf0096cf0096cf0096d00096d00096d00096d00096d00096d00096d00096d00096d000a6d100a6d100a6d100a6d100a6d100a6d100a6d100a6d100a6d100a6d100a6d100a6d100a6d200a6d200a6d200a6d200a6d200a6d200a6d200a6d300a6d300a6d300a6d300a6d300a6d300a6d300a6d400a6d400a6d400a6d400b6d400b6d400b6d400b6d400b6d500b6d500b6d500b6d500b6d500b6d500b6d500b6d500b6d500b6d500b6d500b6d600b6d600b6d600b6d600b6d600b6d600b6d600b6d600b6d600b6d600b6d600b6d700b6d700b6d700b6d700b6d700b6d700b6d700b6d700b6d700b6d700b6d800c6d800c6d800c6d800c6d800c6d800c6d800c = true := by decide +kernel
  have replay83_9 : fastPacked 3347 (candidateList 3347 2304 256)
      0x6c70076c70076c80076c80076c80076c80076c80076c80076c80076c80076c80076c80076c80076c80076c80076c80076c80076c80086c90086c90086c90086c90086c90086c90086c90086c90086c90086c90086c90086ca0086ca0086ca0086ca0086ca0086ca0086ca0086ca0086ca0086ca0086ca0086ca0086cb0086cb0086cb0086cb0086cb0086cb0086cb0086cb0086cb0086cb0086cc0086cc0086cc0086cc0086cc0086cc0086cc0086cc0086cd0096cd0096cd0096cd0096cd0096cd0096cd0096cd0096cd0096cd0096cd0096ce0096ce0096ce0096ce0096ce0096ce0096ce0096ce0096ce0096ce0096ce0096cf0096cf009 = true := by decide +kernel
  have replay83_10 : fastPacked 3347 (candidateList 3347 2560 256)
      0x6c10066c10066c10066c10066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c20066c30066c30066c30066c30066c30066c30066c30066c30066c30066c30066c30066c30066c40066c40066c40066c40066c40066c40066c40066c40076c40076c40076c40076c40076c50076c50076c50076c50076c50076c50076c50076c50076c50076c50076c50076c50076c60076c60076c60076c60076c60076c60076c60076c60076c60076c60076c60076c60076c60076c60076c70076c70076c70076c70076c70076c70076c70076c70076c7007 = true := by decide +kernel
  have replay83_11 : fastPacked 3347 (candidateList 3347 2816 256)
      0x6bc0056bc0056bc0056bc0056bc0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056bd0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056be0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056bf0056c00056c00056c00056c00066c00066c00066c00066c00066c00066c00066c00066c00066c00066c00066c00066c00066c10066c10066c10066c10066c10066c10066c10066c10066c10066c10066c10066c1006 = true := by decide +kernel
  have replay83_12 : fastPacked 3347 (candidateList 3347 3072 256)
      0x6b80046b80046b80046b80046b80046b80046b80046b80046b80046b80046b80046b80046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046b90046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046ba0046bb0046bb0046bb0046bb0046bb0046bb0046bb0046bb0056bb0056bb0056bb0056bb0056bb0056bb0056bb0056bb0056bb0056bb0056bc0056bc0056bc0056bc0056bc0056bc0056bc0056bc0056bc0056bc0056bc0056bc0056bc0056bc005 = true := by decide +kernel
  have replay83_13 : fastPacked 3347 (candidateList 3347 3328 256)
      0x6b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50036b50046b50046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b60046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b70046b80046b80046b80046b80046b80046b80046b80046b80046b80046b80046b8004 = true := by decide +kernel
  have replay83_14 : fastPacked 3347 (candidateList 3347 3584 256)
      0x6b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b20036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b30036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b40036b5003 = true := by decide +kernel
  have replay83_15 : fastPacked 3347 (candidateList 3347 3840 256)
      0x6af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b00036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b10036b2003 = true := by decide +kernel
  have replay83_16 : fastPacked 3347 (candidateList 3347 4096 256)
      0x6ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ad0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026ae0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af0026af002 = true := by decide +kernel
  have replay83_17 : fastPacked 3347 (candidateList 3347 4352 256)
      0x6ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ac0026ad0026ad0026ad0026ad0026ad0026ad002 = true := by decide +kernel
  have replay83_18 : fastPacked 3347 (candidateList 3347 4608 256)
      0x6a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026aa0026ab0026ab0026ab0026ab0026ab0026ab0026ab0026ab002 = true := by decide +kernel
  have replay83_19 : fastPacked 3347 (candidateList 3347 4864 256)
      0x6a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80016a80026a80026a80026a80026a80026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a90026a9002 = true := by decide +kernel
  have replay83_20 : fastPacked 3347 (candidateList 3347 5120 256)
      0x6a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a70016a7001 = true := by decide +kernel
  have replay83_21 : fastPacked 3347 (candidateList 3347 5376 256)
      0x6a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a50016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a60016a6001 = true := by decide +kernel
  have replay83_22 : fastPacked 3347 (candidateList 3347 5632 256)
      0x6a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a40016a50016a5001 = true := by decide +kernel
  have replay83_23 : fastPacked 3347 (candidateList 3347 5888 256)
      0x6a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a30016a3001 = true := by decide +kernel
  have replay83_24 : fastPacked 3347 (candidateList 3347 6144 256)
      0x6a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a20016a2001 = true := by decide +kernel
  have replay83_25 : fastPacked 3347 (candidateList 3347 6400 256)
      0x6a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a10016a1001 = true := by decide +kernel
  have replay83_26 : fastPacked 3347 (candidateList 3347 6656 256)
      0x6a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a00016a0001 = true := by decide +kernel
  have replay83_27 : fastPacked 3347 (candidateList 3347 6912 256)
      0x69f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00169f00169f00169f00169f0016a00016a00016a0001 = true := by decide +kernel
  have replay83_28 : fastPacked 3347 (candidateList 3347 7168 256)
      0x69e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f00069f000 = true := by decide +kernel
  have replay83_29 : fastPacked 3347 (candidateList 3347 7424 256)
      0x69d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e00069e000 = true := by decide +kernel
  have replay83_30 : fastPacked 3347 (candidateList 3347 7680 256)
      0x69d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d000 = true := by decide +kernel
  have replay83_31 : fastPacked 3347 (candidateList 3347 7936 256)
      0x69c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d00069d000 = true := by decide +kernel
  have replay83_32 : fastPacked 3347 (candidateList 3347 8192 256)
      0x69c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c000 = true := by decide +kernel
  have replay83_33 : fastPacked 3347 (candidateList 3347 8448 256)
      0x69b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c00069c000 = true := by decide +kernel
  have replay83_34 : fastPacked 3347 (candidateList 3347 8704 256)
      0x69b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b000 = true := by decide +kernel
  have replay83_35 : fastPacked 3347 (candidateList 3347 8960 256)
      0x69a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b00069b000 = true := by decide +kernel
  have replay83_36 : fastPacked 3347 (candidateList 3347 9216 256)
      0x69a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a000 = true := by decide +kernel
  have replay83_37 : fastPacked 3347 (candidateList 3347 9472 210)
      0x69900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069900069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a00069a000 = true := by decide +kernel
  have hs : p*p ≤ 3347^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 9682 := by
    have hc : (3347^3 : ℕ).sqrt = 193634 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 38 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay83_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_33 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_34 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_35 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_36 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay83_37 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked86 {p : ℕ} (hp : p.Prime) (hlo : 2*3467 < p)
    (hhi : p^2 < 3467^3) (hmod : p%3 ≠ 3467%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3467 d = true := by
  have replay86_0 : fastPacked 3467 (candidateList 3467 0 256)
      0 = true := by decide +kernel
  have replay86_1 : fastPacked 3467 (candidateList 3467 256 256)
      0x95d19997d1b59881bf98d1c39a01d59ad1e09c01f19d82069de20c9ee21a9fe229a10239a2224ba42268a5827ca61285a6f292a7929ba882aaaaf2ceac12dface2ebaef30bb2d346b5b372b6f386ba93bebd13e5c25438c50462d015110005710005650005330004e90004ca0004b700049800044e00043b00042f0004100003de0003a00003750003560003430002e50002c6 = true := by decide +kernel
  have replay86_2 : fastPacked 3467 (candidateList 3467 512 256)
      0x7f207b7f407c7f507d7f707f7fe0837ff08480008480108580208680308780408780508880808a80908b80c08d80e08e80f08f81209181409381509381c09881e09981f09a82309d82409d82609f8290a182a0a282e0a58300a68320a88350aa8390ad8410b28440b48480b784a0b984e0bc8510be8530c08570c285b0c685f0c88620cb8690d186c0d286f0d58750d98770db8790dc87d0df8850e68870e888d0ec8900ee8960f38990f589b0f789e0f98a40fe8b11098b710d8b910f8bc1118be1138c41188cd11f8d31248e11308e51338e81358ec1388f51408f914490014990a15290f15691215891615c91e16394418394a18894d18b = true := by decide +kernel
  have replay86_3 : fastPacked 3467 (candidateList 3467 768 256)
      0x78c03e78c03e78d03e78e03f78e03f78f03f78f04079004079004079104079204179204179304179304279404279504279604379704479804479904579a04579a04579a04679b04679b04679d04779d04779e04879f0487a00497a504b7a704d7a804d7a904e7ab04f7ac0507ad0507ae0517af0517b00527b20537b40547b40547b50557b60567b70567b80577b90577ba0587bd05a7be05a7bf05b7c305d7c405e7c505e7c605f7c80607c80607c90617c90617ca0627cb0627cd0637d00667d10667d20667d40687d60697d906b7db06c7dc06d7dd06e7de06e7e10707e20717e40727e50737e70747e90757ea0767eb0767eb0777f007a7f107a = true := by decide +kernel
  have replay86_4 : fastPacked 3467 (candidateList 3467 1024 256)
      0x75b02675b02675c02675d02675d02775d02775e02775e02775f02775f02775f02875f02876002876002876002876102876202976202976402a76502a76502a76502a76602b76602b76702b76802b76802c76902c76902c76902c76a02d76a02d76b02d76c02d76c02e76d02e76e02e76e02e76e02f76e02f77002f77002f77003077203077203077303177403177403177503277503277503277603377703377803477903477903477a03477a03477b03577b03577c03577c03677d03677f03777f03778003778203878203978303978303978503a78603a78603b78703b78803c78903c78903c78b03d = true := by decide +kernel
  have replay86_5 : fastPacked 3467 (candidateList 3467 1280 256)
      0x73c01973d01973d01973d01973e01973e01973e01973e01a73f01a73f01a73f01a73f01a74001a74001a74001a74101a74101b74201b74201b74201b74201b74301b74301b74301b74301c74401c74401c74401c74501c74501c74601c74601c74601d74601d74601d74701d74701d74701d74701d74801d74801e74801e74901e74901e74a01e74a01e74a01e74b01e74b01f74b01f74b01f74c01f74c01f74c01f74d01f74e02074e02074e02074e02074f02075002175002175002175002175102175102175102175202175302275302275302275302275402375502375502375502375602375602375602375602475702475802475802475902475902575a025 = true := by decide +kernel
  have replay86_6 : fastPacked 3467 (candidateList 3467 1536 256)
      0x72901272a01272a01272a01272b01272b01272b01272b01272b01372b01372b01372c01372c01372c01372c01372c01372d01372d01372d01372e01372e01372e01372e01372e01472e01472e01472e01472f01472f01473001473001473001473101473101473101573101573101573101573201573201573201573201573301573301573301573301573401673401673401673401673401673501673501673501673501673601673601673601673601673601773701773701773801773801773801773801773901773901773901873901873a01873a01873a01873a01873a01873b01873b01873b01873c01873c01973c01973c019 = true := by decide +kernel
  have replay86_7 : fastPacked 3467 (candidateList 3467 1792 256)
      0x71b00d71b00d71b00d71b00d71b00d71c00d71c00d71c00e71c00e71c00e71c00e71c00e71c00e71d00e71d00e71d00e71d00e71d00e71d00e71e00e71e00e71e00e71e00e71e00e71e00e71e00e71f00e71f00e71f00f71f00f71f00f71f00f72000f72000f72000f72000f72000f72100f72100f72100f72100f72100f72200f72200f72200f722010722010723010723010723010723010723010724010724010724010724010724010724010724010724010725010725010725010725011726011726011726011726011726011726011726011727011727011727011727011728011728011728011728011728012728012728012729012 = true := by decide +kernel
  have replay86_8 : fastPacked 3467 (candidateList 3467 2048 256)
      0x71000a71000a71000a71000a71000a71100a71100a71100a71100a71100b71100b71100b71100b71200b71200b71200b71200b71200b71200b71200b71200b71300b71300b71300b71300b71300b71300b71300b71300b71300b71300b71300b71400b71400b71400b71400b71400b71400b71500b71500c71500c71500c71500c71600c71600c71600c71600c71600c71600c71600c71600c71700c71700c71700c71700c71700c71700c71700c71700c71700c71700c71800c71800c71800c71800c71800c71800c71800c71800c71800c71800d71800d71800d71900d71900d71900d71900d71900d71900d71900d71900d71900d71a00d71a00d71a00d71a00d71a00d71a00d71a00d = true := by decide +kernel
  have replay86_9 : fastPacked 3467 (candidateList 3467 2304 256)
      0x70800870800870800870800870800870800870900870900870900870900870900870900870900870900870900870900870900870900870900870a00870a00870a00970a00970a00970a00970a00970a00970a00970a00970a00970b00970b00970b00970b00970b00970b00970b00970b00970b00970b00970b00970b00970c00970c00970c00970c00970c00970c00970c00970c00970c00970d00970d00970d00970d00970d00970d00970e00a70e00a70e00a70e00a70e00a70e00a70e00a70e00a70e00a70e00a70f00a70f00a70f00a70f00a70f00a70f00a70f00a70f00a70f00a70f00a70f00a71000a71000a71000a71000a71000a = true := by decide +kernel
  have replay86_10 : fastPacked 3467 (candidateList 3467 2560 256)
      0x701007701007702007702007702007702007702007702007702007702007702007702007702007702007702007702007702007703007703007703007703007703007703007703007703007703007703007703007703007703007704007704007704007704007704007704007704007704007704007704007705007705007705007705007705007705007705007705007705007705007705007706008706008706008706008706008706008706008706008706008706008706008706008706008706008707008707008707008707008707008707008707008707008707008707008707008708008708008708008708008708008 = true := by decide +kernel
  have replay86_11 : fastPacked 3467 (candidateList 3467 2816 256)
      0x6fc0056fc0056fc0056fc0056fc0056fc0056fc0056fc0056fd0056fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fd0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066fe0066ff0066ff0066ff0066ff0066ff0066ff0066ff0066ff0066ff0066ff0066ff0066ff0066ff006700006700006700006700006700006700006700006700006700006700006700006700006700006700006701006701006701006701006701006701006701006701006701006701006701006701006701006701007701007 = true := by decide +kernel
  have replay86_12 : fastPacked 3467 (candidateList 3467 3072 256)
      0x6f80046f80046f80046f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f80056f90056f90056f90056f90056f90056f90056f90056f90056f90056f90056f90056f90056f90056f90056f90056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fa0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fb0056fc0056fc0056fc0056fc0056fc0056fc0056fc0056fc0056fc005 = true := by decide +kernel
  have replay86_13 : fastPacked 3467 (candidateList 3467 3328 256)
      0x6f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f40046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f50046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f60046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f70046f7004 = true := by decide +kernel
  have replay86_14 : fastPacked 3467 (candidateList 3467 3584 256)
      0x6f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f10036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20036f20046f20046f20046f20046f20046f20046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f30046f40046f40046f40046f40046f40046f4004 = true := by decide +kernel
  have replay86_15 : fastPacked 3467 (candidateList 3467 3840 256)
      0x6ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ee0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036ef0036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f00036f0003 = true := by decide +kernel
  have replay86_16 : fastPacked 3467 (candidateList 3467 4096 256)
      0x6eb0026eb0026eb0026eb0026eb0026eb0026eb0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0026ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ec0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ed0036ee0036ee0036ee0036ee0036ee0036ee003 = true := by decide +kernel
  have replay86_17 : fastPacked 3467 (candidateList 3467 4352 256)
      0x6e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026ea0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb0026eb002 = true := by decide +kernel
  have replay86_18 : fastPacked 3467 (candidateList 3467 4608 256)
      0x6e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e80026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e90026e9002 = true := by decide +kernel
  have replay86_19 : fastPacked 3467 (candidateList 3467 4864 256)
      0x6e50026e50026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e60026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e70026e7002 = true := by decide +kernel
  have replay86_20 : fastPacked 3467 (candidateList 3467 5120 256)
      0x6e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50016e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e50026e5002 = true := by decide +kernel
  have replay86_21 : fastPacked 3467 (candidateList 3467 5376 256)
      0x6e20016e20016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e30016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e40016e4001 = true := by decide +kernel
  have replay86_22 : fastPacked 3467 (candidateList 3467 5632 256)
      0x6e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e20016e2001 = true := by decide +kernel
  have replay86_23 : fastPacked 3467 (candidateList 3467 5888 256)
      0x6e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e10016e1001 = true := by decide +kernel
  have replay86_24 : fastPacked 3467 (candidateList 3467 6144 256)
      0x6df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e00016e0001 = true := by decide +kernel
  have replay86_25 : fastPacked 3467 (candidateList 3467 6400 256)
      0x6de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df0016df001 = true := by decide +kernel
  have replay86_26 : fastPacked 3467 (candidateList 3467 6656 256)
      0x6dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de0016de001 = true := by decide +kernel
  have replay86_27 : fastPacked 3467 (candidateList 3467 6912 256)
      0x6dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd0016dd001 = true := by decide +kernel
  have replay86_28 : fastPacked 3467 (candidateList 3467 7168 256)
      0x6db0006db0006db0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0006dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc0016dc001 = true := by decide +kernel
  have replay86_29 : fastPacked 3467 (candidateList 3467 7424 256)
      0x6db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db000 = true := by decide +kernel
  have replay86_30 : fastPacked 3467 (candidateList 3467 7680 256)
      0x6da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db0006db000 = true := by decide +kernel
  have replay86_31 : fastPacked 3467 (candidateList 3467 7936 256)
      0x6d90006d90006d90006d90006d90006d90006d90006d90006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da0006da000 = true := by decide +kernel
  have replay86_32 : fastPacked 3467 (candidateList 3467 8192 256)
      0x6d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d9000 = true := by decide +kernel
  have replay86_33 : fastPacked 3467 (candidateList 3467 8448 256)
      0x6d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d90006d9000 = true := by decide +kernel
  have replay86_34 : fastPacked 3467 (candidateList 3467 8704 256)
      0x6d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d8000 = true := by decide +kernel
  have replay86_35 : fastPacked 3467 (candidateList 3467 8960 256)
      0x6d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d80006d8000 = true := by decide +kernel
  have replay86_36 : fastPacked 3467 (candidateList 3467 9216 256)
      0x6d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d7000 = true := by decide +kernel
  have replay86_37 : fastPacked 3467 (candidateList 3467 9472 256)
      0x6d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d70006d7000 = true := by decide +kernel
  have replay86_38 : fastPacked 3467 (candidateList 3467 9728 256)
      0x6d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d6000 = true := by decide +kernel
  have replay86_39 : fastPacked 3467 (candidateList 3467 9984 224)
      0x6d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d60006d6000 = true := by decide +kernel
  have hs : p*p ≤ 3467^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 10208 := by
    have hc : (3467^3 : ℕ).sqrt = 204141 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 40 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay86_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_33 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_34 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_35 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_36 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_37 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_38 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay86_39 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked88 {p : ℕ} (hp : p.Prime) (hlo : 2*3547 < p)
    (hhi : p^2 < 3547^3) (hmod : p%3 ≠ 3547%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3547 d = true := by
  have replay88_0 : fastPacked 3547 (candidateList 3547 0 256)
      0 = true := by decide +kernel
  have replay88_1 : fastPacked 3547 (candidateList 3547 256 256)
      0x9b01bb9bb1c59c71cf9ce1d59da1e09e01e59ed1f19f51f8a0920aa12212a18218a38235a4323fa4a245a68261a9b290ac12b4acc2beadc2ceb18307b4a336b6234db8e377bc03a8bd73bebfc3e2c6c450caf4920005b30005810005750005620005560005180004e60004da0004c800046b00045e00043f00040d0004010003e20003cf0003c30003b00003a40003910003340003270003150002f50002d60002ca = true := by decide +kernel
  have replay88_2 : fastPacked 3547 (candidateList 3547 512 256)
      0x82c08682e08782f08883008883508b83508c83708d83d09183e09284009384209484209584609784909a84b09b84d09c84e09d85009e8520a08530a08560a28570a385c0a78620ab8630ac8640ad8650ae86b0b286e0b48700b58770ba8790bc87a0bd87f0c08890c888a0c988c0ca88e0cb8900cd8910ce8930cf8950d08980d389e0d88a30dc8a60dd8a90e08b10e68b30e88be0f08c00f28c40f58c70f78c90f98cd0fc8d00fe8da1068df10a8e110c8e410e8e91128eb1148f611d90712b90b12e90d13091913a92013f92b14893214e93915493c15694b16394f16795216a96817c97118498319398719798d19c99119f99b1a89ac1b7 = true := by decide +kernel
  have replay88_3 : fastPacked 3547 (candidateList 3547 768 256)
      0x7c10447c10447c30457c40457c40457c50467c60467c80487c90487ca0497cb0497cc04a7ce04b7cf04b7cf04c7d004c7d304e7d504f7d604f7d70507d70507d90517d90517da0527dd0547de0547df0557e00557e00567e20577e30577e40587e60597e705a7e805a7e905a7ea05b7ec05d7ed05d7ee05d7f005f7f30617f40617f50627f60627f70637f90657fa0657fb0667fd0677fe06780006980106980306a80306b80406b80606c80806e80906f80b07080c07080d07181207481307581507681507781607781807881b07a81c07b81e07c81f07d82107e82207f82307f82608182708282908382908482b085 = true := by decide +kernel
  have replay88_4 : fastPacked 3547 (candidateList 3547 1024 256)
      0x78a02878b02878b02878c02978c02978c02978c02978d02978d02978d02a78e02a78e02a78f02a79102b79102b79102b79202c79302c79302c79302c79402d79402d79502d79502d79602e79702e79702e79702e79802f79902f79a02f79a03079a03079b03079b03079b03079c03179e03179f03279f0327a00337a00337a10337a10337a20337a20337a30347a40347a40347a50357a60357a60367a80367a80367a80377a90377a90377a90377ab0387ad0397ae03a7ae03a7af03a7b003b7b103b7b103b7b203b7b203c7b303c7b303c7b403c7b403d7b503d7b603e7b703e7b803f7b803f7b903f7ba0407bb0417bc0417bc0417bd0417be0427be0427bf0427bf043 = true := by decide +kernel
  have replay88_5 : fastPacked 3547 (candidateList 3547 1280 256)
      0x76b01b76b01b76b01b76c01b76c01b76c01b76d01c76d01c76d01c76e01c76e01c76e01c76e01c76f01c76f01d77001d77001d77001d77101d77101d77101d77101d77201e77201e77201e77201e77301e77301e77301e77301e77401e77401e77401f77501f77501f77601f77601f77601f77601f77702077702077802077802077802077802077902077902177a02177a02177a02177b02177b02177b02177b02277c02277c02277d02277d02277e02377e02377f02377f02378002478002478002478102478102478202478202478202578302578402578402578502678502678602678602678602678702778702778802778802778902778902878902878a028 = true := by decide +kernel
  have replay88_6 : fastPacked 3547 (candidateList 3547 1536 256)
      0x75601375601375601375601375701375701375701375701375701475701475801475801475801475901475901475901475901475901475901475901475a01475a01475a01575a01575a01575a01575b01575b01575b01575b01575c01575c01575c01575c01575d01575d01675d01675d01675e01675e01675e01675e01675e01675f01675f01675f01675f01676001776001776001776001776101776101776201776201776201776201876301876301876301876301876301876301876401876401876401876401876501976501976501976601976601976601976601976601976701976701976801a76801a76801a76901a76901a76a01a76a01b76a01b = true := by decide +kernel
  have replay88_7 : fastPacked 3547 (candidateList 3547 1792 256)
      0x74700e74700e74700e74700e74700e74700e74800e74800e74800f74800f74800f74900f74900f74900f74900f74900f74900f74a00f74a00f74a00f74a00f74a00f74b00f74b00f74b00f74b00f74b01074b01074b01074c01074c01074c01074c01074c01074c01074d01074d01074d01074d01074d01074d01074d01074e01074e01074e01074e01174e01174f01174f01174f01174f011750011750011750011750011750011751011751011751011751011751012752012752012752012752012752012753012753012753012753012753012753012754012754012754012754013755013755013755013756013 = true := by decide +kernel
  have replay88_8 : fastPacked 3547 (candidateList 3547 2048 256)
      0x73c00b73c00b73c00b73c00b73c00b73c00b73c00b73d00b73d00b73d00b73d00b73e00c73e00c73e00c73e00c73e00c73e00c73e00c73e00c73e00c73f00c73f00c73f00c73f00c73f00c73f00c74000c74000c74000c74000c74000c74000c74000c74000c74000c74000c74000c74100c74100c74100c74100c74100c74100d74100d74200d74200d74200d74200d74200d74200d74200d74300d74300d74300d74300d74300d74300d74400d74400d74400d74400d74400d74400d74500d74500e74500e74500e74500e74500e74500e74500e74500e74500e74600e74600e74600e74600e74600e74600e74700e74700e = true := by decide +kernel
  have replay88_9 : fastPacked 3547 (candidateList 3547 2304 256)
      0x73300973300973300973300973400973400973400973400973400973400973400973400973500973500973500973500973500973500973500973500973500973500973600973600973600973600973600973600973600973600973600973600973600a73600a73600a73600a73700a73700a73700a73700a73700a73700a73700a73700a73700a73700a73700a73800a73800a73800a73800a73800a73800a73800a73800a73800a73900a73900a73900a73900a73900a73900a73900a73900a73900a73900a73a00a73a00a73a00a73a00a73a00b73a00b73a00b73a00b73a00b73b00b73b00b73b00b73b00b73b00b73b00b73b00b73b00b73b00b73c00b73c00b = true := by decide +kernel
  have replay88_10 : fastPacked 3547 (candidateList 3547 2560 256)
      0x72c00772c00772c00772c00772d00772d00772d00772d00772d00772d00772d00772d00772d00772d00772e00772e00772e00772e00772e00772e00772e00772e00772e00772e00872e00872e00872e00872e00872e00872f00872f00872f00872f00872f00872f00872f00872f00872f00872f00872f00872f00872f008730008730008730008730008730008730008730008730008730008730008731008731008731008731008731008731008731008731008731008732008732008732008732008732008732008732008732008732008732008732008732008732009732009732009733009733009733009733009733009733009733009733009 = true := by decide +kernel
  have replay88_11 : fastPacked 3547 (candidateList 3547 2816 256)
      0x72700672700672700672700672700672700672700672700672700672700672700672700672700672700672700672700672800672800672800672800672800672800672800672800672800672800672800672800672800672800672800672800672800672900672900672900672900672900672900672900672900672900672900672900672900672900672900672900672a00672a00672a00672a00672a00772a00772a00772a00772a00772a00772a00772a00772a00772a00772b00772b00772b00772b00772b00772b00772b00772b00772b00772b00772b00772b00772b00772b00772b00772c00772c00772c00772c00772c00772c00772c00772c00772c00772c007 = true := by decide +kernel
  have replay88_12 : fastPacked 3547 (candidateList 3547 3072 256)
      0x722005722005722005722005722005722005722005722005722005722005722005722005722005722005722005723005723005723005723005723005723005723005723005723005723005723005723005723005723005723005723005723005723005723005724005724005724005724005724005724005724005724005724005724005724005724005724005724005724005724005724005724005724005725005725005725005725005725005725005725005725005725005725005725005725005725005725006725006725006725006725006725006726006726006726006726006726006726006726006726006726006726006726006726006726006726006726006726006727006727006 = true := by decide +kernel
  have replay88_13 : fastPacked 3547 (candidateList 3547 3328 256)
      0x71e00471e00471e00471e00471e00471e00471e00471e00471e00471e00471e00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f00471f004720004720004720004720004720004720004720004720004720004720004720004720004720005720005720005720005720005720005720005720005721005721005721005721005721005721005721005721005721005721005721005721005721005721005721005721005721005721005721005722005722005722005722005722005722005722005 = true := by decide +kernel
  have replay88_14 : fastPacked 3547 (candidateList 3547 3584 256)
      0x71b00371b00371b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471b00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471c00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471d00471e00471e00471e00471e00471e00471e00471e00471e00471e004 = true := by decide +kernel
  have replay88_15 : fastPacked 3547 (candidateList 3547 3840 256)
      0x71800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371800371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371900371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a00371a003 = true := by decide +kernel
  have replay88_16 : fastPacked 3547 (candidateList 3547 4096 256)
      0x715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003716003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003717003718003 = true := by decide +kernel
  have replay88_17 : fastPacked 3547 (candidateList 3547 4352 256)
      0x713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002713002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002714002715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003715003 = true := by decide +kernel
  have replay88_18 : fastPacked 3547 (candidateList 3547 4608 256)
      0x711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002711002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002712002713002713002713002713002713002713002713002713002 = true := by decide +kernel
  have replay88_19 : fastPacked 3547 (candidateList 3547 4864 256)
      0x70f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002710002711002711002711002711002711002711002711002711002711002711002711002 = true := by decide +kernel
  have replay88_20 : fastPacked 3547 (candidateList 3547 5120 256)
      0x70d00170d00270d00270d00270d00270d00270d00270d00270d00270d00270d00270d00270d00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270e00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f00270f002 = true := by decide +kernel
  have replay88_21 : fastPacked 3547 (candidateList 3547 5376 256)
      0x70c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d00170d001 = true := by decide +kernel
  have replay88_22 : fastPacked 3547 (candidateList 3547 5632 256)
      0x70a00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170b00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c00170c001 = true := by decide +kernel
  have replay88_23 : fastPacked 3547 (candidateList 3547 5888 256)
      0x70900170900170900170900170900170900170900170900170900170900170900170900170900170900170900170900170900170900170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a00170a001 = true := by decide +kernel
  have replay88_24 : fastPacked 3547 (candidateList 3547 6144 256)
      0x708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001709001 = true := by decide +kernel
  have replay88_25 : fastPacked 3547 (candidateList 3547 6400 256)
      0x707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001708001 = true := by decide +kernel
  have replay88_26 : fastPacked 3547 (candidateList 3547 6656 256)
      0x706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001707001 = true := by decide +kernel
  have replay88_27 : fastPacked 3547 (candidateList 3547 6912 256)
      0x705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001706001 = true := by decide +kernel
  have replay88_28 : fastPacked 3547 (candidateList 3547 7168 256)
      0x704001704001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001705001 = true := by decide +kernel
  have replay88_29 : fastPacked 3547 (candidateList 3547 7424 256)
      0x704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001704001 = true := by decide +kernel
  have replay88_30 : fastPacked 3547 (candidateList 3547 7680 256)
      0x703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000704000 = true := by decide +kernel
  have replay88_31 : fastPacked 3547 (candidateList 3547 7936 256)
      0x702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000703000 = true := by decide +kernel
  have replay88_32 : fastPacked 3547 (candidateList 3547 8192 256)
      0x702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000 = true := by decide +kernel
  have replay88_33 : fastPacked 3547 (candidateList 3547 8448 256)
      0x701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000702000 = true := by decide +kernel
  have replay88_34 : fastPacked 3547 (candidateList 3547 8704 256)
      0x701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000701000 = true := by decide +kernel
  have replay88_35 : fastPacked 3547 (candidateList 3547 8960 256)
      0x700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000701000701000701000701000701000701000701000701000701000701000701000701000701000 = true := by decide +kernel
  have replay88_36 : fastPacked 3547 (candidateList 3547 9216 256)
      0x700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000700000 = true := by decide +kernel
  have replay88_37 : fastPacked 3547 (candidateList 3547 9472 256)
      0x6ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff000700000700000700000700000700000700000700000700000700000700000700000700000700000 = true := by decide +kernel
  have replay88_38 : fastPacked 3547 (candidateList 3547 9728 256)
      0x6ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff000 = true := by decide +kernel
  have replay88_39 : fastPacked 3547 (candidateList 3547 9984 256)
      0x6fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff0006ff000 = true := by decide +kernel
  have replay88_40 : fastPacked 3547 (candidateList 3547 10240 256)
      0x6fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe000 = true := by decide +kernel
  have replay88_41 : fastPacked 3547 (candidateList 3547 10496 67)
      0x6fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe0006fe000 = true := by decide +kernel
  have hs : p*p ≤ 3547^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 10563 := by
    have hc : (3547^3 : ℕ).sqrt = 211247 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 42 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay88_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_33 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_34 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_35 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_36 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_37 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_38 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_39 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_40 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay88_41 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked97 {p : ℕ} (hp : p.Prime) (hlo : 2*3907 < p)
    (hhi : p^2 < 3907^3) (hmod : p%3 ≠ 3907%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3907 d = true := by
  have replay97_0 : fastPacked 3907 (candidateList 3907 0 256)
      0 = true := by decide +kernel
  have replay97_1 : fastPacked 3907 (candidateList 3907 256 256)
      0xbc02e4bd92fbbf4314c04324c22340c2f34cc5136cc66381c9f3b7cba3d1ccd3e4d41454d6d47fd8e4a0e5656400061a0005e80005dc0005c900058c00056000054e00052f0005100005030004f10004c50004b300048700045600044900043600042a0003ec0003ba0003ae00039b00033d000331000312 = true := by decide +kernel
  have replay97_2 : fastPacked 3907 (candidateList 3907 512 256)
      0x93d0bd9400bf9410c09430c19480c69490c694c0c99540ce9550cf9590d295a0d395c0d49610d89650db9670dd96b0df96c0e096e0e29720e49730e59770e89790ea9800ef9880f598a0f698c0f898e0fa99610099a10399c1059a710d9a910f9ab1119b31169c11229c31239c61269c81279cb12a9cd12c9d012e9d21309d81349e013b9e81429ec1449f21499fe153a00155a11163a14165a1a16ba1f16fa21171a29177a2d17ba3c187a4418ea47191a4c195a5419ca5719fa691aea851c6a8b1cba8f1cfaa41e1aaf1ebac11fbacd205ad9210adf215af922db02235b0723ab2f25eb4026db6328eb6b294b7629fb7e2a7b932babb72db = true := by decide +kernel
  have replay97_3 : fastPacked 3907 (candidateList 3907 768 256)
      0x8ac05e8ac05e8af05f8af0608b00608b10618b20618b50638b70648b80658b90658bb0678bd0688be0698bf0698bf0698c406c8c606e8c706e8c906f8c906f8cb0718cc0718cd0728d10748d30758d30768d50778d60778d80798d90798db07a8dc07b8df07d8e007e8e107e8e30808e50818e60828e70828eb0858ef0878f00888f20898f208a8f308a8f708d8f808d8fa08f8fc0908fd0918ff09390109490309590509690509790709890b09a90d09c90f09d91009e91109f9190a491a0a591c0a691d0a791f0a89210aa9240ac9260ad9290af92b0b092d0b292e0b39300b49330b79350b89380ba9390ba93b0bc = true := by decide +kernel
  have replay97_4 : fastPacked 3907 (candidateList 3907 1024 256)
      0x86503786503786603886703886703886703886803886803986903986903986903986a03a86b03a86d03b86d03b86e03c86f03c87003c87003d87103d87103d87203e87203e87303e87403f87503f87503f87503f87604087704187904187904287a04287a04287a04287b04287c04387e04488004588004588104688104688204688204688304788304788504888604888604888704988904a88904a88b04b88b04b88c04b88c04c88c04c88d04c88f04d89204f89304f89405089505089505189605189705289805289805289905389a05389a05389b05489c05589e05589e0568a00578a10578a20588a30598a40598a505a8a605a8a705b8a805b8a805b8a905c8a905c = true := by decide +kernel
  have replay97_5 : fastPacked 3907 (candidateList 3907 1280 256)
      0x83c02483d02583d02583e02583f02583f02683f02684002684002684002684102684102684102784202784302784302784302784402884402884502884502884502884502884602884602984602984702984702984702984802984802a84802a84802a84a02a84a02b84a02b84b02b84b02b84b02b84c02b84c02b84d02c84d02c84e02c84e02c84e02c84f02d85002d85002d85102d85102e85102e85102e85202e85202e85302f85402f85402f85502f85503085603085703085803185803185803185903185903285a03285a03285b03285c03385d03385d03385e03485f03485f03485f034860035860035861035862036863036863036863036864037864037 = true := by decide +kernel
  have replay97_6 : fastPacked 3907 (candidateList 3907 1536 256)
      0x82201a82201a82301a82301a82301a82301a82401b82401b82401b82401b82401b82501b82501b82601b82601b82601b82601c82601c82601c82701c82701c82701c82701c82701c82801c82801c82801c82801c82901c82901d82901d82a01d82a01d82b01d82b01d82b01d82b01d82b01e82c01e82c01e82c01e82c01e82d01e82d01e82e01f82e01f82e01f82f01f82f01f82f01f82f01f83001f83002083102083102083102083202083202083202083302083302083302183302183402183402183502183502183502283502283602283602283702283702283702283702283702283802383902383902383902383a02483b02483b02483c02483c024 = true := by decide +kernel
  have replay97_7 : fastPacked 3907 (candidateList 3907 1792 256)
      0x81001381001381001481001481001481001481001481001481101481101481101481101481201481201481201481201481201481301581301581301581401581401581401581401581401581401581501581501581501581501581601581601681601681601681601681601681701681701681701681701681701681801681801681801681801681901781901781901781a01781a01781a01781b01781b01781b01781b01781b01881c01881c01881c01881c01881d01881d01881d01881d01881e01881e01881e01981e01981f01981f01981f01981f01981f01982001982001982001982101a82101a82101a82201a = true := by decide +kernel
  have replay97_8 : fastPacked 3907 (candidateList 3907 2048 256)
      0x80200f80200f80200f80200f80200f80200f80200f80300f80300f80301080301080401080401080401080401080401080401080401080401080501080501080501080501080601080601080601080601080601080601080601180701180701180701180701180701180701180701180801180801180801180801180801180801180901180901180901180901180901180a01180a01280a01280a01280a01280a01280b01280b01280b01280b01280b01280c01280c01280c01280c01280c01280d01280d01380d01380d01380d01380d01380d01380e01380e01380e01380e01380e01380f01380f01380f01380f01380f013 = true := by decide +kernel
  have replay97_9 : fastPacked 3907 (candidateList 3907 2304 256)
      0x7f700c7f700c7f700c7f700c7f700c7f700c7f800c7f800c7f800c7f800c7f800c7f800c7f900c7f900c7f900c7f900c7f900d7f900d7f900d7f900d7fa00d7fa00d7fa00d7fa00d7fa00d7fa00d7fa00d7fa00d7fa00d7fa00d7fb00d7fb00d7fb00d7fb00d7fb00d7fb00d7fb00d7fb00d7fb00d7fb00d7fc00d7fc00d7fc00d7fc00d7fc00d7fc00d7fc00d7fc00d7fc00d7fc00e7fd00e7fd00e7fd00e7fd00e7fd00e7fd00e7fe00e7fe00e7fe00e7fe00e7fe00e7fe00e7fe00e7fe00e7fe00e7ff00e7ff00e7ff00e7ff00e7ff00e7ff00e80000e80000e80000e80000f80000f80000f80000f80000f80100f80100f80100f80100f80100f80100f80100f = true := by decide +kernel
  have replay97_10 : fastPacked 3907 (candidateList 3907 2560 256)
      0x7ee00a7ee00a7ee00a7ee00a7ef00a7ef00a7ef00a7ef00a7ef00a7ef00a7ef00a7ef00a7ef00a7f000a7f000a7f000a7f000a7f000a7f000a7f000a7f000a7f000a7f100a7f100a7f100a7f100a7f100a7f100a7f100a7f100a7f100a7f100a7f100a7f100a7f100b7f200b7f200b7f200b7f200b7f200b7f200b7f200b7f200b7f300b7f300b7f300b7f300b7f300b7f300b7f300b7f300b7f300b7f400b7f400b7f400b7f400b7f400b7f400b7f400b7f400b7f400b7f500b7f500b7f500b7f500b7f500b7f500b7f500b7f500c7f500c7f600c7f600c7f600c7f600c7f600c7f600c7f600c7f600c7f600c7f600c7f600c7f700c7f700c7f700c = true := by decide +kernel
  have replay97_11 : fastPacked 3907 (candidateList 3907 2816 256)
      0x7e70087e70087e70087e70087e70087e70087e70087e80087e80087e80087e80087e80087e80087e80087e80087e80087e80087e90087e90087e90087e90087e90087e90087e90087e90087e90087e90087e90087e90087e90087e90097e90097ea0097ea0097ea0097ea0097ea0097ea0097ea0097ea0097ea0097ea0097ea0097ea0097eb0097eb0097eb0097eb0097eb0097eb0097eb0097eb0097eb0097eb0097eb0097ec0097ec0097ec0097ec0097ec0097ec0097ec0097ec0097ec0097ec0097ec0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ed0097ee0097ee00a7ee00a7ee00a7ee00a7ee00a7ee00a = true := by decide +kernel
  have replay97_12 : fastPacked 3907 (candidateList 3907 3072 256)
      0x7e10077e10077e10077e20077e20077e20077e20077e20077e20077e20077e20077e20077e20077e20077e20077e20077e20077e20077e20077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e30077e40077e40077e40077e40077e40077e40077e40077e40077e40077e40077e40077e40077e40077e40077e40077e50077e50077e50077e50077e50077e50077e50077e50077e50087e50087e50087e50087e50087e50087e50087e60087e60087e60087e60087e60087e60087e60087e60087e60087e60087e60087e60087e60087e60087e60087e70087e70087e70087e70087e70087e70087e70087e70087e7008 = true := by decide +kernel
  have replay97_13 : fastPacked 3907 (candidateList 3907 3328 256)
      0x7dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067dd0067de0067de0067de0067de0067de0067de0067de0067de0067de0067de0067de0067de0067de0067de0067de0067de0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067df0067e00067e00067e00067e00067e00067e00067e00067e00067e00067e00067e00067e00067e00067e00067e00067e10077e10077e10077e10077e10077e10077e10077e10077e10077e10077e10077e10077e1007 = true := by decide +kernel
  have replay97_14 : fastPacked 3907 (candidateList 3907 3584 256)
      0x7d80057d80057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057d90057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057da0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057db0057dc0057dc0057dc0057dc0057dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc0067dc006 = true := by decide +kernel
  have replay97_15 : fastPacked 3907 (candidateList 3907 3840 256)
      0x7d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d50047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60047d60057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d70057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d80057d8005 = true := by decide +kernel
  have replay97_16 : fastPacked 3907 (candidateList 3907 4096 256)
      0x7d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d20047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d30047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d40047d50047d50047d5004 = true := by decide +kernel
  have replay97_17 : fastPacked 3907 (candidateList 3907 4352 256)
      0x7cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037cf0037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d00037d10037d10037d10037d10037d10037d10037d10037d10037d10037d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d10047d1004 = true := by decide +kernel
  have replay97_18 : fastPacked 3907 (candidateList 3907 4608 256)
      0x7cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037cd0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037ce0037cf0037cf0037cf0037cf0037cf0037cf0037cf003 = true := by decide +kernel
  have replay97_19 : fastPacked 3907 (candidateList 3907 4864 256)
      0x7ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0037ca0037ca0037ca0037ca0037ca0037ca0037ca0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cb0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc0037cc003 = true := by decide +kernel
  have replay97_20 : fastPacked 3907 (candidateList 3907 5120 256)
      0x7c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027c90027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca0027ca002 = true := by decide +kernel
  have replay97_21 : fastPacked 3907 (candidateList 3907 5376 256)
      0x7c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c70027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c80027c8002 = true := by decide +kernel
  have replay97_22 : fastPacked 3907 (candidateList 3907 5632 256)
      0x7c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c50027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c60027c6002 = true := by decide +kernel
  have replay97_23 : fastPacked 3907 (candidateList 3907 5888 256)
      0x7c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c40027c50027c50027c50027c50027c5002 = true := by decide +kernel
  have replay97_24 : fastPacked 3907 (candidateList 3907 6144 256)
      0x7c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c30017c30017c30017c30017c30017c30017c30017c30017c30017c30017c30017c30017c30017c30017c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c30027c3002 = true := by decide +kernel
  have replay97_25 : fastPacked 3907 (candidateList 3907 6400 256)
      0x7c00017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c20017c2001 = true := by decide +kernel
  have replay97_26 : fastPacked 3907 (candidateList 3907 6656 256)
      0x7bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c00017c0001 = true := by decide +kernel
  have replay97_27 : fastPacked 3907 (candidateList 3907 6912 256)
      0x7be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf001 = true := by decide +kernel
  have replay97_28 : fastPacked 3907 (candidateList 3907 7168 256)
      0x7bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be001 = true := by decide +kernel
  have replay97_29 : fastPacked 3907 (candidateList 3907 7424 256)
      0x7bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd001 = true := by decide +kernel
  have replay97_30 : fastPacked 3907 (candidateList 3907 7680 256)
      0x7bb0017bb0017bb0017bb0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc001 = true := by decide +kernel
  have replay97_31 : fastPacked 3907 (candidateList 3907 7936 256)
      0x7bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb001 = true := by decide +kernel
  have replay97_32 : fastPacked 3907 (candidateList 3907 8192 256)
      0x7ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb001 = true := by decide +kernel
  have replay97_33 : fastPacked 3907 (candidateList 3907 8448 256)
      0x7b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017b90017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba001 = true := by decide +kernel
  have replay97_34 : fastPacked 3907 (candidateList 3907 8704 256)
      0x7b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90017b90017b90017b90017b90017b90017b90017b90017b9001 = true := by decide +kernel
  have replay97_35 : fastPacked 3907 (candidateList 3907 8960 256)
      0x7b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b9000 = true := by decide +kernel
  have replay97_36 : fastPacked 3907 (candidateList 3907 9216 256)
      0x7b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b8000 = true := by decide +kernel
  have replay97_37 : fastPacked 3907 (candidateList 3907 9472 256)
      0x7b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b7000 = true := by decide +kernel
  have replay97_38 : fastPacked 3907 (candidateList 3907 9728 256)
      0x7b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b7000 = true := by decide +kernel
  have replay97_39 : fastPacked 3907 (candidateList 3907 9984 256)
      0x7b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b6000 = true := by decide +kernel
  have replay97_40 : fastPacked 3907 (candidateList 3907 10240 256)
      0x7b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b6000 = true := by decide +kernel
  have replay97_41 : fastPacked 3907 (candidateList 3907 10496 256)
      0x7b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b5000 = true := by decide +kernel
  have replay97_42 : fastPacked 3907 (candidateList 3907 10752 256)
      0x7b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b5000 = true := by decide +kernel
  have replay97_43 : fastPacked 3907 (candidateList 3907 11008 256)
      0x7b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b4000 = true := by decide +kernel
  have replay97_44 : fastPacked 3907 (candidateList 3907 11264 256)
      0x7b30007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b4000 = true := by decide +kernel
  have replay97_45 : fastPacked 3907 (candidateList 3907 11520 256)
      0x7b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b3000 = true := by decide +kernel
  have replay97_46 : fastPacked 3907 (candidateList 3907 11776 256)
      0x7b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b3000 = true := by decide +kernel
  have replay97_47 : fastPacked 3907 (candidateList 3907 12032 179)
      0x7b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b3000 = true := by decide +kernel
  have hs : p*p ≤ 3907^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 12211 := by
    have hc : (3907^3 : ℕ).sqrt = 244210 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 48 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay97_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_33 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_34 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_35 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_36 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_37 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_38 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_39 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_40 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_41 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_42 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_43 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_44 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_45 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_46 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay97_47 (candidateP_mem hp hlo hhi hmod hres hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked98 {p : ℕ} (hp : p.Prime) (hlo : 2*3947 < p)
    (hhi : p^2 < 3947^3) (hmod : p%3 ≠ 3947%3) (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p 3947 d = true := by
  have replay98_0 : fastPacked 3947 (candidateList 3947 0 256)
      0 = true := by decide +kernel
  have replay98_1 : fastPacked 3947 (candidateList 3947 256 256)
      0xc2f337c94397cbd3beccf3cfd1f41dd5d459dcd4c7ebd5b40006600006410006220006030005e40005b300059400058700057500056800055600052a00051800050b0004ec0004bb00049c00048f00047000045e00043e0004320004130003e10003d50003a3000358000339000326 = true := by decide +kernel
  have replay98_2 : fastPacked 3947 (candidateList 3947 512 256)
      0x95d0c595e0c69610c89640ca96e0d29700d39720d49740d69750d69770d89780d997a0da97f0de9810df9850e39870e49890e598e0ea9920ec9940ee99f0f69a10f89a30f99a90fe9ab0ff9af1029b31069b51089bc10c9be10e9c31129c71159ce11b9da1249df1289e612e9e91319f11379f613b9f913e9ff142a07149a0d14ea13153a1f15da23160a2a166a3316da37171a3a173a41179a50186a55189a60193a64197a701a1a751a5a781a8a7e1aca8a1b7aa31cdaad1d5ab11d9ab71deabb1e2ac61ecad81fbae4206b02221b0a228b0f22db18234b2c246b3524eb4425db5b271b6527bb6c281b7728bb8a29cbe92f5bf8303c0230d = true := by decide +kernel
  have replay98_3 : fastPacked 3947 (candidateList 3947 768 256)
      0x8c405f8c40608c50608c60618c70618c70628c90628c90628ca0638cb0648cc0648cd0658ce0658cf0668d00678d00678d20688d40698d506a8d706b8d706b8d806b8d906c8d906c8da06d8dc06e8dd06e8de06f8df0708e10718e80758ec0788ed0798ef07a8f107b8f307c8f407d8f607e8f607f8f90808fb0828fe0838ff08490008590108690308790508890608890708a90c08d90d08d90f08e91409291509391709491909691b09791c09791d09891e09991f09a92009a92409c9290a092a0a192b0a192e0a49320a69350a99380ab93a0ac93c0ae93d0ae9420b29440b39470b59490b694b0b894e0ba94f0bb9510bc9520bd9590c295a0c3 = true := by decide +kernel
  have replay98_4 : fastPacked 3947 (candidateList 3947 1024 256)
      0x87f03a87f03a88003a88103b88103b88203b88203b88303c88403c88403c88403c88503d88503d88503d88603d88603d88803e88903f88b04088c04088c04088d04188d04188e04188f04289004289104389204389204389204489304489404489404589604689604689704689804789904789904789a04889c04989c04989d04989e04a89f04a8a004b8a204c8a204c8a204c8a304d8a304d8a504e8a504e8a804f8a804f8a90508aa0508aa0508ab0518ac0518ad0528ad0528ae0538b10548b10558b20558b50578b60578b70588b80588b90598bb05a8bb05a8bc05b8be05c8bf05c8c005d8c205e = true := by decide +kernel
  have replay98_5 : fastPacked 3947 (candidateList 3947 1280 256)
      0x85402685402685502685502685602685602785602785602785702785702785802785802885902885902885902885a02885b02985b02985c02985c02985c02985c02985d02a85d02a85d02a85e02a85f02a85f02b85f02b86002b86102b86102b86102b86102c86202c86202c86202c86202c86302c86402d86402d86402d86602e86602e86602e86702e86702e86802e86802f86802f86902f86902f86902f86a03086b03086c03086c03186c03186d03186d03186f03286f03286f03286f03287003287003387103387103387303487303487303487403487503587603587603587603687703687703687703687803687803687a03787a03787b03887c03887d039 = true := by decide +kernel
  have replay98_6 : fastPacked 3947 (candidateList 3947 1536 256)
      0x83901b83a01b83b01c83b01c83b01c83c01c83c01c83c01c83c01c83c01c83c01c83d01c83d01d83d01d83e01d83e01d83e01d83f01d83f01d83f01d84001d84001e84001e84001e84001e84101e84101e84101e84201e84201e84301f84301f84401f84401f84401f84401f84401f84501f84502084502084502084602084602084702084702084802184802184802184802184902184902184902184902184a02184a02284a02284b02284b02284b02284c02284c02284c02284e02384e02384e02384e02384f02384f024850024850024850024850024851024851024851025851025852025852025853025853025854026854026 = true := by decide +kernel
  have replay98_7 : fastPacked 3947 (candidateList 3947 1792 256)
      0x82601482601482601482601482701482701482701482701482701582701582801582801582801582801582901582901582901582901582901582a01582a01582a01582a01682a01682b01682b01682b01682b01682c01682c01682c01682c01682d01682d01782d01782d01782d01782e01782e01782f01782f01782f01782f01783001783001883001883001883101883101883101883101883201883201883201883201883201883201883301983301983301983301983401983401983401983501983501983501983501a83601a83601a83601a83601a83701a83701a83701a83701a83801a83801a83801b83801b83801b83801b83901b = true := by decide +kernel
  have replay98_8 : fastPacked 3947 (candidateList 3947 2048 256)
      0x81800f81801081801081801081801081801081901081901081901081901081901081901081901081a01081a01081a01081a01081a01081a01081a01081b01081b01081b01181b01181b01181b01181b01181b01181c01181c01181c01181c01181c01181d01181d01181d01181d01181d01181e01181e01281e01281e01281f01281f01281f01281f012820012820012820012820012820012820012820012821012821012821012821012821012821012821012821013822013822013822013822013822013822013822013822013823013823013823013823013823013823013823013824013824013824013824013824013824013825014825014825014825014825014825014826014 = true := by decide +kernel
  have replay98_9 : fastPacked 3947 (candidateList 3947 2304 256)
      0x80d00c80d00c80d00c80d00c80d00d80d00d80d00d80e00d80e00d80e00d80e00d80e00d80e00d80e00d80e00d80e00d80e00d80e00d80f00d80f00d80f00d80f00d80f00d80f00d80f00d80f00d81000d81000d81000d81000d81000d81000d81100d81100d81100d81100d81100e81100e81100e81100e81100e81100e81200e81200e81200e81200e81200e81200e81300e81300e81300e81300e81300e81300e81400e81400e81400e81400e81400e81400f81500f81500f81500f81500f81500f81500f81500f81600f81600f81600f81600f81600f81600f81600f81600f81600f81600f81700f81700f81700f81700f81700f81700f = true := by decide +kernel
  have replay98_10 : fastPacked 3947 (candidateList 3947 2560 256)
      0x80400a80400a80400a80400a80400a80400a80500a80500a80500a80500a80500a80500a80500a80500a80500a80500a80500a80500a80600a80600a80600a80600a80600b80600b80600b80600b80600b80600b80700b80700b80700b80700b80700b80700b80700b80800b80800b80800b80800b80800b80800b80800b80800b80800b80900b80900b80900b80900b80900b80900b80900b80900b80a00b80a00c80a00c80a00c80a00c80a00c80a00c80a00c80a00c80a00c80b00c80b00c80b00c80b00c80b00c80b00c80b00c80b00c80b00c80b00c80c00c80c00c80c00c80c00c80c00c80c00c80c00c80c00c80c00c = true := by decide +kernel
  have replay98_11 : fastPacked 3947 (candidateList 3947 2816 256)
      0x7fd0087fd0087fd0087fd0087fd0087fd0087fd0087fd0087fd0087fd0087fe0087fe0087fe0087fe0087fe0097fe0097fe0097fe0097fe0097fe0097fe0097fe0097ff0097ff0097ff0097ff0097ff0097ff0097ff0097ff0097ff0097ff0097ff0097ff00980000980000980000980000980000980000980000980000980000980000980000980100980100980100980100980100980100980100980100980100980100980100980200980200980200980200980200a80200a80200a80200a80200a80200a80200a80300a80300a80300a80300a80300a80300a80300a80300a80300a80300a80300a80300a80400a80400a80400a80400a80400a = true := by decide +kernel
  have replay98_12 : fastPacked 3947 (candidateList 3947 3072 256)
      0x7f70077f70077f70077f70077f70077f70077f70077f70077f70077f70077f70077f70077f80077f80077f80077f80077f80077f80077f80077f80077f80077f80077f80077f80077f80077f80077f90077f90077f90077f90077f90077f90077f90077f90077f90077f90077f90077f90087f90087fa0087fa0087fa0087fa0087fa0087fa0087fa0087fa0087fa0087fa0087fa0087fa0087fa0087fb0087fb0087fb0087fb0087fb0087fb0087fb0087fb0087fb0087fb0087fb0087fb0087fb0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fc0087fd0087fd0087fd008 = true := by decide +kernel
  have replay98_13 : fastPacked 3947 (candidateList 3947 3328 256)
      0x7f20067f20067f20067f20067f20067f20067f20067f20067f20067f20067f20067f20067f20067f20067f20067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f30067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f40067f50067f50067f50067f50067f50067f50067f50067f50077f50077f50077f50077f50077f50077f50077f50077f50077f50077f50077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f60077f70077f70077f7007 = true := by decide +kernel
  have replay98_14 : fastPacked 3947 (candidateList 3947 3584 256)
      0x7ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ee0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057ef0057f00057f00057f00057f00057f00057f00057f00057f00057f00057f00057f00067f00067f00067f00067f00067f00067f00067f00067f00067f00067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f10067f20067f20067f20067f2006 = true := by decide +kernel
  have replay98_15 : fastPacked 3947 (candidateList 3947 3840 256)
      0x7ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047ea0047eb0047eb0047eb0047eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057eb0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ec0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed0057ed005 = true := by decide +kernel
  have replay98_16 : fastPacked 3947 (candidateList 3947 4096 256)
      0x7e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e70047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e80047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047e90047ea0047ea0047ea0047ea0047ea0047ea0047ea004 = true := by decide +kernel
  have replay98_17 : fastPacked 3947 (candidateList 3947 4352 256)
      0x7e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e40037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50037e50047e50047e50047e50047e50047e50047e50047e50047e50047e50047e50047e50047e50047e50047e50047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e60047e6004 = true := by decide +kernel
  have replay98_18 : fastPacked 3947 (candidateList 3947 4608 256)
      0x7e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e20037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e30037e40037e40037e40037e40037e40037e4003 = true := by decide +kernel
  have replay98_19 : fastPacked 3947 (candidateList 3947 4864 256)
      0x7df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e00037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e10037e1003 = true := by decide +kernel
  have replay98_20 : fastPacked 3947 (candidateList 3947 5120 256)
      0x7dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027de0027df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df0037df003 = true := by decide +kernel
  have replay98_21 : fastPacked 3947 (candidateList 3947 5376 256)
      0x7db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dc0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd0027dd002 = true := by decide +kernel
  have replay98_22 : fastPacked 3947 (candidateList 3947 5632 256)
      0x7d90027d90027d90027d90027d90027d90027d90027d90027d90027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027da0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db0027db002 = true := by decide +kernel
  have replay98_23 : fastPacked 3947 (candidateList 3947 5888 256)
      0x7d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d90027d9002 = true := by decide +kernel
  have replay98_24 : fastPacked 3947 (candidateList 3947 6144 256)
      0x7d60017d60017d60017d60017d60017d60017d60017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70017d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d70027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d80027d8002 = true := by decide +kernel
  have replay98_25 : fastPacked 3947 (candidateList 3947 6400 256)
      0x7d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d60017d6001 = true := by decide +kernel
  have replay98_26 : fastPacked 3947 (candidateList 3947 6656 256)
      0x7d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d50017d5001 = true := by decide +kernel
  have replay98_27 : fastPacked 3947 (candidateList 3947 6912 256)
      0x7d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d40017d4001 = true := by decide +kernel
  have replay98_28 : fastPacked 3947 (candidateList 3947 7168 256)
      0x7d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d30017d3001 = true := by decide +kernel
  have replay98_29 : fastPacked 3947 (candidateList 3947 7424 256)
      0x7d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d20017d2001 = true := by decide +kernel
  have replay98_30 : fastPacked 3947 (candidateList 3947 7680 256)
      0x7d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d10017d1001 = true := by decide +kernel
  have replay98_31 : fastPacked 3947 (candidateList 3947 7936 256)
      0x7cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d00017d0001 = true := by decide +kernel
  have replay98_32 : fastPacked 3947 (candidateList 3947 8192 256)
      0x7ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf0017cf001 = true := by decide +kernel
  have replay98_33 : fastPacked 3947 (candidateList 3947 8448 256)
      0x7ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce001 = true := by decide +kernel
  have replay98_34 : fastPacked 3947 (candidateList 3947 8704 256)
      0x7cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017cd0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce0017ce001 = true := by decide +kernel
  have replay98_35 : fastPacked 3947 (candidateList 3947 8960 256)
      0x7cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd0007cd000 = true := by decide +kernel
  have replay98_36 : fastPacked 3947 (candidateList 3947 9216 256)
      0x7cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc000 = true := by decide +kernel
  have replay98_37 : fastPacked 3947 (candidateList 3947 9472 256)
      0x7cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc0007cc000 = true := by decide +kernel
  have replay98_38 : fastPacked 3947 (candidateList 3947 9728 256)
      0x7cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb000 = true := by decide +kernel
  have replay98_39 : fastPacked 3947 (candidateList 3947 9984 256)
      0x7ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb0007cb000 = true := by decide +kernel
  have replay98_40 : fastPacked 3947 (candidateList 3947 10240 256)
      0x7ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca000 = true := by decide +kernel
  have replay98_41 : fastPacked 3947 (candidateList 3947 10496 256)
      0x7c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca0007ca000 = true := by decide +kernel
  have replay98_42 : fastPacked 3947 (candidateList 3947 10752 256)
      0x7c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c9000 = true := by decide +kernel
  have replay98_43 : fastPacked 3947 (candidateList 3947 11008 256)
      0x7c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c90007c9000 = true := by decide +kernel
  have replay98_44 : fastPacked 3947 (candidateList 3947 11264 256)
      0x7c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c8000 = true := by decide +kernel
  have replay98_45 : fastPacked 3947 (candidateList 3947 11520 256)
      0x7c70007c70007c70007c70007c70007c70007c70007c70007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c80007c8000 = true := by decide +kernel
  have replay98_46 : fastPacked 3947 (candidateList 3947 11776 256)
      0x7c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c7000 = true := by decide +kernel
  have replay98_47 : fastPacked 3947 (candidateList 3947 12032 256)
      0x7c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c7000 = true := by decide +kernel
  have replay98_48 : fastPacked 3947 (candidateList 3947 12288 111)
      0x7c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c70007c7000 = true := by decide +kernel
  have hs : p*p ≤ 3947^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 12399 := by
    have hc : (3947^3 : ℕ).sqrt = 247970 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 49 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay98_0 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_1 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_2 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_3 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_4 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_5 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_6 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_7 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_8 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_9 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_10 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_11 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_12 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_13 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_14 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_15 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_16 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_17 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_18 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_19 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_20 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_21 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_22 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_23 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_24 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_25 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_26 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_27 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_28 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_29 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_30 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_31 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_32 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_33 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_34 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_35 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_36 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_37 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_38 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_39 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_40 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_41 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_42 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_43 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_44 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_45 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_46 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_47 (candidateP_mem hp hlo hhi hmod hres hbase hend)
  · exact fastPacked_sound replay98_48 (candidateP_mem hp hlo hhi hmod hres hbase hb)

private def validIndices : List ℕ := [1, 2, 5, 7, 8, 11, 13, 14, 19, 20, 22, 23, 29, 32, 35, 40, 41, 43, 44, 46, 47, 49, 50, 56, 58, 61, 67, 76, 79, 82, 83, 86, 88, 97, 98]

private theorem checkedIndices : (List.range 100).all
    (fun i => !possiblePrime (qFromIndex i) || validIndices.contains i) = true := by
  decide +kernel

private theorem index_mem {i : ℕ} (hi : i<100) (hq : (qFromIndex i).Prime) :
    i ∈ validIndices := by
  have h := List.all_eq_true.mp checkedIndices i (List.mem_range.mpr hi)
  have hs := prime_possiblePrime hq
  simpa [hs] using h

private theorem check_for_index {p i : ℕ} (hp : p.Prime) (hi : i<100)
    (hq : (qFromIndex i).Prime) (hlo : 2*qFromIndex i<p)
    (hhi : p^2<(qFromIndex i)^3) (hmod : p%3≠qFromIndex i%3)
    (hres : p%20=3 ∨ p%20=7) :
    ∃ d, signCertificate p (qFromIndex i) d = true := by
  have hvalid := index_mem hi hq
  simp only [validIndices, List.mem_cons, List.not_mem_nil, or_false] at hvalid
  rcases hvalid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked01 hp hlo hhi hmod hres
  · exact checked02 hp hlo hhi hmod hres
  · exact checked05 hp hlo hhi hmod hres
  · exact checked07 hp hlo hhi hmod hres
  · exact checked08 hp hlo hhi hmod hres
  · exact checked11 hp hlo hhi hmod hres
  · exact checked13 hp hlo hhi hmod hres
  · exact checked14 hp hlo hhi hmod hres
  · exact checked19 hp hlo hhi hmod hres
  · exact checked20 hp hlo hhi hmod hres
  · exact checked22 hp hlo hhi hmod hres
  · exact checked23 hp hlo hhi hmod hres
  · exact checked29 hp hlo hhi hmod hres
  · exact checked32 hp hlo hhi hmod hres
  · exact checked35 hp hlo hhi hmod hres
  · exact checked40 hp hlo hhi hmod hres
  · exact checked41 hp hlo hhi hmod hres
  · exact checked43 hp hlo hhi hmod hres
  · exact checked44 hp hlo hhi hmod hres
  · exact checked46 hp hlo hhi hmod hres
  · exact checked47 hp hlo hhi hmod hres
  · exact checked49 hp hlo hhi hmod hres
  · exact checked50 hp hlo hhi hmod hres
  · exact checked56 hp hlo hhi hmod hres
  · exact checked58 hp hlo hhi hmod hres
  · exact checked61 hp hlo hhi hmod hres
  · exact checked67 hp hlo hhi hmod hres
  · exact checked76 hp hlo hhi hmod hres
  · exact checked79 hp hlo hhi hmod hres
  · exact checked82 hp hlo hhi hmod hres
  · exact checked83 hp hlo hhi hmod hres
  · exact checked86 hp hlo hhi hmod hres
  · exact checked88 hp hlo hhi hmod hres
  · exact checked97 hp hlo hhi hmod hres
  · exact checked98 hp hlo hhi hmod hres

theorem bounded : OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H1 := by
  apply bounded_of_signCertificates
  intro p q hp hq hqBound hq8 hq5 hp4 hp5 hlo hhi hmod
  have hqValue := q_index_eq hq8 hq5
  have hi : q/40 < 100 := by omega
  have hqPrime : (qFromIndex (q/40)).Prime := by rwa [hqValue]
  have hlo' : 2*qFromIndex (q/40)<p := by rwa [hqValue]
  have hhi' : p^2<(qFromIndex (q/40))^3 := by rwa [hqValue]
  have hmod' : p%3≠qFromIndex (q/40)%3 := by rwa [hqValue]
  have h := check_for_index hp hi hqPrime hlo' hhi' hmod' (p_mod_twenty hp4 hp5)
  rwa [hqValue] at h


end A056777Bounded

theorem OMA.solution : OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H1 :=
  A056777Bounded.bounded
