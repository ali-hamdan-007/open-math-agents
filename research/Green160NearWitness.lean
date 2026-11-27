import Lean

/-!
An upper-bound case for W(3,13) on 160 positions, numbered 0 through 159.
The eight fixed positions agree with a 159-position progression-free coloring.
They cannot all agree in a 160-position progression-free coloring.

The checker tracks chosen color-0 points and a mask of the remaining candidates.
Each instruction either considers both colors at an unassigned point or checks
a 13-term progression with at most one possible color-0 point.
The bit-mask soundness arguments adapt Green14.W_3_12.R1.H3 by MrSeizy,
which in turn credits Vincent T. Mossman for the pair-exclusion checks.
-/

namespace OMA.Green160NearWitness

def extra (x y : Nat) : Nat :=
  let a := min x y
  let d := max x y - a
  if d = 0 then 0 else
    (1 <<< (a+2*d)) ||| (if d ≤ a then 1 <<< (a-d) else 0) |||
      (if d%2=0 then 1 <<< (a+d/2) else 0)

def removeMask (allowed bad : Nat) := allowed ^^^ (allowed &&& bad)

def bluePattern (a d : Nat) : Nat :=
  (List.range 13).foldr (fun t m => (1 <<< (a+t*d)) ||| m) 0

def NoTriple (R : Nat → Prop) := ∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False

theorem extra_safe {R : Nat → Prop} (h : NoTriple R) {x y t : Nat}
    (hx : R x) (hy : R y) (ht : R t) : (extra x y).testBit t = false := by
  suffices ordered : ∀ a d : Nat, 0 < d → R a → R (a+d) →
      t ≠ a+2*d ∧ (d ≤ a → t ≠ a-d) ∧ (d%2=0 → t ≠ a+d/2) by
    unfold extra
    rcases Nat.le_total x y with hxy | hyx
    · rw [Nat.min_eq_left hxy, Nat.max_eq_right hxy]
      dsimp only
      by_cases hz : y-x=0
      · simp [hz]
      have hb : R (x+(y-x)) := by simpa [Nat.add_sub_of_le hxy] using hy
      obtain ⟨h₁,h₂,h₃⟩ := ordered x (y-x) (by omega) hx hb
      simp only [if_neg hz]
      split <;> split <;> simp_all [Nat.shiftLeft_eq, Nat.testBit_two_pow] <;> omega
    · rw [Nat.min_eq_right hyx, Nat.max_eq_left hyx]
      dsimp only
      by_cases hz : x-y=0
      · simp [hz]
      have hb : R (y+(x-y)) := by simpa [Nat.add_sub_of_le hyx] using hx
      obtain ⟨h₁,h₂,h₃⟩ := ordered y (x-y) (by omega) hy hb
      simp only [if_neg hz]
      split <;> split <;> simp_all [Nat.shiftLeft_eq, Nat.testBit_two_pow] <;> omega
  intro a d hd ha hb
  refine ⟨fun he => h a d hd ha hb (he ▸ ht), ?_, ?_⟩
  · intro hle he
    apply h (a-d) d hd (he ▸ ht)
    · simpa [Nat.sub_add_cancel hle] using ha
    · rwa [show a - d + 2 * d = a+d by omega]
  · intro heven he
    apply h a (d/2) (by omega) ha (he ▸ ht)
    rwa [show a+2*(d/2)=a+d by omega]

theorem remove_safe {a b t : Nat} (ha : a.testBit t = true) (hb : b.testBit t = false) :
    (removeMask a b).testBit t = true := by simp [removeMask, Nat.testBit_xor, ha, hb]

def Mono (r : Nat → Bool) := ∃ (b : Bool) (a d : Nat), 0 < d ∧
  a + (if b then 12 else 2)*d < 160 ∧ ∀ t ≤ (if b then 12 else 2), r (a+t*d) = b

def Red (r : Nat → Bool) (x : Nat) := x < 160 ∧ r x = false

theorem noTriple {r : Nat → Bool} (hn : ¬ Mono r) : NoTriple (Red r) := by
  intro a d hd h₀ h₁ h₂
  apply hn
  refine ⟨false,a,d,hd,h₂.1,?_⟩
  intro t ht
  change t ≤ 2 at ht
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simpa [Red] using h₀.2
  · simpa [Red] using h₁.2
  · exact h₂.2

theorem pattern_has {t : Nat} (ht : t < 13) (a d : Nat) :
    (bluePattern a d).testBit (a+t*d) = true := by
  suffices ∀ xs : List Nat, t ∈ xs → (xs.foldr (fun i m : Nat => (1 <<< (a+i*d)) ||| m) 0).testBit (a+t*d) = true from
    this _ (List.mem_range.mpr ht)
  intro xs
  induction xs with
  | nil => simp
  | cons u xs ih =>
    intro hm
    rcases List.mem_cons.mp hm with rfl | h
    · simp [Nat.shiftLeft_eq]
    · simp [ih h]

def bases : Array Nat := #[1, 0x1fff, 0x1555555, 0x1249249249, 0x1111111111111, 0x1084210842108421, 0x1041041041041041041, 0x1020408102040810204081, 0x1010101010101010101010101, 0x1008040201008040201008040201, 0x1004010040100401004010040100401, 0x1002004008010020040080100200400801, 0x1001001001001001001001001001001001001, 0x1000800400200100080040020010008004002001]

theorem base_correct : ∀ d : Fin 14, bases[d.val]! = bluePattern 0 d.val := by decide +kernel

def pattern (a d : Nat) : Nat :=
  if 0 < d ∧ a + 12*d < 160 then bases[d]! <<< a else bases[1]!

def Hits (R : Nat → Prop) := ∀ a d, ∃ x, (pattern a d).testBit x = true ∧ R x

theorem shifted_hit {r : Nat → Bool} (hn : ¬ Mono r) {a d : Nat}
    (hd : 0 < d) (hb : a+12*d < 160) :
    ∃ x, ((bases[d]!) <<< a).testBit x = true ∧ Red r x := by
  apply Classical.byContradiction
  intro bad
  apply hn
  refine ⟨true,a,d,hd,hb,?_⟩
  intro t ht
  change t ≤ 12 at ht
  have hx : a+t*d < 160 := by have := Nat.mul_le_mul_right d ht; omega
  have hbit : ((bases[d]!) <<< a).testBit (a+t*d) = true := by
    rw [base_correct ⟨d,by omega⟩]
    simpa [Nat.testBit_shiftLeft, Nat.le_add_right] using pattern_has (by omega : t < 13) 0 d
  cases hh : r (a+t*d)
  · exact (bad ⟨_, hbit, hx, hh⟩).elim
  · rfl

theorem hits {r : Nat → Bool} (hn : ¬ Mono r) : Hits (Red r) := by
  intro a d
  unfold pattern
  split
  · rename_i h
    exact shifted_hit hn h.1 h.2
  · simpa using shifted_hit hn (a:=0) (d:=1) (by decide) (by decide)

def pairBans (p : Nat) : List Nat → Nat
  | [] => 0
  | q :: qs => extra p q ||| pairBans p qs

def pvAfter (rs : List Nat) (a p : Nat) : Nat :=
  removeMask a (pairBans p rs)

theorem pv_safe {R : Nat → Prop} (hn : NoTriple R) {rs : List Nat} {a p t : Nat}
    (hr : ∀ q ∈ rs, R q) (_bound : ∀ q, R q → q < 160)
    (hp : R p) (ht : R t) (ha : a.testBit t = true) :
    (pvAfter rs a p).testBit t = true := by
  apply remove_safe ha
  induction rs with
  | nil => simp [pairBans]
  | cons q qs ih =>
    have hq := hr q (by simp)
    have hqs := ih (fun x hx => hr x (by simp [hx]))
    simp [pairBans, extra_safe hn hp hq ht, hqs]

def erasePt (a p : Nat) := removeMask a (1 <<< p)

def Bad (s : List Nat × Nat) := ∀ R : Nat → Prop, NoTriple R → Hits R → (∀ q, R q → q < 160) →
    (∀ x ∈ s.1, R x) → (∀ x, R x → s.2.testBit x = true) → False

def gate (leaves : Array {s // Bad s}) (k : Nat) (rs : List Nat) (a : Nat) : Bool :=
  match leaves[k]? with
  | some leaf => leaf.val == (rs,a)
  | none => false

theorem gate_sound (leaves : Array {s // Bad s}) {R : Nat → Prop} (hn : NoTriple R) (hit : Hits R) (bound : ∀ q, R q → q < 160)
    (k : Nat) (rs : List Nat) (a : Nat) (hr : ∀ x ∈ rs, R x) (ha : ∀ x, R x → a.testBit x = true) :
    gate leaves k rs a ≠ true := by
  unfold gate
  split
  · rename_i leaf _
    intro hh
    have hbad := leaf.property
    rw [beq_iff_eq.mp hh] at hbad
    exact hbad R hn hit bound hr ha
  · decide

def forceN {α : Type} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)

theorem forceN_eq {α : Type} (x : Nat) (f : Nat → α) : forceN x f = f x := by cases x <;> rfl

def walk (leaves : Array {s // Bad s}) (tape : Nat) : Nat → Nat → List Nat → Nat → Nat
  | 0, _, _, _ => 0
  | gas+1, i, rs, a =>
    forceN a fun a => forceN i fun i =>
    forceN ((tape >>> (16*i)) % 65536) fun op =>
    if op ≥ 3000 then
      if gate leaves (op-3000) rs a then i+1 else 0
    else if op ≥ 256 then
      let rest := pattern ((op-256)%160) ((op-256)/160) &&& a
      if rest = 0 then i+1 else
      forceN rest.log2 fun p =>
      if rest = 1 <<< p then
        walk leaves tape gas (i+1) (p::rs) (pvAfter rs a p)
      else 0
    else
      let j := walk leaves tape gas (i+1) (op::rs) (pvAfter rs a op)
      if j = 0 then 0 else walk leaves tape gas j rs (erasePt a op)

theorem erase_safe {R : Nat → Prop} {a p t : Nat} (hp : ¬ R p) (ht : R t)
    (ha : a.testBit t = true) : (erasePt a p).testBit t = true := by
  apply remove_safe ha
  simp [Nat.shiftLeft_eq, (show p ≠ t by rintro rfl; exact hp ht)]

theorem walk_sound (leaves : Array {s // Bad s}) (tape : Nat)
    {R : Nat → Prop} (hn : NoTriple R) (hit : Hits R) (bound : ∀ q, R q → q < 160)
    (gas i : Nat) (rs : List Nat) (a : Nat)
    (hr : ∀ x ∈ rs, R x) (ha : ∀ x, R x → a.testBit x = true) :
    walk leaves tape gas i rs a = 0 := by
  induction gas generalizing i rs a with
  | zero => rfl
  | succ gas ih =>
    rw [walk]
    simp only [forceN_eq]
    generalize (tape >>> (16*i)) % 65536 = op
    split
    · simp [gate_sound leaves hn hit bound _ rs a hr ha]
    · split
      · obtain ⟨t,hb,ht⟩ := hit ((op-256)%160) ((op-256)/160)
        have hrest : ((pattern ((op-256)%160) ((op-256)/160)) &&& a).testBit t = true :=
          by simp [hb, ha t ht]
        split
        · rename_i he
          change pattern ((op-256)%160) ((op-256)/160) &&& a = 0 at he
          simp [he] at hrest
        · split
          · rename_i he
            rw [he, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow] at hrest
            have heq := of_decide_eq_true hrest
            exact ih _ _ _ (by simpa [heq] using And.intro ht hr)
              (fun u hu => pv_safe hn hr bound (heq.symm ▸ ht) hu (ha u hu))
          · rfl
      · split
        · rfl
        · rename_i hj
          by_cases hp : R op
          · exact (hj (ih _ _ _ (by simpa using And.intro hp hr)
              (fun u hu => pv_safe hn hr bound hp hu (ha u hu)))).elim
          · exact ih _ _ _ hr (fun u hu => erase_safe hp hu (ha u hu))

theorem certify {s : List Nat × Nat} (tape : Nat) (leaves : Array {s // Bad s})
    (ok : walk leaves tape 60 0 s.1 s.2 ≠ 0) : Bad s := by
  intro R hn hit bound hr ha
  exact ok (walk_sound leaves tape hn hit bound _ _ _ _ hr ha)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 150000000 in
private theorem checkedBranch : Bad ([98,96,89,71,70,66],0xfffffffb99fee76d9fe0cacf9fd7a3ebffffffff) := certify 0x105a3057b029b03a50269025201b401b101d20212058e057b0031062d032904540445026201ca0246022801a002210207021301a802f002fc043703a503a401ec03290057002f025e0570043203a4058c00320066042e032901ec01ca0268058c02620585005c01e8021001a80258026b02400603057406b2044103a404e104db02e002ab020a02a1024501b80256026b01d5002704d402c206a201d5026b042103a100370020044502a7021302320221029b020703320267025601d501d3035a01b00256022c0229038e03320757046b04f30037002504ed04d4046b02f9061305a906230332046b029d005b02560605020e03d304cf02e0042001d5060303a504ed029b020901d5020706c8002d0020002f003002e80207033201d304210383035202c502b8022c01a0035a02e8020703320037025e0440025801c60440001804410233020703480352025602180421038603a50300026b0243022001a5020e01d101b7033201c204e70256002f04d4062402ba0564003200300040045e05aa035a046803380420038304d401d10263061d03ac04db033801b801ca06ab01d50269061d06b201d50399006d002704ed044103ac057402fd06b20441003400390043004f02030590044a0590003403cb03a402f3020702fd01ce058205740269005b04f3034d022a0219021602ed020702f7029d025f01c9057b03cb0459038602a1021502130445005f003f01ea062304f30459004f032c02a4020301d20454092307f80744060502c201ae0590042502e002280345022101b70391026b025a01b9003101d504db02a401b101ab024502280221034b024d01d503450230022f02be021d01a801bd01af021602580040002d03cb01bd01d5024b03570216050c046b063c006f032c059003cb020300550459032c0203005700340056004902a4020302bd02b70383056d042e01c9058c058505720216032902b601c90585005f03ac045401c6038e04e107f4032c02a4020306ae005b058c05850034045e038a02c601d50582033e020703320210020e050c03ea046b02aa06bf06b601d5025a0254057706140031006d006606ae032c025e058c026806a00221042105740356035201c60343046b02a4032903000423038e01d502f4020301c60423025a0037058c05850034005c004e #[] (by decide +kernel)

/-- A 160-point coloring agreeing with these eight entries of the lower-bound
witness contains one of the required monochromatic progressions. -/
theorem forces_progression (r : Nat → Bool)
    (red : ∀ x ∈ [66,70,71,89,96,98], r x = false)
    (blue : ∀ x ∈ [77,93], r x = true) : Mono r := by
  apply Classical.byContradiction
  intro hn
  have known : ∀ x ∈ [98,96,89,71,70,66], Red r x := by
    intro x hx
    have hc : x = 98 ∨ x = 96 ∨ x = 89 ∨ x = 71 ∨ x = 70 ∨ x = 66 := by simpa using hx
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, red _ (by decide)⟩
  let initial : Nat := erasePt (erasePt (2^160-1) 77) 93
  let step (state : List Nat × Nat) (p : Nat) := (p :: state.1, pvAfter state.1 state.2 p)
  have mask_ok : ∀ x, Red r x → initial.testBit x = true := by
    have full : ∀ i : Fin 160, (2^160-1 : Nat).testBit i.val = true := by decide +kernel
    have b77 := blue 77 (by decide)
    have b93 := blue 93 (by decide)
    intro x hx
    exact erase_safe (by simp [Red,b93]) hx
      (erase_safe (by simp [Red,b77]) hx (full ⟨x,hx.1⟩))
  have restrict (s : List Nat × Nat) (p : Nat) (hp : Red r p)
      (hr : ∀ x ∈ s.1, Red r x)
      (ha : ∀ x, Red r x → s.2.testBit x = true) :
      ∀ x, Red r x → (step s p).2.testBit x = true :=
    fun x hx => pv_safe (noTriple hn) hr (fun _ h => h.1) hp hx (ha x hx)
  apply checkedBranch (Red r) (noTriple hn) (hits hn) (fun _ h => h.1) known
  have h66 := known 66 (by decide)
  have h70 := known 70 (by decide)
  have h71 := known 71 (by decide)
  have h89 := known 89 (by decide)
  have h96 := known 96 (by decide)
  have h98 := known 98 (by decide)
  have h1 := restrict ([],initial) 66 h66 (by simp) mask_ok
  have h2 := restrict (step ([],initial) 66) 70 h70 (by simp [step,h66]) h1
  have h3 := restrict (step (step ([],initial) 66) 70) 71 h71 (by simp [step,h66,h70]) h2
  have h4 := restrict (step (step (step ([],initial) 66) 70) 71) 89 h89 (by simp [step,h66,h70,h71]) h3
  have h5 := restrict (step (step (step (step ([],initial) 66) 70) 71) 89) 96 h96
    (by simp [step,h66,h70,h71,h89]) h4
  have h6 := restrict (step (step (step (step (step ([],initial) 66) 70) 71) 89) 96) 98 h98
    (by simp [step,h66,h70,h71,h89,h96]) h5
  have same : (step (step (step (step (step (step ([],initial) 66) 70) 71) 89) 96) 98).2 =
      0xfffffffb99fee76d9fe0cacf9fd7a3ebffffffff := by decide +kernel
  simpa only [same] using h6

theorem reflect_progression (r : Nat → Bool) (h : Mono (fun i => r (159-i))) : Mono r := by
  obtain ⟨b,a,d,hd,hend,hmono⟩ := h
  generalize hlength : (if b then 12 else 2) = k at hend hmono
  refine ⟨b,159-(a+k*d),d,hd,?_,?_⟩
  · rw [hlength]
    omega
  · rw [hlength]
    intro t ht
    have hle := Nat.mul_le_mul_right d ht
    have hh := hmono (k-t) (by omega)
    change r (159-(a+(k-t)*d)) = b at hh
    rw [Nat.sub_mul] at hh
    rwa [show 159-(a+(k*d-t*d)) = 159-(a+k*d)+t*d by omega] at hh

/-- Reflection excludes the corresponding eight assignments at the other end. -/
theorem reflected_forces_progression (r : Nat → Bool)
    (red : ∀ x ∈ [93,89,88,70,63,61], r x = false)
    (blue : ∀ x ∈ [82,66], r x = true) : Mono r := by
  apply reflect_progression
  apply forces_progression
  · intro x hx
    have hc : x = 66 ∨ x = 70 ∨ x = 71 ∨ x = 89 ∨ x = 96 ∨ x = 98 := by simpa using hx
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact red _ (by decide)
  · intro x hx
    have hc : x = 77 ∨ x = 93 := by simpa using hx
    rcases hc with rfl | rfl <;> exact blue _ (by decide)

end OMA.Green160NearWitness

#print axioms OMA.Green160NearWitness.forces_progression

#print axioms OMA.Green160NearWitness.reflected_forces_progression
