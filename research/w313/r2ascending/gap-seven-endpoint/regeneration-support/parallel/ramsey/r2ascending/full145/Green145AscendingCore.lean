import Lean

namespace OMA.Green145AscendingCore

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
  a + (if b then 12 else 2)*d < 145 ∧ ∀ t ≤ (if b then 12 else 2), r (a+t*d) = b

def Red (r : Nat → Bool) (x : Nat) := x < 145 ∧ r x = false

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
  if 0 < d ∧ a + 12*d < 145 then bases[d]! <<< a else bases[1]!

def Hits (R : Nat → Prop) := ∀ a d, ∃ x, (pattern a d).testBit x = true ∧ R x

theorem shifted_hit {r : Nat → Bool} (hn : ¬ Mono r) {a d : Nat}
    (hd : 0 < d) (hb : a+12*d < 145) :
    ∃ x, ((bases[d]!) <<< a).testBit x = true ∧ Red r x := by
  apply Classical.byContradiction
  intro bad
  apply hn
  refine ⟨true,a,d,hd,hb,?_⟩
  intro t ht
  change t ≤ 12 at ht
  have hx : a+t*d < 145 := by have := Nat.mul_le_mul_right d ht; omega
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
    (hr : ∀ q ∈ rs, R q) (_bound : ∀ q, R q → q < 145)
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

def Bad (s : List Nat × Nat) := ∀ R : Nat → Prop, NoTriple R → Hits R → (∀ q, R q → q < 145) →
    (∀ x ∈ s.1, R x) → (∀ x, R x → s.2.testBit x = true) → False

def gate (leaves : Array {s // Bad s}) (k : Nat) (rs : List Nat) (a : Nat) : Bool :=
  match leaves[k]? with
  | some leaf => leaf.val == (rs,a)
  | none => false

theorem gate_sound (leaves : Array {s // Bad s}) {R : Nat → Prop} (hn : NoTriple R) (hit : Hits R) (bound : ∀ q, R q → q < 145)
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
    {R : Nat → Prop} (hn : NoTriple R) (hit : Hits R) (bound : ∀ q, R q → q < 145)
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

end OMA.Green145AscendingCore
