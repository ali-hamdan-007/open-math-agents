import TuplePell

namespace TuplePellIndex

/-- Bit `i` records whether `i` is the least nonnegative residue of a square. -/
private def squareMask (p : Nat) : Nat :=
  match p with
  | 349 => 0x1712f6dd431934322f97b5e7c22bc69f8844f65582340b106a9bc8847e58f510f9eb7a7d130b2630aedbd23b
  | 173 => 0x1299e1f15fb456f22411973a620913da8b7ea3e1e653
  | 61 => 0x1713e6940a59f23b
  | 269 => 0x1395a3708b9757f9bc90f253365005f1c528e3e8029b3293c24f67faba7443b16a73
  | 41 => 0x1b382b50737
  | _ => 0

private def MaskSound (p : Nat) : Prop :=
  ∀ r : Fin p, (squareMask p).testBit
    (((r : Nat) : Int) * ((r : Nat) : Int) % (p : Int)).toNat = true

private theorem mask_equation (p : Nat) (hp : 0 < p) (hs : MaskSound p)
    (a z : Int) (he : a = z * z) :
    (squareMask p).testBit (a % (p : Int)).toNat = true := by
  let r := (z % (p : Int)).toNat
  have hr : (r : Int) = z % (p : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))
  have hb : r < p := by
    have hb' := Int.emod_lt_of_pos z (show (0 : Int) < (p : Int) by omega)
    omega
  have h := hs ⟨r, hb⟩
  change (squareMask p).testBit (((r : Int) * (r : Int)) % (p : Int)).toNat = true at h
  rw [hr, ← Int.mul_emod z z (p : Int), ← he] at h
  exact h

private theorem mask349 : MaskSound 349 := by unfold MaskSound; decide +kernel
private theorem mask173 : MaskSound 173 := by unfold MaskSound; decide +kernel
private theorem mask61 : MaskSound 61 := by unfold MaskSound; decide +kernel
private theorem mask269 : MaskSound 269 := by unfold MaskSound; decide +kernel
private theorem mask41 : MaskSound 41 := by unfold MaskSound; decide +kernel

private def passes (x : Int) (p : Nat) : Bool :=
  (squareMask p).testBit ((8*x*x-7) % (p : Int)).toNat

private def passesAll (x : Int) : Bool :=
  passes x 349 && passes x 173 && passes x 61 && passes x 269 && passes x 41

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem checkedIndices : ∀ n : Fin 501,
    passesAll (TuplePell.three n.val).1 = true → n.val = 0 ∨ n.val = 2 :=
  by decide +kernel

/-- Both Pell branches must satisfy the same square equation. The finite modular
    sieve therefore excludes every index through 500 except 0 and 2. -/
theorem index_eq_zero_or_two (n : Nat) (z : Int) (hn : n ≤ 500)
    (he : 8*(TuplePell.three n).1*(TuplePell.three n).1-7 = z*z) :
    n = 0 ∨ n = 2 := by
  apply checkedIndices ⟨n, by omega⟩
  unfold passesAll passes
  rw [mask_equation 349 (by decide) mask349 _ z he,
    mask_equation 173 (by decide) mask173 _ z he,
    mask_equation 61 (by decide) mask61 _ z he,
    mask_equation 269 (by decide) mask269 _ z he,
    mask_equation 41 (by decide) mask41 _ z he]
  decide

theorem extension_eq_zero_or_120 (n : Nat) (d z : Int) (hn : n ≤ 500)
    (he : 8*(TuplePell.three n).1*(TuplePell.three n).1-7 = z*z)
    (hd : d = (TuplePell.three n).1*(TuplePell.three n).1-1) :
    d = 0 ∨ d = 120 := by
  rcases index_eq_zero_or_two n z hn he with rfl | rfl <;> simp [TuplePell.three] at hd <;>
    omega

end TuplePellIndex

#print axioms TuplePellIndex.index_eq_zero_or_two
#print axioms TuplePellIndex.extension_eq_zero_or_120
