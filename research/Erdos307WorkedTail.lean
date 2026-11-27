import Erdos307CofactorSquare
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

namespace Erdos307Structure

open Finset

/-- The first 58 primes, followed by the three fixed primes in the worked tail. -/
def workedTailBase : Finset ℕ :=
  ((range 272).filter Nat.Prime) ∪ {283,307,311}

private abbrev workedD : ℕ :=
  8556164953052023544892322984114403284457846469345358833070474639639598323273473515497029490499110122518107224564620370

private abbrev workedN : ℕ :=
  17187165334418816369682117404926920694018364962360056188171819315343864662226971626622274285914948624448686500021479289

private abbrev witnessPrime : ℕ := 2424113

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem worked_base_constants :
    denom workedTailBase = workedD ∧ numer workedTailBase = workedN := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem witness_prime : Nat.Prime witnessPrime := by
  norm_num [witnessPrime]

private theorem worked_residue_pow :
    ((132834 : ℕ) : ZMod witnessPrime) ^ 1212056 = ((2424112 : ℕ) : ZMod witnessPrime) := by
  change (132834 : ZMod 2424113) ^ 1212056 = 2424112
  reduce_mod_char

/-- The global minus-square is impossible for every added member, even
without imposing primality on that member. -/
theorem worked_tail_no_minus_square (q y : ℕ) :
    y ^ 2 ≠ (numer workedTailBase - 2 * denom workedTailBase) * q + denom workedTailBase := by
  intro h
  rw [worked_base_constants.1, worked_base_constants.2] at h
  let _ : Fact witnessPrime.Prime := ⟨witness_prime⟩
  have hminus : ((workedN - 2 * workedD : ℕ) : ZMod witnessPrime) = 0 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    norm_num [witnessPrime, workedN, workedD]
  have hd : (workedD : ZMod witnessPrime) = ((132834 : ℕ) : ZMod witnessPrime) := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    norm_num [witnessPrime, workedD]
  have hy := congrArg (fun n : ℕ => (n : ZMod witnessPrime)) h
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul] at hy
  rw [hminus, zero_mul, zero_add, hd] at hy
  have hz : (y : ZMod witnessPrime) ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hy
    exact (by decide : (0 : ZMod witnessPrime) ≠ ((132834 : ℕ) : ZMod witnessPrime)) hy
  have hp := congrArg (fun r : ZMod witnessPrime => r ^ 1212056) hy
  change ((y : ZMod witnessPrime)^2)^1212056 =
    (((132834 : ℕ) : ZMod witnessPrime)^1212056) at hp
  rw [← pow_mul, show 2*1212056 = witnessPrime - 1 by decide,
    ZMod.pow_card_sub_one_eq_one hz, worked_residue_pow] at hp
  exact (by decide : (1 : ZMod witnessPrime) ≠ ((2424112 : ℕ) : ZMod witnessPrime)) hp

#print axioms worked_tail_no_minus_square

end Erdos307Structure
