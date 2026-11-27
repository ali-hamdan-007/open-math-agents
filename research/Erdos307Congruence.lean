import Erdos307CrossCoprime
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

open Finset
open scoped BigOperators

namespace Erdos307Structure

private lemma cofactor_mul_cast (A : Finset ℕ) {a m : ℕ} (ha : a ∈ A) :
    ((denom A / a : ℕ) : ZMod m) * (a : ZMod m) = (denom A : ZMod m) := by
  have hdvd : a ∣ denom A :=
    ⟨denom (A.erase a), by simpa [denom, mul_comm] using (Finset.prod_erase_mul A id ha).symm⟩
  exact (Nat.cast_mul _ _).symm.trans
    (congrArg (fun n : ℕ => (n : ZMod m)) (Nat.div_mul_cancel hdvd))

private lemma denom_cast_isUnit {A : Finset ℕ} {m : ℕ}
    (hA : ∀ a ∈ A, a.Coprime m) : IsUnit (denom A : ZMod m) := by
  have hprod : (denom A).Coprime m := Nat.coprime_prod_left_iff.mpr hA
  simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime _ hprod).isUnit

/-- A common invertible square residue makes numerator divisibility equivalent
to divisibility of the sum of the denominators. The modulus may be a prime power. -/
theorem dvd_numer_iff_dvd_sum_of_common_square {A : Finset ℕ} {m u : ℕ}
    (hu : u.Coprime m) (hA : ∀ a ∈ A, a.Coprime m)
    (hsq : ∀ a ∈ A, (a : ZMod m) * a = (u : ZMod m) * u) :
    m ∣ numer A ↔ m ∣ ∑ a ∈ A, a := by
  have hu' : IsUnit (u : ZMod m) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime _ hu).isUnit
  have heq : ((u : ZMod m) * u) * (numer A : ZMod m) =
      (denom A : ZMod m) * (↑(∑ a ∈ A, a) : ZMod m) := by
    rw [numer, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← hsq a ha, mul_comm ((a : ZMod m) * a), ← mul_assoc, cofactor_mul_cast A ha]
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
  exact (hu'.mul hu').mul_right_eq_zero.symm.trans
    ((congrArg (· = 0) heq).to_iff.trans (denom_cast_isUnit hA).mul_right_eq_zero)

/-- If all members are in one invertible residue class, a cross-product equality
forces the same divisibility of the opposite product and this side's cardinality. -/
theorem dvd_denom_iff_dvd_card_of_common_residue {P Q : Finset ℕ} {m u : ℕ}
    (hu : u.Coprime m) (hQ : ∀ q ∈ Q, q.Coprime m)
    (hres : ∀ q ∈ Q, (q : ZMod m) = u) (hswap : numer Q = denom P) :
    m ∣ denom P ↔ m ∣ Q.card := by
  have hu' : IsUnit (u : ZMod m) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime _ hu).isUnit
  rw [← hswap, dvd_numer_iff_dvd_sum_of_common_square hu hQ
    (fun q hq => by rw [hres q hq]), ← ZMod.natCast_eq_zero_iff,
    ← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
  have heq : (∑ q ∈ Q, (q : ZMod m)) = (u : ZMod m) * Q.card := by
    calc
      _ = ∑ _q ∈ Q, (u : ZMod m) := Finset.sum_congr rfl hres
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [heq, hu'.mul_right_eq_zero]

/-- A divisor of the opposite product larger than the side's cardinality
rules out uniform invertible residues on that side. -/
theorem no_common_residue_of_card_lt_divisor {P Q : Finset ℕ} {m u : ℕ}
    (hQpos : Q.Nonempty) (hlt : Q.card < m)
    (hm : m ∣ denom P) (hu : u.Coprime m) (hQ : ∀ q ∈ Q, q.Coprime m)
    (hswap : numer Q = denom P) :
    ¬ ∀ q ∈ Q, (q : ZMod m) = u := by
  intro hres
  have hd := (dvd_denom_iff_dvd_card_of_common_residue hu hQ hres hswap).mp hm
  exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd hQpos.card_pos hd)

end Erdos307Structure
