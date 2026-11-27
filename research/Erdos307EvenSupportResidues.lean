import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

namespace Erdos307Structure

private theorem finite_even_support_table :
    ∀ k m : Fin 4, ∀ w : Fin 8,
      w.val % 4 = (if m.val % 2 = 0 then 1 else 3) →
      (w.val * (1 + 2 * k.val + 4 * m.val)) % 8 = 5 →
      ((w.val = 1 ∨ w.val = 7) ↔ (m.val = 0 ∨ m.val = 1)) →
      (k.val + 4 - m.val) % 4 = 2 ∧
        w.val = (if k.val = 0 then 5 else if k.val = 1 then 3 else
          if k.val = 2 then 1 else 7) := by
  decide +kernel

/-- The parity table forced jointly by the odd-product mod-four identity,
the cofactor sum mod eight, and the quadratic-reciprocity sign. Here k is
the number of odd primes and m counts those which are three mod four. -/
theorem even_support_one_mod_four_count {k m W : ℕ} (hm : m ≤ k)
    (hProd : W % 4 = (if m % 2 = 0 then 1 else 3))
    (hDer : (W * (1 + 2 * k + 4 * m)) % 8 = 5)
    (hRec : (W % 8 = 1 ∨ W % 8 = 7) ↔ (m % 4 = 0 ∨ m % 4 = 1)) :
    (k - m) % 4 = 2 ∧
      W % 8 = (if k % 4 = 0 then 5 else if k % 4 = 1 then 3 else
        if k % 4 = 2 then 1 else 7) := by
  have hW4 : (W % 8) % 4 = W % 4 := by omega
  have hm2 : (m % 4) % 2 = m % 2 := by omega
  have hP : (W % 8) % 4 = (if (m % 4) % 2 = 0 then 1 else 3) := by
    rw [hW4, hm2, hProd]
  have hinner : (1 + 2 * k + 4 * m) % 8 =
      (1 + 2 * (k % 4) + 4 * (m % 4)) % 8 := by omega
  have hD : ((W % 8) * (1 + 2 * (k % 4) + 4 * (m % 4))) % 8 = 5 := by
    rw [Nat.mul_mod W _ 8, hinner] at hDer
    rw [Nat.mul_mod (W % 8) _ 8, Nat.mod_mod]
    exact hDer
  obtain ⟨hcount, hw⟩ := finite_even_support_table
    ⟨k % 4, Nat.mod_lt _ (by decide)⟩ ⟨m % 4, Nat.mod_lt _ (by decide)⟩
    ⟨W % 8, Nat.mod_lt _ (by decide)⟩ hP hD hRec
  refine ⟨?_, hw⟩
  change (k % 4 + 4 - m % 4) % 4 = 2 at hcount
  omega

#print axioms even_support_one_mod_four_count
end Erdos307Structure
