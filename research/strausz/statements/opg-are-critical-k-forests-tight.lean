import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

/-!
# Strausz’s conjecture on critical uniform hyperforests

Open Problem Garden: https://www.openproblemgarden.org/op/are_critical_k_forests_tight

H. Gebauer, A. Gundert, R. A. Moser, and Y. Okamoto, *Not All Saturated 3-Forests Are Tight*,
Section 2 defines colorings as surjective. Theorem 2.2 disproves the conjecture.
https://arxiv.org/abs/1109.3390.
-/

namespace OMA.S_opg_are_critical_k_forests_tight

/-- An edge uses every color in the specified palette. -/
def Rainbow {n k : ℕ} (c : Fin n → Fin k) (e : Finset (Fin n)) : Prop :=
  e.image c = Finset.univ

/-- Each edge can be the unique rainbow edge under a coloring with `k` colors. -/
def IsForest {n : ℕ} (k : ℕ) (E : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ E, ∃ c : Fin n → Fin k, ∀ f ∈ E, (Rainbow c f ↔ f = e)

/-- No missing `k`-edge on the same vertex set can be added while retaining the forest property. -/
def IsSaturated {n : ℕ} (k : ℕ) (E : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ (Finset.univ : Finset (Fin n)).powersetCard k, e ∉ E → ¬ IsForest k (insert e E)

/-- Every coloring using all `k` colors makes at least one edge rainbow. -/
def IsTight {n : ℕ} (k : ℕ) (E : Finset (Finset (Fin n))) : Prop :=
  ∀ c : Fin n → Fin k, Rainbow c Finset.univ → ∃ e ∈ E, Rainbow c e

/-- Every saturated `k`-forest is tight. The palette has positive size and the vertex set has
at least `k` vertices, so surjective `k`-colorings exist. -/
theorem main :
    ∀ (n k : ℕ) (E : Finset (Finset (Fin n))), 0 < k → k ≤ n →
      (∀ e ∈ E, e.card = k) → IsForest k E → IsSaturated k E → IsTight k E := by
  sorry

end OMA.S_opg_are_critical_k_forests_tight
