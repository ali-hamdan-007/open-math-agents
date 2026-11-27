import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

/-!
# Critical uniform hyperforests need not be tight

Open Problem Garden: https://www.openproblemgarden.org/op/are_critical_k_forests_tight

H. Gebauer, A. Gundert, R. A. Moser, and Y. Okamoto, *Not All Saturated 3-Forests Are Tight*,
Theorem 2.2 and Section 3, https://arxiv.org/abs/1109.3390.
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

/-- The published counterexample, with vertices relabeled from 1–6 to 0–5. -/
def counterexampleEdges : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3},
    {1, 2, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}}

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem forest : IsForest 3 counterexampleEdges := by
  unfold IsForest Rainbow
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem saturated : IsSaturated 3 counterexampleEdges := by
  unfold IsSaturated IsForest Rainbow
  decide +kernel

private theorem not_tight : ¬ IsTight 3 counterexampleEdges := by
  intro h
  let c (v : Fin 6) : Fin 3 := if v = 0 then 2 else if v = 5 then 0 else 1
  obtain ⟨e, he, hc⟩ := h c (by unfold Rainbow; decide +kernel)
  have hno : ∀ f ∈ counterexampleEdges, ¬ Rainbow c f := by
    unfold Rainbow
    decide +kernel
  exact hno e he hc

/-- There is a saturated uniform hyperforest that is not tight. Thus Strausz's question has a
negative answer, already for a 3-forest on six vertices. -/
theorem main :
    ∃ (n k : ℕ) (E : Finset (Finset (Fin n))), 2 < k ∧
      (∀ e ∈ E, e.card = k) ∧ IsForest k E ∧ IsSaturated k E ∧ ¬ IsTight k E := by
  refine ⟨6, 3, counterexampleEdges, by decide, ?_, forest, saturated, not_tight⟩
  decide +kernel

end OMA.S_opg_are_critical_k_forests_tight

#print axioms OMA.S_opg_are_critical_k_forests_tight.main
