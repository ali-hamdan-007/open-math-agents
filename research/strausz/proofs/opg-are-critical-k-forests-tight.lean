import OMAStatements.S_opg_are_critical_k_forests_tight

/-!
# Counterexample to Strausz’s conjecture on critical uniform hyperforests

The six-vertex 3-forest of Gebauer, Gundert, Moser and Okamoto is saturated and has a
surjective 3-coloring without a rainbow edge. We verify the finite certificate in the kernel.

Source: https://arxiv.org/abs/1109.3390, Theorem 2.2 and Section 3.
-/

namespace OMA.CriticalForestsCounterexample

open OMA.S_opg_are_critical_k_forests_tight

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

theorem counterexample :
    ∃ E : Finset (Finset (Fin 6)),
      (∀ e ∈ E, e.card = 3) ∧ IsForest 3 E ∧ IsSaturated 3 E ∧ ¬ IsTight 3 E := by
  refine ⟨counterexampleEdges, ?_, forest, saturated, not_tight⟩
  decide +kernel

end OMA.CriticalForestsCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_are_critical_k_forests_tight.main) := by
  intro h
  obtain ⟨E, huniform, hforest, hsaturated, hnotTight⟩ := OMA.CriticalForestsCounterexample.counterexample
  exact hnotTight (h 6 3 E (by decide) (by decide) huniform hforest hsaturated)
