import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Topology.EMetricSpace.Diam

/-!
# Adding points at diameter distance

This proves the diameter-graph step of the extension from the nine-dimensional Borsuk
counterexample to higher dimensions. Any cover of the extended set must spend a distinct
cover set on each added point. Those cover sets contain none of the original points.
-/

namespace BorsukApex

open Metric

/-- The set has a cover by `k` sets each of strictly smaller extended diameter. -/
def Cover {E : Type*} [PseudoEMetricSpace E] (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

theorem ediam_insert_of_cross {E : Type*} [PseudoEMetricSpace E] {s : Set E} {a : E}
    (hcross : ∀ x ∈ s, edist a x = ediam s) :
    ediam (insert a s) = ediam s := by
  refine le_antisymm (ediam_le_iff.mpr ?_) (ediam_mono (Set.subset_insert a s))
  intro x hx y hy
  rcases Set.mem_insert_iff.mp hx with hxa | hxs
  · subst x
    rcases Set.mem_insert_iff.mp hy with hya | hys
    · subst y
      simp
    · exact (hcross y hys).le
  · rcases Set.mem_insert_iff.mp hy with hya | hys
    · subst y
      rw [edist_comm]
      exact (hcross x hxs).le
    · exact edist_le_ediam_of_mem hxs hys

theorem cover_of_insert {E : Type*} [PseudoEMetricSpace E] {s : Set E} {a : E}
    {k : ℕ} (hcross : ∀ x ∈ s, edist a x = ediam s)
    (h : Cover (k + 1) (insert a s)) : Cover k s := by
  obtain ⟨c, hcover, hsmall⟩ := h
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_insert a s))
  refine ⟨fun j => c (i.succAbove j), ?_, fun j => ?_⟩
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover (Set.mem_insert_of_mem a hx))
    have hne : j ≠ i := by
      rintro rfl
      have hle := edist_le_ediam_of_mem hi hj
      rw [hcross x hx] at hle
      exact (not_lt_of_ge hle) ((ediam_insert_of_cross hcross) ▸ hsmall j)
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hne
    exact Set.mem_iUnion.mpr ⟨j', hj⟩
  · simpa [ediam_insert_of_cross hcross] using hsmall (i.succAbove j)

/-- Adjoining any family of points at diameter distance from the original set and from each
other preserves the diameter and increases the lower bound on the cover size by the number
of added points. -/
theorem no_cover_union {E : Type*} [PseudoEMetricSpace E] {s : Set E} {k : ℕ}
    (hs : ¬ Cover k s) (t : Finset E)
    (hcross : ∀ a ∈ t, ∀ x ∈ s, edist a x = ediam s)
    (hpair : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → edist a b = ediam s) :
    ediam (s ∪ (t : Set E)) = ediam s ∧ ¬ Cover (k + t.card) (s ∪ (t : Set E)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa
  | @insert a t ha ih =>
    have ht : ∀ b ∈ t, b ∈ insert a t := fun b hb => Finset.mem_insert_of_mem hb
    obtain ⟨hd, hn⟩ := ih (fun b hb => hcross b (ht b hb))
      (fun b hb c hc => hpair b (ht b hb) c (ht c hc))
    have hnew : ∀ x ∈ s ∪ (t : Set E), edist a x = ediam (s ∪ (t : Set E)) := by
      intro x hx
      rw [hd]
      rcases hx with hx | hx
      · exact hcross a (Finset.mem_insert_self a t) x hx
      · exact hpair a (Finset.mem_insert_self a t) x (ht x hx) (by
          rintro rfl
          exact ha hx)
    have hset : s ∪ ((insert a t : Finset E) : Set E) = insert a (s ∪ (t : Set E)) := by
      ext x
      simp
    rw [hset, Finset.card_insert_of_notMem ha, ← Nat.add_assoc]
    exact ⟨(ediam_insert_of_cross hnew).trans hd, fun h => hn (cover_of_insert hnew h)⟩

end BorsukApex

#print axioms BorsukApex.no_cover_union
