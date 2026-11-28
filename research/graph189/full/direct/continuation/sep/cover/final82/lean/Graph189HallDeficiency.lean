import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum

open Finset
namespace Graph189ExteriorGap
variable {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]

/-- The deficiency form of finite Hall. At most |L|−s dummy assignments suffice
to turn a full system of representatives into at least s distinct genuine edges. -/
theorem hall_at_least (neighbors : L → Finset R) (s : ℕ) (small : s ≤ Fintype.card L)
    (hall : ∀ T : Finset L, T.card ≤ (T.biUnion neighbors).card + (Fintype.card L-s)) :
    ∃ U : Finset L, s ≤ U.card ∧ ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let d := Fintype.card L-s
  let choices := fun u : L => (neighbors u).disjSum (Finset.univ : Finset (Fin d))
  have full (T : Finset L) : T.card ≤ (T.biUnion choices).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have eq : T.biUnion choices = (T.biUnion neighbors).disjSum (Finset.univ : Finset (Fin d)) := by
      ext k
      cases k with
      | inl x => simp [choices]
      | inr y =>
        simp [choices]
        exact ⟨u,hu⟩
    rw [eq,Finset.card_disjSum,Finset.card_univ,Fintype.card_fin]
    exact hall T
  obtain ⟨f,hf,acceptable⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp full
  let U := (Finset.univ : Finset L).filter (fun u => ∃ r : R, f u = Sum.inl r)
  have real (u : U) : ∃ r : R, f u.val = Sum.inl r := (Finset.mem_filter.mp u.property).2
  let g := fun u : U => (real u).choose
  have hg (u : U) : f u.val = Sum.inl (g u) := (real u).choose_spec
  have gi : Function.Injective g := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (hg u).trans ((congrArg Sum.inl eq).trans (hg v).symm)
  let D := (Finset.univ : Finset L) \ U
  have dummy (u : D) : ∃ i : Fin d, f u.val = Sum.inr i := by
    cases eq : f u.val with
    | inr j => exact ⟨j,rfl⟩
    | inl r => exact ((Finset.mem_sdiff.mp u.property).2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,r,eq⟩)).elim
  let index := fun u : D => (dummy u).choose
  have di : Function.Injective index := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (dummy u).choose_spec.trans ((congrArg Sum.inr eq).trans (dummy v).choose_spec.symm)
  have cap := Fintype.card_le_of_injective index di
  change Fintype.card D ≤ Fintype.card (Fin d) at cap
  simp only [Fintype.card_coe,Fintype.card_fin] at cap
  have part := Finset.card_sdiff_add_card_inter (Finset.univ : Finset L) U
  simp only [Finset.univ_inter,Finset.card_univ] at part
  change D.card+U.card=Fintype.card L at part
  refine ⟨U,by dsimp [d] at cap; omega,⟨g,gi⟩,?_⟩
  intro u
  have spec := acceptable u.val
  rw [hg] at spec
  simpa [choices] using spec

/-- A degree lower bound t on one shore guarantees any t vertices of that
shore have pairwise distinct representatives. -/
theorem hall_on_dense_vertices (neighbors : L → Finset R) (s : ℕ)
    (U : Finset L) (size : U.card=s) (degree : ∀ u∈U, s ≤ (neighbors u).card) :
    ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let links := fun u : U => neighbors u.val
  have h (T : Finset U) : T.card ≤ (T.biUnion links).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have subset : links u ⊆ T.biUnion links := by
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨u,hu,hz⟩
    have small : T.card ≤ U.card := by simpa using T.card_le_univ
    exact (small.trans (size.le.trans (degree u.val u.property))).trans (Finset.card_le_card subset)
  obtain ⟨f,hi,good⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' links).mp h
  exact ⟨⟨f,hi⟩,good⟩

#print axioms hall_at_least
#print axioms hall_on_dense_vertices
end Graph189ExteriorGap
