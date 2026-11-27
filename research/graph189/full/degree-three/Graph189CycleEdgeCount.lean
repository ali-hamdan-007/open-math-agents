import Mathlib.Data.Finset.Card

namespace Graph189CycleEdgeCount

open Finset

/-- An injective successor map can leave X at most once per boundary vertex. -/
theorem internal_successors_card [DecidableEq V] (succ : V → V)
    (hinj : Function.Injective succ) (X boundary : Finset V)
    (hboundary : ∀ x ∈ X, succ x ∉ X → succ x ∈ boundary) :
    X.card - boundary.card ≤ (X.filter fun x => succ x ∈ X).card := by
  let outside := X.filter fun x => succ x ∉ X
  let inside := X.filter fun x => succ x ∈ X
  have houtside : outside.image succ ⊆ boundary := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact hboundary x (mem_filter.mp hx).1 (mem_filter.mp hx).2
  have hcard := card_le_card houtside
  rw [card_image_of_injective outside hinj] at hcard
  have hdisj : Disjoint inside outside := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxo
    exact (mem_filter.mp hxo).2 (mem_filter.mp hxi).2
  have hUnion : inside ∪ outside = X := by
    ext x
    by_cases hx : succ x ∈ X <;> simp [inside, outside, hx]
  have hsplit : inside.card + outside.card = X.card := by
    rw [← card_union_of_disjoint hdisj, hUnion]
  change X.card - boundary.card ≤ inside.card
  omega

/-- The cycle version uses the permutation taking each vertex to its
oriented successor. -/
theorem internal_cycle_edges_card [DecidableEq V] (succ : Equiv.Perm V)
    (X boundary : Finset V) {b : ℕ} (hsize : boundary.card ≤ b)
    (hboundary : ∀ x ∈ X, succ x ∉ X → succ x ∈ boundary) :
    X.card - b ≤ (X.filter fun x => succ x ∈ X).card := by
  have := internal_successors_card succ succ.injective X boundary hboundary
  omega

#print axioms internal_cycle_edges_card

end Graph189CycleEdgeCount
