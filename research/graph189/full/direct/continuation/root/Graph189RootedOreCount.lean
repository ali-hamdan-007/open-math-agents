import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Graph189RootedOreCount
open SimpleGraph Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path contact and its successor violate local Ore for at least one
contact. The other hypotheses isolate the path-splicing part of the proof. -/
theorem bad_wedge_of_successors (u : V) (W : Finset V) (succ : V → V)
    (hn : W.Nonempty) (inj : Set.InjOn succ (↑W : Set V))
    (touch : ∀ w ∈ W, G.Adj u w)
    (miss : ∀ w ∈ W, succ w ≠ u ∧ ¬G.Adj u (succ w))
    (indep : ∀ a ∈ W, ∀ b ∈ W, ¬G.Adj (succ a) (succ b))
    (common : ∀ w ∈ W, ∀ v, G.Adj u v → G.Adj (succ w) v → v ∈ W) :
    ∃ w ∈ W, G.degree u + G.degree (succ w) <
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset (succ w)).card := by
  classical
  let U := W.image succ
  by_contra! hall
  have row (w : V) (hw : w ∈ W) :
      ((U.filter fun v => G.Adj w v)).card + 1 ≤ ((W.filter fun v => G.Adj v (succ w))).card := by
    let A := G.neighborFinset u
    let B := G.neighborFinset (succ w)
    let C := G.neighborFinset w
    let D := C \ (A ∪ B)
    have hu : D ∪ (A ∪ B) = (A ∪ C) ∪ B := by ext a; simp [D]; tauto
    have dis : Disjoint D (A ∪ B) := by
      rw [Finset.disjoint_left]
      exact fun _ h => (Finset.mem_sdiff.mp h).2
    have join := Finset.card_union_of_disjoint dis
    rw [hu] at join
    have oi := Finset.card_union_add_card_inter A B
    have ah : A.card = G.degree u := G.card_neighborFinset_eq_degree u
    have bh : B.card = G.degree (succ w) := G.card_neighborFinset_eq_degree _
    have localbound := hall w hw
    change ((A ∪ C) ∪ B).card ≤ G.degree u + G.degree (succ w) at localbound
    have bound : D.card ≤ (A ∩ B).card := by omega
    have hsub : insert u ((U.filter fun v => G.Adj w v)) ⊆ D := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset _ _).mpr (touch w hw).symm,?_⟩
        intro hum
        rcases Finset.mem_union.mp hum with ha | hb
        · exact ((G.mem_neighborFinset _ _).mp ha).ne rfl
        · exact (miss _ hw).2 ((G.mem_neighborFinset _ _).mp hb).symm
      · obtain ⟨hvU,hvA⟩ := Finset.mem_filter.mp hv
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hvU
        apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset _ _).mpr hvA,?_⟩
        intro h
        rcases Finset.mem_union.mp h with ha | hB
        · exact (miss _ hb).2 ((G.mem_neighborFinset _ _).mp ha)
        · exact (indep _ hw _ hb) ((G.mem_neighborFinset _ _).mp hB)
    have hout : u ∉ (U.filter fun v => G.Adj w v) := by
      intro hu
      obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
      exact (miss _ hb).1 he
    have small := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hout] at small
    have other : A ∩ B ⊆ (W.filter fun v => G.Adj v (succ w)) := by
      intro v hv
      obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp hv
      have e₁ := (G.mem_neighborFinset _ _).mp h₁
      have e₂ := (G.mem_neighborFinset _ _).mp h₂
      exact Finset.mem_filter.mpr ⟨common _ hw v e₁ e₂,e₂.symm⟩
    exact small.trans (bound.trans (Finset.card_le_card other))
  have rows := Finset.sum_le_sum row
  have dbl : (∑ w ∈ W, (U.filter fun v => G.Adj w v).card) =
      ∑ v ∈ U, (W.filter fun w => G.Adj w v).card := by
    classical
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have im : (∑ v ∈ U, ((W.filter fun w => G.Adj w v)).card) =
      ∑ w ∈ W, ((W.filter fun v => G.Adj v (succ w))).card := Finset.sum_image inj
  rw [im] at dbl
  rw [Finset.sum_add_distrib] at rows
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at rows
  have pos := hn.card_pos
  omega
#print axioms bad_wedge_of_successors
end Graph189RootedOreCount
