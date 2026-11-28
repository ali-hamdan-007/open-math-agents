import Graph189MatchingGroups
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open scoped BigOperators

namespace Graph189MatchedCharging

/-- Per-row reserve counting with one distinct witness for each other matching row. -/
theorem card_targets_le {I V : Type*} [DecidableEq I] [DecidableEq V]
    (M : Finset I) (targets : Finset V) (group : V → I)
    (quota fixed : I → Finset V) (witness : I → I → V) (credit : I → ℕ) {k : ℕ}
    (cover : ∀ x ∈ targets, group x ∈ M)
    (cap : ∀ p ∈ M, (quota p).card ≤ k + 1)
    (fixed_card : ∀ p ∈ M, (fixed p).card + credit p = 3)
    (hfixed : ∀ p ∈ M, fixed p ⊆ quota p)
    (hrow : ∀ p ∈ M, ∀ x ∈ targets, group x = p → x ∈ quota p ∧ x ∉ fixed p)
    (hwit : ∀ p ∈ M, ∀ q ∈ M, q ≠ p →
      witness p q ∈ quota p ∧ witness p q ∉ fixed p ∧
      (witness p q ∈ targets → group (witness p q) ≠ p))
    (hinj : ∀ p ∈ M, Set.InjOn (witness p) (↑(M.erase p) : Set I)) :
    targets.card + M.card * (M.card + 1) ≤ M.card * k + ∑ p ∈ M, credit p := by
  classical
  let row := fun p => targets.filter (fun x => group x = p)
  let extras := fun p => (M.erase p).image (witness p)
  have row_bound (p : I) (hp : p ∈ M) : (row p).card + (M.card+1) ≤ k + credit p := by
    have d0 : Disjoint (row p) (fixed p) := by
      rw [Finset.disjoint_left]
      intro x hx hf
      obtain ⟨ht,hg⟩ := mem_filter.mp hx
      exact (hrow p hp x ht hg).2 hf
    have d1 : Disjoint (row p ∪ fixed p) (extras p) := by
      rw [Finset.disjoint_left]
      intro x hx he
      obtain ⟨q,hq,rfl⟩ := mem_image.mp he
      obtain ⟨hne,hqm⟩ := mem_erase.mp hq
      have hqval := hwit p hp q hqm hne
      rcases mem_union.mp hx with hr | hf
      · obtain ⟨ht,hg⟩ := mem_filter.mp hr
        exact hqval.2.2 ht hg
      · exact hqval.2.1 hf
    have sub : (row p ∪ fixed p) ∪ extras p ⊆ quota p := by
      intro x hx
      rcases mem_union.mp hx with hf | he
      · rcases mem_union.mp hf with hr | hf
        · obtain ⟨ht,hg⟩ := mem_filter.mp hr
          exact (hrow p hp x ht hg).1
        · exact hfixed p hp hf
      · obtain ⟨q,hq,rfl⟩ := mem_image.mp he
        obtain ⟨hne,hqm⟩ := mem_erase.mp hq
        exact (hwit p hp q hqm hne).1
    have h := (card_le_card sub).trans (cap p hp)
    rw [card_union_of_disjoint d1,card_union_of_disjoint d0] at h
    have he : (extras p).card + 1 = M.card := by
      change ((M.erase p).image (witness p)).card + 1 = M.card
      rw [card_image_of_injOn (hinj p hp),card_erase_add_one hp]
    have hf := fixed_card p hp
    omega
  have hsum := Finset.sum_le_sum (s:=M) fun p hp => row_bound p hp
  have hfib : ∑ p ∈ M, (row p).card = targets.card := by
    have hf := Finset.sum_card_fiberwise_eq_card_filter targets M group
    have hfilter : targets.filter (fun x => group x ∈ M) = targets := filter_eq_self.mpr cover
    simpa only [hfilter] using hf
  calc
    targets.card + M.card * (M.card + 1) = ∑ p ∈ M, ((row p).card + (M.card + 1)) := by
      rw [Finset.sum_add_distrib,hfib,Finset.sum_const,Nat.nsmul_eq_mul]
    _ ≤ ∑ p ∈ M, (k + credit p) := hsum
    _ = M.card * k + ∑ p ∈ M, credit p := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul]

/-- Duplicate credits in a three-set cover. A further set already shared by the
second and third sets can be charged separately from the two reserved subsets. -/
theorem union_add_credits_le {V : Type*} [DecidableEq V]
    (E0 E1 E2 Q D1 D2 : Finset V)
    (hq : Q ⊆ E1 ∩ E2) (h1 : D1 ⊆ E0 ∩ E1) (h2 : D2 ⊆ E0 ∩ E2)
    (hd : Disjoint Q (D1 ∩ D2)) :
    ((E1 ∪ E2) ∪ E0).card + Q.card + D1.card + D2.card ≤ E0.card + E1.card + E2.card := by
  classical
  have hBoth : Q ∪ (D1 ∩ D2) ⊆ E1 ∩ E2 := by
    intro v hv
    rcases mem_union.mp hv with hqv | hDv
    · exact hq hqv
    · obtain ⟨hDv1,hDv2⟩ := mem_inter.mp hDv
      exact mem_inter.mpr ⟨(mem_inter.mp (h1 hDv1)).2,(mem_inter.mp (h2 hDv2)).2⟩
  have hEither : D1 ∪ D2 ⊆ (E1 ∪ E2) ∩ E0 := by
    intro v hv
    rcases mem_union.mp hv with hd1 | hd2
    · obtain ⟨hh0,hh1⟩ := mem_inter.mp (h1 hd1)
      exact mem_inter.mpr ⟨mem_union_left _ hh1,hh0⟩
    · obtain ⟨hh0,hh2⟩ := mem_inter.mp (h2 hd2)
      exact mem_inter.mpr ⟨mem_union_right _ hh2,hh0⟩
  have hB := Finset.card_le_card hBoth
  rw [card_union_of_disjoint hd] at hB
  have hE := Finset.card_le_card hEither
  have h01 := card_union_add_card_inter E1 E2
  have h02 := card_union_add_card_inter (E1 ∪ E2) E0
  have hD := card_union_add_card_inter D1 D2
  omega

end Graph189MatchedCharging
