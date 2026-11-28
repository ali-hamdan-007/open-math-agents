import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic

namespace Graph189ExteriorContacts

open Finset

/-- For adjacent vertices outside a longest path, contacts of distinct
vertices cannot be one or two positions apart. The three sets below are
path positions at distance two from the first exterior vertex. -/
theorem cross_contact_count (A B : Finset ℤ)
    (gapOne : ∀ a ∈ A, ∀ b ∈ B, a ≠ b + 1 ∧ a + 1 ≠ b)
    (gapTwo : ∀ a ∈ A, ∀ b ∈ B, a ≠ b + 2) :
    A.card + B.card =
      ((A.image (fun i => i - 1) ∪ (A ∩ B).image (fun i => i + 1)) ∪ (B \ A)).card := by
  have hd : Disjoint (A.image (fun i => i - 1)) ((A ∩ B).image (fun i => i + 1)) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hw
    exact (gapTwo a ha b (Finset.mem_inter.mp hb).2) (by omega)
  have he : Disjoint (A.image (fun i => i - 1) ∪ (A ∩ B).image (fun i => i + 1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (gapOne a ha _ hb).1 (by omega)
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (gapOne a (Finset.mem_inter.mp ha).1 _ hb).2 rfl
  rw [Finset.card_union_of_disjoint he, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (show Function.Injective (fun i : ℤ => i - 1) by
      intro x y h; change x - 1 = y - 1 at h; omega),
    Finset.card_image_of_injective _ (show Function.Injective (fun i : ℤ => i + 1) by
      intro x y h; change x + 1 = y + 1 at h; omega)]
  have cover : (B \ A) ∪ (A ∩ B) = B := by ext i; simp; tauto
  have disj : Disjoint (B \ A) (A ∩ B) := by
    rw [Finset.disjoint_left]
    exact fun _ h h' => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp h').1
  have hc := Finset.card_union_of_disjoint disj
  rw [cover] at hc
  omega

#print axioms cross_contact_count

end Graph189ExteriorContacts
