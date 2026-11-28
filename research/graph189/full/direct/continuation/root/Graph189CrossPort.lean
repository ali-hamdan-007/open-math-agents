import Graph189SeparatorCover
import Mathlib.Data.Finset.Prod

open SimpleGraph Finset
namespace Graph189CrossPort
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- An odd high-to-high route across a separator must use a one-step and a
two-step anchor incidence. The other pairs use a source's even-distance budget. -/
theorem pair_bound (hc : G.Connected) (A B S : Finset V)
    (separate : Disjoint A B) (source : Disjoint A S) (target : Disjoint B S)
    (diam : ∀ x ∈ A, ∀ y ∈ B, G.dist x y ≤ 4)
    (through : ∀ x ∈ A, ∀ y ∈ B, ∃ i ∈ S, G.dist x y = G.dist x i + G.dist i y)
    (k : ℕ) (cap : ∀ u, G.distEven u ≤ k+1) :
    A.card * B.card ≤ A.card * k + ∑ i ∈ S,
      ((A.filter (fun x => G.dist x i = 1)).card * (B.filter (fun y => G.dist i y = 2)).card +
       (A.filter (fun x => G.dist x i = 2)).card * (B.filter (fun y => G.dist i y = 1)).card) := by
  classical
  let EvenRow (x : V) := B.filter (fun y => Even (G.dist x y))
  let Cross (i : V) :=
    (A.filter (fun x => G.dist x i = 1) ×ˢ B.filter (fun y => G.dist i y = 2)) ∪
    (A.filter (fun x => G.dist x i = 2) ×ˢ B.filter (fun y => G.dist i y = 1))
  have even_count (x : V) (hx : x ∈ A) : (EvenRow x).card ≤ k := by
    let E := Finset.univ.filter (fun y => Even (G.dist x y))
    have inE : x ∈ E := by simp [E]
    have hcap := cap x
    change E.card ≤ k+1 at hcap
    have sub : EvenRow x ⊆ E.erase x := by
      intro y hy
      obtain ⟨hyB, h⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_erase.mpr ⟨?_, mem_filter.mpr ⟨mem_univ _, h⟩⟩
      rintro rfl
      exact Finset.disjoint_left.mp separate hx hyB
    have hle := card_le_card sub
    rw [card_erase_of_mem inE] at hle
    omega
  have covered : A ×ˢ B ⊆ (A.biUnion (fun x => {x} ×ˢ EvenRow x)) ∪ S.biUnion Cross := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    by_cases parity : Even (G.dist x y)
    · apply mem_union_left
      exact mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_singleton_self _,mem_filter.mpr ⟨hy,parity⟩⟩⟩
    · obtain ⟨i,hi,route⟩ := through x hx y hy
      have left : G.dist x i ≠ 0 := fun eq => Finset.disjoint_left.mp source hx ((hc.dist_eq_zero_iff.mp eq).symm ▸ hi)
      have right : G.dist i y ≠ 0 := fun eq => Finset.disjoint_left.mp target hy ((hc.dist_eq_zero_iff.mp eq) ▸ hi)
      have hd := diam x hx y hy
      rw [Nat.even_iff] at parity
      have alternatives : (G.dist x i = 1 ∧ G.dist i y = 2) ∨
          (G.dist x i = 2 ∧ G.dist i y = 1) := by omega
      apply mem_union_right
      refine mem_biUnion.mpr ⟨i,hi,?_⟩
      rcases alternatives with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨hx,h₁⟩, mem_filter.mpr ⟨hy,h₂⟩⟩)
      · exact mem_union_right _ (mem_product.mpr ⟨mem_filter.mpr ⟨hx,h₁⟩, mem_filter.mpr ⟨hy,h₂⟩⟩)
  rw [← card_product]
  apply le_trans (card_le_card covered)
  apply le_trans (card_union_le _ _)
  apply Nat.add_le_add
  · apply le_trans card_biUnion_le
    calc (∑ x ∈ A, (({x} : Finset V) ×ˢ EvenRow x).card)
        ≤ ∑ _ ∈ A, k := by
          apply Finset.sum_le_sum
          intro x hx
          simpa using even_count x hx
      _ = A.card * k := by simp
  · apply le_trans card_biUnion_le
    apply Finset.sum_le_sum
    intro i hi
    simpa only [Cross, card_product] using
      (card_union_le
        (A.filter (fun x => G.dist x i = 1) ×ˢ B.filter (fun y => G.dist i y = 2))
        (A.filter (fun x => G.dist x i = 2) ×ˢ B.filter (fun y => G.dist i y = 1)))
#print axioms pair_bound
end Graph189CrossPort
