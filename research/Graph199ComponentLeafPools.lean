import Graph199CliqueSeparator

namespace Graph199

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {ι : Type*} [DecidableEq ι]

omit [Fintype V] [DecidableEq ι] in
private theorem choose_component_leaves (C : ι → Set V) (J : Finset ι) (u : V)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (hJ : ∀ i ∈ J, ∃ x ∈ C i, G.Adj x u) :
    ∃ S : Finset V, S.card = J.card ∧ G.IsIndepSet (S : Set V) ∧
      ∀ x ∈ S, G.Adj x u ∧ ∃ i ∈ J, x ∈ C i := by
  classical
  let pick (i : J) : V := Classical.choose (hJ i i.property)
  have hmem (i : J) : pick i ∈ C i := (Classical.choose_spec (hJ i i.property)).1
  have hadj (i : J) : G.Adj (pick i) u := (Classical.choose_spec (hJ i i.property)).2
  have hinj : Function.Injective pick := by
    intro i j h
    apply Subtype.ext
    by_contra hne
    exact (hsep i j hne (pick i) (hmem i) (pick j) (hmem j)).1 h
  let S := J.attach.image pick
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_attach]
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    have hij : (i : ι) ≠ j := fun h => hxy (congrArg pick (Subtype.ext h))
    exact (hsep i j hij _ (hmem i) _ (hmem j)).2
  · intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact ⟨hadj i, i, i.property, hmem i⟩

/-- Attach one leaf from each of two disjoint pools of components to the designated
vertices of a core induced tree. The two designated vertices may coincide. -/
theorem component_leaf_pools_bound (B : Finset V) (C : ι → Set V) (J₁ J₂ : Finset ι)
    (u v : V) (hB : (G.induce (B : Set V)).IsTree) (hu : u ∈ B) (hv : v ∈ B)
    (hJ : Disjoint J₁ J₂)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (hdis : ∀ i ∈ J₁ ∪ J₂, Disjoint (C i) (B : Set V))
    (h₁ : ∀ i ∈ J₁, ∃ x ∈ C i, G.Adj x u)
    (h₂ : ∀ i ∈ J₂, ∃ x ∈ C i, G.Adj x v)
    (honly₁ : ∀ i ∈ J₁, ∀ x ∈ C i, ∀ y ∈ B, G.Adj x y → y = u)
    (honly₂ : ∀ i ∈ J₂, ∀ x ∈ C i, ∀ y ∈ B, G.Adj x y → y = v) :
    B.card + J₁.card + J₂.card ≤ largestInducedTreeSize G := by
  obtain ⟨S, hSc, hSind, hSmem⟩ := choose_component_leaves C J₁ u hsep h₁
  obtain ⟨T, hTc, hTind, hTmem⟩ := choose_component_leaves C J₂ v hsep h₂
  have hSB : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨i, hi, hxi⟩ := (hSmem x hx).2
    exact Set.disjoint_left.mp (hdis i (mem_union.mpr (Or.inl hi))) hxi hb
  have hTB : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨i, hi, hxi⟩ := (hTmem x hx).2
    exact Set.disjoint_left.mp (hdis i (mem_union.mpr (Or.inr hi))) hxi hb
  have hST (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨i, hi, hxi⟩ := (hSmem x hx).2
    obtain ⟨j, hj, hyj⟩ := (hTmem y hy).2
    have hij : i ≠ j := by
      rintro rfl
      exact Finset.disjoint_left.mp hJ hi hj
    exact hsep i j hij x hxi y hyj
  rw [← hSc, ← hTc]
  apply leaf_sets_on_induced_tree B S T u v hB hu hv hSB hTB hSind hTind hST
    (fun x hx => (hSmem x hx).1) (fun y hy => (hTmem y hy).1)
  · intro x hx y hy hxy
    obtain ⟨i, hi, hxi⟩ := (hSmem x hx).2
    exact honly₁ i hi x hxi y hy hxy
  · intro x hx y hy hxy
    obtain ⟨i, hi, hxi⟩ := (hTmem x hx).2
    exact honly₂ i hi x hxi y hy hxy

end Graph199
