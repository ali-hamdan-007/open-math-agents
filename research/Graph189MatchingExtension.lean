import Graph189BipartiteStructure

namespace Graph189Bipartite
variable {V : Type*} [DecidableEq V]

/-- Extend a partial injection of two finite parts to an injection on the entire first part. -/
theorem extend_partial_matching (left right domain : Finset V) (hdom : domain ⊆ left)
    (hcard : left.card ≤ right.card) [Nonempty V]
    (f : V → V) (hf : Set.InjOn f domain) (hfr : Set.MapsTo f domain right) :
    ∃ e : V → V, Set.InjOn e left ∧ Set.MapsTo e left right ∧
      ∀ x ∈ domain, e x = f x := by
  classical
  have himage : domain.image f ⊆ right := hfr.finsetImage_subset
  have hcard' : (left \ domain).card ≤ (right \ domain.image f).card := by
    rw [Finset.card_sdiff_of_subset hdom, Finset.card_sdiff_of_subset himage,
      Finset.card_image_of_injOn hf]
    omega
  have hencard :
      ((left \ domain : Finset V) : Set V).encard ≤
        ((right \ domain.image f : Finset V) : Set V).encard := by
    rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hcard'
  obtain ⟨g,hgr,hg⟩ := (left \ domain).finite_toSet.exists_injOn_of_encard_le hencard
  let e (x : V) := if x ∈ domain then f x else g x
  have hg' {x} (hx : x ∈ left) (hn : x ∉ domain) : g x ∈ right \ domain.image f :=
    hgr (Finset.mem_sdiff.mpr ⟨hx,hn⟩)
  have hsep {x y} (hx : x ∈ domain) (hy : y ∈ left) (hyn : y ∉ domain) :
      f x ≠ g y := fun he =>
    (Finset.mem_sdiff.mp (hg' hy hyn)).2 (he ▸ Finset.mem_image_of_mem f hx)
  refine ⟨e, ?_, ?_, fun x hx => if_pos hx⟩
  · intro x hx y hy he
    change x ∈ left at hx
    change y ∈ left at hy
    by_cases hxd : x ∈ domain <;> by_cases hyd : y ∈ domain
    · exact hf hxd hyd (by simpa [e,hxd,hyd] using he)
    · exact (hsep hxd hy hyd (by simpa [e,hxd,hyd] using he)).elim
    · exact (hsep hyd hx hxd (by simpa [e,hxd,hyd] using he.symm)).elim
    · exact hg (Finset.mem_sdiff.mpr ⟨hx,hxd⟩) (Finset.mem_sdiff.mpr ⟨hy,hyd⟩)
        (by simpa [e,hxd,hyd] using he)
  · intro x hx
    change x ∈ left at hx
    change e x ∈ right
    by_cases hxd : x ∈ domain
    · simpa [e,hxd] using hfr hxd
    · simpa [e,hxd] using (Finset.mem_sdiff.mp (hg' hx hxd)).1

#print axioms extend_partial_matching
end Graph189Bipartite
