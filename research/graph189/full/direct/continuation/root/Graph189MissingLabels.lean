import Graph189PortLabels

open SimpleGraph Finset
namespace Graph189MissingLabels
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X S C : Finset V}

omit [DecidableRel G.Adj] in
/-- Without a full representative at least two separator labels are not
common. A single residual label would have a representative adjacent to it
and every common label. -/
theorem two_residual (xs : X.Nonempty) (each : ∀ i ∈ S, ∃ x ∈ X, G.Adj x i)
    (common : ∀ x ∈ X, ∀ i ∈ C, G.Adj x i)
    (notFull : ∀ x ∈ X, ¬∀ i ∈ S, G.Adj x i) : 2 ≤ (S \ C).card := by
  classical
  by_contra! small
  obtain ⟨x,hx⟩ := xs
  have missing := notFull x hx
  push Not at missing
  obtain ⟨i,hi,xi⟩ := missing
  have ic : i ∉ C := fun ci => xi (common x hx i ci)
  obtain ⟨y,hy,yi⟩ := each i hi
  have missing' := notFull y hy
  push Not at missing'
  obtain ⟨j,hj,yj⟩ := missing'
  have jc : j ∉ C := fun cj => yj (common y hy j cj)
  have eq : i = j := card_le_one_iff.mp (by omega : (S \ C).card ≤ 1)
    (mem_sdiff.mpr ⟨hi,ic⟩) (mem_sdiff.mpr ⟨hj,jc⟩)
  exact yj (eq ▸ yi)

/-- If only two labels are noncommon, a vertex missing any separator
label uses at most one of those two. -/
theorem at_most_one {x : V} (common : ∀ i ∈ C, G.Adj x i)
    (notFull : ¬∀ i ∈ S, G.Adj x i) (small : (S \ C).card ≤ 2) :
    (Graph189PortLabels.support G S x \ C).card ≤ 1 := by
  classical
  push Not at notFull
  obtain ⟨i,hi,miss⟩ := notFull
  have ic : i ∉ C := fun h => miss (common i h)
  have sub : Graph189PortLabels.support G S x \ C ⊆ (S \ C).erase i := by
    intro j hj
    obtain ⟨js,nc⟩ := mem_sdiff.mp hj
    obtain ⟨sj,ed⟩ := mem_filter.mp js
    exact mem_erase.mpr ⟨fun eq => miss (eq ▸ ed),mem_sdiff.mpr ⟨sj,nc⟩⟩
  have h := card_le_card sub
  rw [card_erase_of_mem (mem_sdiff.mpr ⟨hi,ic⟩)] at h
  omega

#print axioms two_residual
#print axioms at_most_one
end Graph189MissingLabels
