module
public import Graph189CutCore
import all Graph189CutCore

public section
namespace Graph189CutExtract
open SimpleGraph Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Passing from a component on the deletion subtype to its ambient vertex set
preserves connectedness of the induced graph. -/
theorem componentVertices_connected (c : V)
    (C : (G.induce {v | v ≠ c}).ConnectedComponent) :
    (G.induce (componentVertices c C : Set V)).Connected := by
  classical
  let φ : C.toSimpleGraph →g G.induce (componentVertices c C : Set V) :=
    { toFun := fun z => ⟨z.val.val, mem_componentVertices.mpr ⟨z.val.property,z.property⟩⟩
      map_rel' := fun h => h }
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨hn,hC⟩ := mem_componentVertices.mp z.property
    exact ⟨⟨⟨z.val,hn⟩,hC⟩, Subtype.ext rfl⟩
  exact Connected.map φ hsurj C.connected_toSimpleGraph

/-- Two components after deletion supply the two disjoint connected sides
covering every vertex except the deleted vertex. -/
theorem two_connected_sides (c : V)
    (htwo : Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2) :
    ∃ A B : Finset V, Side G c A ∧ Side G c B ∧ Disjoint A B ∧
      (∀ x, x = c ∨ x ∈ A ∨ x ∈ B) ∧
      (G.induce (A : Set V)).Connected ∧ (G.induce (B : Set V)).Connected := by
  classical
  let H := G.induce {v | v ≠ c}
  let _ := Fintype.ofFinite H.ConnectedComponent
  have hcard : Fintype.card H.ConnectedComponent = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact htwo
  let e : H.ConnectedComponent ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let C := e.symm 0
  let D := e.symm 1
  have hne : C ≠ D := fun eq => (by decide : (0 : Fin 2) ≠ 1) (e.symm.injective eq)
  refine ⟨componentVertices c C, componentVertices c D,
    componentVertices_side c C, componentVertices_side c D, componentVertices_disjoint hne,
    ?_, componentVertices_connected c C, componentVertices_connected c D⟩
  intro x
  by_cases hx : x = c
  · exact Or.inl hx
  · let t := H.connectedComponentMk ⟨x,hx⟩
    have alt : e t = 0 ∨ e t = 1 := by
      have lim := (e t).isLt
      rcases (by omega : (e t).val = 0 ∨ (e t).val = 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases alt with h | h
    · exact Or.inr (Or.inl (mem_componentVertices.mpr ⟨hx, (e.eq_symm_apply).mpr h⟩))
    · exact Or.inr (Or.inr (mem_componentVertices.mpr ⟨hx, (e.eq_symm_apply).mpr h⟩))

end Graph189CutExtract
