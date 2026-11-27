import Graph199H1Data
import Graph199Reduction

namespace Graph199
open SimpleGraph

universe u

/-- Neighbor subgroups in a rooted H1 decomposition have independence number
at most two, including each attachment class and the spare subgroup. -/
theorem H1FarData.indepNum_le_two {V : Type u} [Fintype V] {G : SimpleGraph V}
    {v w : V} {A : Set V} (D : H1FarData G v w A) (S : Set V)
    (hS : ∀ x ∈ S, x ∈ A ∧ G.Adj v x) : (G.induce S).indepNum ≤ 2 := by
  classical
  by_contra! hn
  obtain ⟨t,ht⟩ := (G.induce S).exists_isNIndepSet_indepNum
  have hc : 2 < t.card := by rwa [ht.card_eq]
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hc
  have ha' := hS a.val a.property
  have hb' := hS b.val b.property
  have hc' := hS c.val c.property
  exact D.near_no_independent_triple _ _ _ ha'.1 hb'.1 hc'.1 ha'.2 hb'.2 hc'.2
    (fun e => hab (Subtype.ext e)) (fun e => hac (Subtype.ext e)) (fun e => hbc (Subtype.ext e))
    (ht.isIndepSet ha hb hab) (ht.isIndepSet ha hc hac) (ht.isIndepSet hb hc hbc)

/-- The full H1 graph problem follows from the corresponding block-ordering
problem. The only residual graphs have a clique side and rooted far blocks
on the other side. -/
theorem two_component_step_of_far_data
    (solve :
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (v w : V) (A B : Set V), v ≠ w →
        (v ∉ A ∧ w ∉ A) → (v ∉ B ∧ w ∉ B) →
        (∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B) →
        (∀ x ∈ A, ∀ y ∈ B, x ≠ y) →
        B.Nonempty → G.IsClique B → (∀ x ∈ B, G.Adj v x ∧ G.Adj w x) →
        H1FarData G v w A →
        ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian) :
    TwoComponentStep.{u} := by
  intro V _ _ G hκ ht v w A B hvw hnA hnB hvA hwA hvB hwB hA hB hcover hsep hnc
  by_contra hno
  have hshape := frontier_of_two_component_case v w hvw A B ⟨hvA,hwA⟩ ⟨hvB,hwB⟩
    hcover hA hB hsep hnc hκ ht hno
  have hs (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ A) : x ≠ y ∧ ¬ G.Adj x y :=
    ⟨(hsep y hy x hx).1.symm, fun h => (hsep y hy x hx).2 h.symm⟩
  obtain ⟨hmA,hmB,_,_⟩ := minimum_two_cut_attachments v w hvw A B ⟨hvA,hwA⟩ ⟨hvB,hwB⟩
    hcover hA hB hsep hκ
  rcases hshape with ⟨hcl,_,hfull,hmiss,_⟩ | ⟨hcl,_,hfull,hmiss,_⟩
  · have hcov (x : V) (hx : x ≠ v) (hy : x ≠ w) : x ∈ B ∨ x ∈ A :=
      (hcover x hx hy).symm
    let D := h1FarData v w B A ⟨hvB,hwB⟩ hcov hB hnA hs
      (fun x hx => (hfull x hx).1) (fun x hx => (hfull x hx).2)
      hmB hmiss hκ.ge ht
    exact hno (solve G v w B A hvw ⟨hvB,hwB⟩ ⟨hvA,hwA⟩ hcov
      (fun x hx y hy => (hs x hx y hy).1) hnA hcl hfull D)
  · let D := h1FarData v w A B ⟨hvA,hwA⟩ hcover hA hnB hsep
      (fun x hx => (hfull x hx).1) (fun x hx => (hfull x hx).2)
      hmA hmiss hκ.ge ht
    exact hno (solve G v w A B hvw ⟨hvA,hwA⟩ ⟨hvB,hwB⟩ hcover
      (fun x hx y hy => (hsep x hx y hy).1) hnB hcl hfull D)

#print axioms H1FarData.indepNum_le_two
#print axioms two_component_step_of_far_data
end Graph199
