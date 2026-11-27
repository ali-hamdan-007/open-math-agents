import Graph199CompatibleSeparator
import Mathlib.Data.Fintype.Option

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Restoring one deleted vertex can merge only the old complementary
components it meets. The new graph has an extra component representing the
restored vertex and the components merged with it. -/
theorem restore_cut_component_bound (U : Finset V) (u : V) (hu : u ∈ U) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent + 1 ≤
    Nat.card (G.induce ((↑(U.erase u) : Set V)ᶜ)).ConnectedComponent +
      {i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent | MeetsComponent U u i}.ncard := by
  classical
  let W := ↥((U : Set V)ᶜ)
  let Z := ↥((↑(U.erase u) : Set V)ᶜ)
  let K := G.induce ((U : Set V)ᶜ)
  let H := G.induce ((↑(U.erase u) : Set V)ᶜ)
  let I := K.ConnectedComponent
  let J := H.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Finite J := Finite.of_surjective H.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  let _ : Fintype J := Fintype.ofFinite J
  let A : Set I := {i | MeetsComponent U u i}
  let _ : Fintype ↥(Aᶜ) := Fintype.ofFinite _
  have uniqueU {x : Z} (hx : x.val ∈ U) : x.val = u := by
    by_contra he
    exact x.property (mem_erase.mpr ⟨he,hx⟩)
  let label (x : Z) : Option ↥(Aᶜ) :=
    if hx : x.val ∈ U then none else
      let i := K.connectedComponentMk (⟨x.val,hx⟩ : W)
      if hi : i ∈ Aᶜ then some ⟨i,hi⟩ else none
  have hlabel (x y : Z) (hxy : H.Adj x y) : label x = label y := by
    have he : G.Adj x.val y.val := hxy
    by_cases hx : x.val ∈ U
    · by_cases hy : y.val ∈ U
      · simp [label,hx,hy]
      · have hey : G.Adj u y.val := by simpa only [uniqueU hx] using he
        have hyA : K.connectedComponentMk (⟨y.val,hy⟩ : W) ∈ A :=
          ⟨⟨y.val,hy⟩,rfl,hey⟩
        simp [label,hx,hy,Set.mem_compl_iff,hyA]
    · by_cases hy : y.val ∈ U
      · have hex : G.Adj u x.val := by simpa only [uniqueU hy] using he.symm
        have hxA : K.connectedComponentMk (⟨x.val,hx⟩ : W) ∈ A :=
          ⟨⟨x.val,hx⟩,rfl,hex⟩
        simp [label,hx,hy,Set.mem_compl_iff,hxA]
      · have hEq : K.connectedComponentMk (⟨x.val,hx⟩ : W) =
            K.connectedComponentMk (⟨y.val,hy⟩ : W) :=
          ConnectedComponent.connectedComponentMk_eq_of_adj (show K.Adj ⟨x.val,hx⟩ ⟨y.val,hy⟩ from he)
        simp only [label,dif_neg hx,dif_neg hy]
        rw [hEq]
  have hpath {x y : Z} (h : Relation.ReflTransGen H.Adj x y) : label x = label y := by
    induction h with
    | refl => rfl
    | tail _ he ih => exact ih.trans (hlabel _ _ he)
  let labels : J → Option ↥(Aᶜ) :=
    Quot.lift label (fun x y he => hpath ((H.reachable_iff_reflTransGen x y).mp he))
  have hs : Function.Surjective labels := by
    intro o
    cases o with
    | none =>
      let x : Z := ⟨u, by simp⟩
      refine ⟨H.connectedComponentMk x,?_⟩
      change label x = none
      simp [label,x,hu]
    | some i =>
      let x : W := i.val.out
      let y : Z := ⟨x.val,fun he => x.property (mem_of_mem_erase he)⟩
      refine ⟨H.connectedComponentMk y,?_⟩
      change label y = some i
      have hxU : x.val ∉ U := x.property
      have hI : K.connectedComponentMk x = i.val := i.val.out_eq
      simp only [label,y,dif_neg hxU]
      change (if h : K.connectedComponentMk x ∈ Aᶜ then
        some ⟨K.connectedComponentMk x,h⟩ else none) = some i
      rw [hI]
      exact dif_pos i.property
  have hcard := Fintype.card_le_of_surjective labels hs
  rw [Fintype.card_option, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hcard
  change (Aᶜ).ncard + 1 ≤ Nat.card J at hcard
  have hsplit := Set.ncard_add_ncard_compl A
  change Nat.card I + 1 ≤ Nat.card J + A.ncard
  omega

#print axioms restore_cut_component_bound
end Graph199
