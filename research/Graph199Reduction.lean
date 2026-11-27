import Graph199CutBranches
import Graph199Independent
import Graph199TwoCliques

namespace Graph199
open SimpleGraph Finset

universe u

/-- The two-component case with a nonclique side at connectivity two. -/
def TwoComponentStep : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    vertexConnectivity G = 2 → largestInducedTreeSize G ≤ 4 →
    ∀ (v w : V) (A B : Set V), v ≠ w →
    A.Nonempty → B.Nonempty → v ∉ A → w ∉ A → v ∉ B → w ∉ B →
    (G.induce A).Connected → (G.induce B).Connected →
    (∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B) →
    (∀ x ∈ A, ∀ y ∈ B, x ≠ y ∧ ¬ G.Adj x y) →
    (¬ G.IsClique A ∨ ¬ G.IsClique B) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Connectivity at least three, with an independent triple. -/
def HighConnectivityStep : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → 3 ≤ vertexConnectivity G → 3 ≤ G.indepNum →
    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

variable {V : Type u} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}

private theorem exists_minimum_two_cut (hk : vertexConnectivity G = 2)
    (hn : 3 < Fintype.card V) :
    ∃ S : Finset V, S.card = 2 ∧ ¬ (G.induce ((S : Set V)ᶜ)).Connected := by
  classical
  let A : Set ℕ := {k | ∃ S : Finset V, S.card = k ∧
    (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1)}
  have hkn : vertexConnectivity G = sInf A := by
    unfold vertexConnectivity
    rw [if_neg (by omega)]
  have hA : A.Nonempty := by
    let v : V := Classical.choice (inferInstance : Nonempty V)
    exact ⟨Fintype.card V - 1, univ.erase v, by simp, Or.inr (by simp)⟩
  obtain ⟨S, hS, hcut | hcard⟩ := Nat.sInf_mem hA
  · exact ⟨S, by rwa [← hkn, hk] at hS, hcut⟩
  · rw [← hkn, hk] at hS
    omega

omit [DecidableEq V] in
private theorem card_ge_four_of_indepNum (hc : G.Connected) (hi : 3 ≤ G.indepNum) :
    3 < Fintype.card V := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  by_contra! hn
  have hsu : s = univ := by
    refine eq_of_subset_of_card_le (subset_univ _) ?_
    rw [card_univ, hs.card_eq]
    exact hn.trans hi
  obtain ⟨a,b,hab⟩ := exists_pair_ne V
  obtain ⟨p⟩ := hc a b
  cases p with
  | nil => exact hab rfl
  | @cons _ c _ h _ =>
    exact (hs.isIndepSet (by simp [hsu]) (by simp [hsu]) h.ne) h

theorem connectivity_two_reduction (step : TwoComponentStep.{u})
    (hg : G.Connected) (hk : vertexConnectivity G = 2)
    (hi : 3 ≤ G.indepNum) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨S, hS, hs⟩ := exists_minimum_two_cut hk (card_ge_four_of_indepNum hg hi)
  obtain ⟨v,w,hvw,rfl⟩ := card_eq_two.mp hS
  let W := ↥((↑({v,w} : Finset V) : Set V)ᶜ)
  let K : SimpleGraph W := G.induce ((↑({v,w} : Finset V) : Set V)ᶜ)
  let I := K.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  let C (i : I) : Set V := Subtype.val '' i.supp
  have hn (i : I) : (C i).Nonempty := ⟨i.out.val, i.out, i.out_eq, rfl⟩
  have hout (i : I) (x : V) (hx : x ∈ C i) : x ∉ ({v,w} : Finset V) := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  have hcover (x : V) (hx : x ∉ ({v,w} : Finset V)) : ∃ i, x ∈ C i := by
    let y : W := ⟨x, hx⟩
    exact ⟨K.connectedComponentMk y, y, rfl, rfl⟩
  have hsep {i j : I} {x y : V} (hij : i ≠ j)
      (hx : x ∈ C i) (hy : y ∈ C j) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    change K.connectedComponentMk a = i at ha
    change K.connectedComponentMk b = j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by rwa [ha,hb]
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj
        (show K.Adj a b from he))⟩
  have hconn (i : I) : (G.induce (C i)).Connected := by
    let e : i.supp → C i := fun x => ⟨x.val.val, x.val, x.property, rfl⟩
    have hinj : Function.Injective e := by
      intro a b h
      have hv : a.val.val = b.val.val := congrArg (fun x : C i => x.val) h
      exact Subtype.ext (Subtype.ext hv)
    have hsurj : Function.Surjective e := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩, rfl⟩
    let iso : K.induce i.supp ≃g G.induce (C i) :=
      ⟨Equiv.ofBijective e ⟨hinj,hsurj⟩, by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  have hnon : Nonempty W := by
    have hlt : ({v,w} : Finset V).card < Fintype.card V := by
      have hnV := card_ge_four_of_indepNum hg hi
      omega
    have hne : ∃ z : V, z ∉ ({v,w} : Finset V) := by
      by_contra! he
      have he' : ({v,w} : Finset V) = univ := eq_univ_of_forall he
      simp [he'] at hlt
    obtain ⟨z,hz⟩ := hne
    exact ⟨⟨z,hz⟩⟩
  have hlow : 1 < Fintype.card I := by
    by_contra! hnI
    have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hnI
    apply hs
    let _ : Nonempty W := hnon
    exact ⟨fun a b => ConnectedComponent.exact (Subsingleton.elim _ _)⟩
  have hsκ : ({v,w} : Finset V).card = vertexConnectivity G := hS.trans hk.symm
  have hhigh := min_cut_component_count ({v,w} : Finset V) v (by simp) hsκ ht C hn hout hcover
    (fun h a b => hsep h a b)
  have hcount : Fintype.card I = 2 ∨ Fintype.card I = 3 := by omega
  have hout' (i : I) : v ∉ C i ∧ w ∉ C i :=
    ⟨fun h => hout i v h (by simp), fun h => hout i w h (by simp)⟩
  have hcover' (x : V) (hxv : x ≠ v) (hxw : x ≠ w) : ∃ i, x ∈ C i :=
    hcover x (by simp [hxv,hxw])
  rcases hcount with htwo | hthree
  · let e := Fintype.equivFinOfCardEq htwo
    let A := C (e.symm 0)
    let B := C (e.symm 1)
    have hsep' : ∀ x ∈ A, ∀ y ∈ B, x ≠ y ∧ ¬ G.Adj x y :=
      fun x hx y hy => hsep (e.symm.injective.ne (by decide)) hx hy
    have hcover'' (x : V) (hxv : x ≠ v) (hxw : x ≠ w) : x ∈ A ∨ x ∈ B := by
      obtain ⟨i,hi⟩ := hcover' x hxv hxw
      have hEq : i = e.symm (e i) := (e.symm_apply_apply i).symm
      rw [hEq] at hi
      have hIdx : e i = 0 ∨ e i = 1 := by
        have hv : (e i).val < 2 := (e i).isLt
        rcases (show (e i).val = 0 ∨ (e i).val = 1 by omega) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hIdx with h | h
      · rw [h] at hi
        exact Or.inl hi
      · rw [h] at hi
        exact Or.inr hi
    by_cases hAB : G.IsClique A ∧ G.IsClique B
    · exact hamiltonian_of_two_clique_components v w hvw A B (hn _) (hn _) (hout' _) (hout' _)
        hsep' hcover'' (fun x hx y hy hne => hAB.1 hx hy hne)
        (fun x hx y hy hne => hAB.2 hx hy hne) hk.ge
    · exact step G hk (by omega) v w A B hvw (hn _) (hn _)
        (hout' _).1 (hout' _).2 (hout' _).1 (hout' _).2 (hconn _) (hconn _)
        hcover'' hsep' (by tauto)
  · let e := Fintype.equivFinOfCardEq hthree
    exact conjecture199_connectivity_two_three_components v w hvw hk ht (C ∘ e.symm)
      (fun i => hout' (e.symm i))
      (fun x hx hy => by obtain ⟨i,hi⟩ := hcover' x hx hy; exact ⟨e i, by simpa using hi⟩)
      (fun hij hx hy => hsep (e.symm.injective.ne hij) hx hy) (fun i => hconn (e.symm i))

/-- A checked split of WOWII #199 into the two remaining classes. -/
theorem conjecture199_reduction_local (h1 : TwoComponentStep.{u}) (h2 : HighConnectivityStep.{u})
    (G : SimpleGraph V) (hc : G.Connected)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases hα : G.indepNum ≤ 2
  · exact conjecture199_of_indepNum_le_two hc hα
  by_cases hκ1 : vertexConnectivity G ≤ 1
  · exact conjecture199_of_connectivity_le_one hc ht hκ1
  by_cases hκ2 : vertexConnectivity G = 2
  · exact connectivity_two_reduction h1 hc hκ2 (by omega) ht
  exact h2 G hc (by omega) (by omega) ht

#print axioms conjecture199_reduction_local
end Graph199
