import Graph189MatchingExtension
import BipartiteMissingMatching

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Prepend the exceptional vertex to the indexed path, starting at a chosen neighbor. -/
theorem hamiltonian_of_indexed_matching {k : ℕ} (hk : 3 ≤ k) (z : V)
    (f : Fin k ⊕ Option (Fin k) → V) (hfinj : Function.Injective f)
    (hfz : ∀ a, f a ≠ z) (hfcover : ∀ a, a ≠ z → ∃ i, f i = a)
    (hcross : ∀ i j : Fin k, i ≠ j → G.Adj (f (.inl i)) (f (.inr (some j))))
    (hfree : ∀ i : Fin k, G.Adj (f (.inl i)) (f (.inr none)))
    (start : Option (Fin k)) (hstart : G.Adj z (f (.inr start))) :
    ∃ b, ∃ p : G.Walk z b, p.IsHamiltonian := by
  let H := G.comap f
  obtain ⟨b,p,hp⟩ := BipartiteMissingMatching.hamiltonian_from_right hk H hcross hfree start
  let q : G.Walk (f (.inr start)) (f b) := p.map (SimpleGraph.Hom.comap f G)
  have hqs : q.support = p.support.map f := p.support_map _
  have hzq : z ∉ q.support := by
    rw [hqs]
    intro hz
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hz
    exact hfz i hi
  have hnodup : (Walk.cons hstart q).support.Nodup := by
    simpa [hqs, hzq, List.nodup_cons] using
      And.intro hzq (hp.isPath.support_nodup.map hfinj)
  refine ⟨f b, .cons hstart q, (Walk.IsPath.mk' hnodup).isHamiltonian_of_mem ?_⟩
  intro a
  rw [Walk.support_cons]
  by_cases ha : a = z
  · simp [ha]
  · obtain ⟨i,rfl⟩ := hfcover a ha
    exact List.mem_cons_of_mem _ (hqs ▸ List.mem_map_of_mem (hp.mem_support i))


/-- In equal-sized parts of size at least four, choosing the exceptional vertex
in its own part allows the remaining graph to be indexed by a missing matching. -/
theorem hamiltonian_balanced_large [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hsize : (part C c).card = (part C d).card)
    (hlarge : 4 ≤ (part C c).card) (z : V) (hz : z ∈ part C c)
    (hhigh : ∀ x, x ≠ z → secondSmallestDegree G ≤ G.degree x) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let left := (part C c).erase z
  let right := part C d
  let k := left.card
  have hk' : k = (part C c).card - 1 := Finset.card_erase_of_mem hz
  have hk : 3 ≤ k := by omega
  have hcard : right.card = k + 1 := by dsimp [right]; omega
  have hparts (v : V) : v ∈ part C c ∨ v ∈ right := by
    simp only [right, mem_part]
    generalize C v = e
    fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all
  have hdis (x : V) (hx : x ∈ part C c) (hy : x ∈ right) : False :=
    hcd (((mem_part C c x).mp hx).symm.trans ((mem_part C d x).mp hy))
  have hzleft : z ∉ left := Finset.notMem_erase _ _
  have hzright : z ∉ right := hdis z hz
  let domain := left.filter fun x => ∃ y ∈ right, ¬ G.Adj x y
  have hdom := Finset.filter_subset (fun x => ∃ y ∈ right, ¬ G.Adj x y) left
  let q (x : V) := if hx : ∃ y ∈ right, ¬ G.Adj x y then hx.choose else z
  have hq (x : V) (hx : x ∈ domain) : q x ∈ right ∧ ¬ G.Adj x (q x) := by
    have hd := (Finset.mem_filter.mp hx).2
    simpa [q, hd] using hd.choose_spec
  have hqinj : Set.InjOn q domain := by
    intro x hx y hy he
    obtain ⟨hr,hm⟩ := hq x hx
    have hx' := Finset.mem_of_mem_erase (hdom hx)
    have hy' := Finset.mem_of_mem_erase (hdom hy)
    exact balanced_missing_edges h C hσ hcd.symm hsize.symm hr
      (hhigh _ (fun heq => hzright (heq ▸ hr))) x hx' y hy'
      (fun e => hm e.symm) (fun e => (hq y hy).2 (he ▸ e.symm))
  obtain ⟨e,heinj,her,heq⟩ :=
    extend_partial_matching left right domain hdom (by omega) q hqinj (fun x hx => (hq x hx).1)
  have hmatch (x : V) (hx : x ∈ left) (y : V) (hy : y ∈ right) (hm : ¬ G.Adj x y) :
      e x = y := by
    have hd : x ∈ domain := Finset.mem_filter.mpr ⟨hx,y,hy,hm⟩
    rw [heq x hd]
    exact balanced_missing_edges h C hσ hcd hsize (Finset.mem_of_mem_erase hx)
      (hhigh _ (Finset.ne_of_mem_erase hx)) (q x) (hq x hd).1 y hy (hq x hd).2 hm
  obtain ⟨w,⟨hwr,hwout⟩,hwunique⟩ :=
    Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one heinj her hcard
  let el : Fin k ≃ left :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe left)).symm
  let l (i : Fin k) : V := (el i).val
  have hl (i : Fin k) : l i ∈ left := (el i).property
  have hlinj : Function.Injective l := fun _ _ he => el.injective (Subtype.ext he)
  have hlsurj (x : V) (hx : x ∈ left) : ∃ i, l i = x := by
    obtain ⟨i,hi⟩ := el.surjective ⟨x,hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  let r (o : Option (Fin k)) : V := o.elim w (fun i => e (l i))
  have hr (o : Option (Fin k)) : r o ∈ right := by
    cases o with
    | none => exact hwr
    | some i => exact her (hl i)
  have hwne (i : Fin k) : e (l i) ≠ w := fun he =>
    hwout (he ▸ Finset.mem_image_of_mem e (hl i))
  have hrinj : Function.Injective r := by
    intro i j he
    cases i <;> cases j
    · rfl
    · exact (hwne _ he.symm).elim
    · exact (hwne _ he).elim
    · exact congrArg some (hlinj (heinj (hl _) (hl _) he))
  have hrsurj (y : V) (hy : y ∈ right) : ∃ o, r o = y := by
    by_cases him : y ∈ left.image e
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp him
      obtain ⟨i,rfl⟩ := hlsurj x hx
      exact ⟨some i,rfl⟩
    · exact ⟨none,(hwunique y ⟨hy,him⟩).symm⟩
  let f : Fin k ⊕ Option (Fin k) → V := Sum.elim l r
  have hfinj : Function.Injective f := by
    intro a b he
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hlinj he)
      | inr j =>
        have he' : l i = r j := he
        exact (hdis (l i) (Finset.mem_of_mem_erase (hl i)) (he'.symm ▸ hr j)).elim
    | inr i =>
      cases b with
      | inl j =>
        have he' : r i = l j := he
        exact (hdis (l j) (Finset.mem_of_mem_erase (hl j)) (he' ▸ hr i)).elim
      | inr j => exact congrArg Sum.inr (hrinj he)
  have hfz (a) : f a ≠ z := by
    cases a with
    | inl i => exact Finset.ne_of_mem_erase (hl i)
    | inr i => exact fun he => hzright (he ▸ hr i)
  have hfcover (v : V) (hv : v ≠ z) : ∃ a, f a = v := by
    rcases hparts v with hv' | hv'
    · obtain ⟨i,hi⟩ := hlsurj v (Finset.mem_erase.mpr ⟨hv,hv'⟩)
      exact ⟨.inl i,hi⟩
    · obtain ⟨i,hi⟩ := hrsurj v hv'
      exact ⟨.inr i,hi⟩
  have hcross (i j : Fin k) (hij : i ≠ j) : G.Adj (l i) (e (l j)) := by
    by_contra hn
    exact hij (hlinj (heinj (hl i) (hl j) (hmatch _ (hl i) _ (her (hl j)) hn)))
  have hfree (i : Fin k) : G.Adj (l i) w := by
    by_contra hn
    exact hwne i (hmatch _ (hl i) _ hwr hn)
  obtain ⟨x,hzx⟩ := h.preconnected.exists_adj_of_nontrivial z
  have hxr := neighborFinset_subset_part C hcd hz ((G.mem_neighborFinset z x).mpr hzx)
  obtain ⟨start,hs⟩ := hrsurj x hxr
  obtain ⟨b,p,hp⟩ := hamiltonian_of_indexed_matching hk z f hfinj hfz hfcover
    hcross hfree start (by change G.Adj z (r start); rwa [hs])
  exact ⟨z,b,p,hp⟩

#print axioms hamiltonian_of_indexed_matching
#print axioms hamiltonian_balanced_large
end Graph189Bipartite
