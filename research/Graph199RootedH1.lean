import Graph199Noncliques

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem arm_star_two_spokes (v a b x y : V)
    (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hva : G.Adj v a) (hab : G.Adj a b) (hvb : ¬ G.Adj v b) (hbv : b ≠ v)
    (hxy : x ≠ y) (hnxy : ¬ G.Adj x y)
    (hax : a ≠ x ∧ ¬ G.Adj a x) (hay : a ≠ y ∧ ¬ G.Adj a y)
    (hbx : b ≠ x ∧ ¬ G.Adj b x) (hby : b ≠ y ∧ ¬ G.Adj b y) :
    5 ≤ largestInducedTreeSize G := by
  let S : Finset V := {x,y}
  have hS : S.card = 2 := by
    change ({x,y} : Finset V).card = 2
    rw [card_insert_of_notMem (show x ∉ ({y} : Finset V) from by simpa using hxy), card_singleton]
  have hnd : (S : Set V).Pairwise (fun w z => ¬ G.Adj w z) := by
    intro w hw z hz hne
    simp only [S, mem_coe, mem_insert, mem_singleton] at hw hz
    rcases hw with rfl | rfl <;> rcases hz with rfl | rfl
    · exact (hne rfl).elim
    · exact hnxy
    · exact fun he => hnxy he.symm
    · exact (hne rfl).elim
  have hin (w : V) (hw : w ∈ S) : w = x ∨ w = y := by
    simpa [S] using hw
  have h := arm_star_bound v a b S hnd (by
      intro w hw
      rcases hin w hw with rfl | rfl
      · exact hvx
      · exact hvy) hva hab hvb hbv (by simp [S,hax.1,hay.1]) (by simp [S,hbx.1,hby.1])
    (fun w hw h => (hin w hw).elim (fun he => hbx.2 (he ▸ h)) (fun he => hby.2 (he ▸ h)))
    (fun w hw h => (hin w hw).elim (fun he => hax.2 (he ▸ h)) (fun he => hay.2 (he ▸ h)))
  omega

/-- Within the vertices of the far side missed by the separator, adjacency to
a neighbor of the separator is constant along edges. -/
theorem rooted_attachment_edge (v z a x y : V)
    (hvz : G.Adj v z) (hva : G.Adj v a)
    (hnza : z ≠ a ∧ ¬ G.Adj z a)
    (hnzx : z ≠ x ∧ ¬ G.Adj z x) (hnzy : z ≠ y ∧ ¬ G.Adj z y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hnvx : ¬ G.Adj v x) (hnvy : ¬ G.Adj v y)
    (hxy : G.Adj x y) (hax : G.Adj a x) (hay : y ≠ a)
    (ht : largestInducedTreeSize G ≤ 4) :
    G.Adj a y := by
  by_contra hnay
  have h := two_arms_bound a v z x y hva.symm hvz
    (fun he => hnza.2 he.symm) hax hxy hnay hnza.1 hay
    ⟨hxv.symm,hnvx⟩ ⟨hyv.symm,hnvy⟩ hnzx hnzy
  omega

/-- Any two far-side non-neighbors of the separator sharing an attachment
neighbor must be adjacent. -/
theorem rooted_shared_attachment_clique (v z a x y : V)
    (hvz : G.Adj v z) (hva : G.Adj v a)
    (hnza : z ≠ a ∧ ¬ G.Adj z a)
    (hnzx : z ≠ x ∧ ¬ G.Adj z x) (hnzy : z ≠ y ∧ ¬ G.Adj z y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hnvx : ¬ G.Adj v x) (hnvy : ¬ G.Adj v y)
    (hax : G.Adj a x) (hay : G.Adj a y) (hxy : x ≠ y)
    (ht : largestInducedTreeSize G ≤ 4) :
    G.Adj x y := by
  by_contra hn
  have h := arm_star_two_spokes a v z x y hax hay hva.symm hvz (fun h => hnza.2 h.symm)
    hnza.1 hxy hn ⟨hxv.symm,hnvx⟩ ⟨hyv.symm,hnvy⟩ hnzx hnzy
  omega

/-- A separator neighbor that has an attachment to one far block is adjacent
to every separator neighbor which misses that block. -/
theorem rooted_cross_attachment (v z a a' x : V)
    (hvz : G.Adj v z) (hva : G.Adj v a) (hva' : G.Adj v a')
    (hnza : z ≠ a ∧ ¬ G.Adj z a) (hnza' : z ≠ a' ∧ ¬ G.Adj z a')
    (hnzx : z ≠ x ∧ ¬ G.Adj z x)
    (hxv : x ≠ v) (hnvx : ¬ G.Adj v x)
    (haa' : a ≠ a') (hax : G.Adj a x) (hnxa' : x ≠ a' ∧ ¬ G.Adj x a')
    (ht : largestInducedTreeSize G ≤ 4) :
    G.Adj a a' := by
  by_contra hn
  have h := arm_star_two_spokes v a x z a' hvz hva' hva hax hnvx hxv
    hnza'.1 hnza'.2 ⟨hnza.1.symm,fun he => hnza.2 he.symm⟩ ⟨haa',hn⟩
    ⟨hnzx.1.symm,fun he => hnzx.2 he.symm⟩ hnxa'
  omega

/-- An attachment edge into a connected far block forces adjacency to every
vertex of that block. -/
theorem rooted_attachment_all (v z a : V) (T : Set V)
    (hvz : G.Adj v z) (hva : G.Adj v a) (hnza : z ≠ a ∧ ¬ G.Adj z a)
    (hfar : ∀ x ∈ T, x ≠ v ∧ (z ≠ x ∧ ¬ G.Adj z x) ∧ ¬ G.Adj v x)
    (hc : (G.induce T).Connected) (ha : ∃ x ∈ T, G.Adj a x)
    (ht : largestInducedTreeSize G ≤ 4) :
    ∀ y ∈ T, G.Adj a y := by
  obtain ⟨x,hx,hax⟩ := ha
  intro y hy
  let K := G.induce T
  let p : T := ⟨x,hx⟩
  let q : T := ⟨y,hy⟩
  have hreach := (K.reachable_iff_reflTransGen p q).mp (hc p q)
  have propagate {b : T} (h : Relation.ReflTransGen K.Adj p b) : G.Adj a b.val := by
    induction h with
    | refl => exact hax
    | tail _ hxy ih =>
      rename_i x y _
      have hX := hfar x.val x.property
      have hY := hfar y.val y.property
      have hne : y.val ≠ a := fun he => hY.2.2 (he ▸ hva)
      exact rooted_attachment_edge v z a x.val y.val hvz hva hnza hX.2.1 hY.2.1
        hX.1 hY.1 hX.2.2 hY.2.2 hxy ih hne ht
  exact propagate hreach

/-- Far components are cliques, and each has a nonempty attachment class.
Any separator neighbor attaches to at most one far component. -/
theorem rooted_far_component_structure {I : Type*} (v z : V) (A : Set V) (T : I → Set V)
    (hvz : G.Adj v z) (hvA : v ∉ A)
    (hsep : ∀ x ∈ A, z ≠ x ∧ ¬ G.Adj z x) (hcA : (G.induce A).Connected)
    (hmeet : ∃ a ∈ A, G.Adj v a)
    (hfar : ∀ i x, x ∈ T i → x ∈ A ∧ ¬ G.Adj v x)
    (hcover : ∀ x ∈ A, ¬ G.Adj v x → ∃ i, x ∈ T i)
    (hdis : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ T i → y ∈ T j → x ≠ y ∧ ¬ G.Adj x y)
    (hconn : ∀ i, (G.induce (T i)).Connected) (ht : largestInducedTreeSize G ≤ 4) :
    (∀ i, G.IsClique (T i) ∧
      ∃ a ∈ A, G.Adj v a ∧ ∀ x ∈ T i, G.Adj a x) ∧
    (∀ a ∈ A, G.Adj v a → ∀ {i j : I} {x y : V},
      x ∈ T i → y ∈ T j → G.Adj a x → G.Adj a y → i = j) := by
  classical
  constructor
  · intro i
    let S : Finset A := univ.filter (fun x => x.val ∈ T i)
    have hS : S.Nonempty := by
      obtain ⟨x⟩ := (hconn i).nonempty
      exact ⟨⟨x.val,(hfar i _ x.property).1⟩, mem_filter.mpr ⟨mem_univ _,x.property⟩⟩
    have hSu : S ≠ univ := by
      obtain ⟨y, hy, hvy⟩ := hmeet
      intro he
      have hm : (⟨y,hy⟩ : A) ∈ S := he ▸ mem_univ _
      exact (hfar i y (mem_filter.mp hm).2).2 hvy
    obtain ⟨a, ha, x, hx, hax⟩ := hcA.exists_adj_finset_compl hS hSu
    have hxi : x.val ∈ T i := (mem_filter.mp hx).2
    have hva : G.Adj v a.val := by
      by_contra hn
      obtain ⟨j,haj⟩ := hcover a.val a.property hn
      have hji : j ≠ i := by
        intro he
        subst j
        exact ha (mem_filter.mpr ⟨mem_univ _,haj⟩)
      exact (hdis hji haj hxi).2 hax
    have hall := rooted_attachment_all v z a.val (T i) hvz hva (hsep _ a.property)
      (fun x hx => ⟨fun he => hvA (he ▸ (hfar i x hx).1),hsep _ (hfar i x hx).1,
        (hfar i x hx).2⟩) (hconn i) ⟨x.val,hxi,hax⟩ ht
    refine ⟨?_, a.val,a.property,hva,hall⟩
    intro x hx y hy hxy
    have hx' := hfar i x hx
    have hy' := hfar i y hy
    exact rooted_shared_attachment_clique v z a.val x y hvz hva (hsep _ a.property)
      (hsep _ hx'.1) (hsep _ hy'.1) (fun he => hvA (he ▸ hx'.1))
      (fun he => hvA (he ▸ hy'.1)) hx'.2 hy'.2 (hall x hx) (hall y hy) hxy ht
  · intro a ha hva i j x y hx hy hax hay
    by_contra hne
    have hx' := hfar i x hx
    have hy' := hfar j y hy
    exact (hdis hne hx hy).2 (rooted_shared_attachment_clique v z a x y hvz hva (hsep _ ha)
      (hsep _ hx'.1) (hsep _ hy'.1) (fun he => hvA (he ▸ hx'.1))
      (fun he => hvA (he ▸ hy'.1)) hx'.2 hy'.2 hax hay (hdis hne hx hy).1 ht)

#print axioms rooted_attachment_all
#print axioms rooted_far_component_structure
#print axioms rooted_attachment_edge
#print axioms rooted_shared_attachment_clique
#print axioms rooted_cross_attachment
end Graph199
