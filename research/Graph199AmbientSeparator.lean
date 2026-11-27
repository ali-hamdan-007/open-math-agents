import Graph199CompatibleSeparator
import Graph199GeneralCutIncidence
import Graph199ShortestConnector
import Graph199DistantRows

namespace Graph199

open SimpleGraph Finset

universe u

/-- Data extracted from a shortest compatibility connector between disjoint
full and almost-full separator rows. The outside sets are the actual
components of the graph left after deletion. -/
structure DistantRowConnector {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) {I : Type u} [Fintype I] [DecidableEq I]
    (C : I → Set V) (R : U → Finset I) (d : ℕ) (center : Fin (d+1) ↪ U) : Prop where
  component_nonempty : ∀ i, (C i).Nonempty
  component_outside : ∀ i x, x ∈ C i → x ∉ U
  component_cover : ∀ x ∉ U, ∃ i, x ∈ C i
  component_separated : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j →
    x ≠ y ∧ ¬ G.Adj x y
  component_connected : ∀ i, (G.induce (C i)).Connected
  touches : ∀ u i, i ∈ R u ↔ ∃ x ∈ C i, G.Adj u.val x
  column_bound : ∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card
  row_bound : ∀ u, (R u).card ≤ vertexConnectivity G + 1
  difference_bound : ∀ u v : U, u ≠ v →
    (G.Adj u.val v.val ∨ (R u ∩ R v).Nonempty) →
    ((R u \ R v) ∪ (R v \ R u)).card ≤ vertexConnectivity G
  length_bound : 3 ≤ d
  first_full : (R (center 0)).card = vertexConnectivity G + 1
  last_near_full : vertexConnectivity G ≤ (R (center (Fin.last d))).card
  endpoints_disjoint : Disjoint (R (center 0)) (R (center (Fin.last d)))
  consecutive : ∀ i : Fin d, G.Adj (center i.castSucc).val (center i.succ).val ∨
    (R (center i.castSucc) ∩ R (center i.succ)).Nonempty
  separated_centers : ∀ i j : Fin (d+1), i.val + 1 < j.val →
    ¬ G.Adj (center i).val (center j).val ∧ Disjoint (R (center i)) (R (center j))

private theorem compatible_size_bound {U I : Type*} [DecidableEq I]
    (R : U → Finset I) (K : SimpleGraph U) (k : ℕ)
    (hdist : ∀ u v, u ≠ v → (K.Adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    {a b : U} (h : (separatorCompatibility K R).Adj a b) :
    (R a).card + (R b).card ≤ k + 2 * (R a ∩ R b).card := by
  have hb := hdist a b h.1 h.2
  have hdis : Disjoint (R a \ R b) (R b \ R a) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [card_union_of_disjoint hdis] at hb
  have ha := card_sdiff_add_card_inter (R a) (R b)
  have hc := card_sdiff_add_card_inter (R b) (R a)
  rw [inter_comm (R b)] at hc
  omega

/-- Disjoint rows whose total size exceeds 2k have no compatibility edge
and no common compatibility neighbor. -/
theorem distant_rows_of_disjoint_large_sets {U I : Type*} [DecidableEq I]
    (R : U → Finset I) (K : SimpleGraph U) (k : ℕ)
    (hdist : ∀ u v, u ≠ v → (K.Adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    {a b : U} (hdisj : Disjoint (R a) (R b)) (hlarge : 2*k < (R a).card + (R b).card) :
    a ≠ b ∧ ¬ (separatorCompatibility K R).Adj a b ∧
      ∀ w, ¬ ((separatorCompatibility K R).Adj a w ∧
        (separatorCompatibility K R).Adj w b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    subst b
    have hz : R a = ∅ := disjoint_self.mp hdisj
    simp [hz] at hlarge
  · intro he
    have hb := compatible_size_bound R K k hdist he
    have hz : R a ∩ R b = ∅ := disjoint_iff_inter_eq_empty.mp hdisj
    simp only [hz, card_empty, mul_zero, add_zero] at hb
    omega
  · intro w he
    have hl := compatible_size_bound R K k hdist he.1
    have hr := compatible_size_bound R K k hdist he.2
    have hlt : (R w).card < (R a ∩ R w).card + (R w ∩ R b).card := by omega
    obtain ⟨x,hx⟩ := inter_nonempty_of_card_lt_card_add_card inter_subset_right inter_subset_left hlt
    obtain ⟨hL,hR⟩ := mem_inter.mp hx
    exact Finset.disjoint_left.mp hdisj (mem_inter.mp hL).1 (mem_inter.mp hR).2

/-- An induced-tree bound on distant compatibility rows suffices for the
component-count conclusion for every separator. -/
theorem all_separator_component_bound_of_distant_rows {V : Type u}
    [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
    (large_tree_of_distant_rows :
      ∀ {I : Type u} [Fintype I] [DecidableEq I] {U : Finset V} {C : I → Set V}
        {R : U → Finset I} {d : ℕ} {center : Fin (d+1) ↪ U},
        DistantRowConnector G U C R d center →
          vertexConnectivity G + 3 ≤ largestInducedTreeSize G)
    (hG : G.Connected) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
  intro U
  have hk := vertexConnectivity_pos_of_connected hG
  let W := ↥((U : Set V)ᶜ)
  let K := G.induce ((U : Set V)ᶜ)
  let I := K.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  change Nat.card I ≤ _
  rw [Nat.card_eq_fintype_card]
  rcases subsingleton_or_nontrivial I with hs | hi
  · have h : Fintype.card I ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega
  let C (i : I) : Set V := Subtype.val '' i.supp
  have hCn (i : I) : (C i).Nonempty := ⟨i.out.val,i.out,i.out_eq,rfl⟩
  have hCo (i : I) (x : V) (hx : x ∈ C i) : x ∉ U := by
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  have hCc (x : V) (hx : x ∉ U) : ∃ i, x ∈ C i := by
    let y : W := ⟨x,hx⟩
    exact ⟨K.connectedComponentMk y,y,rfl,rfl⟩
  have hCs {i j : I} {x y : V} (hij : i ≠ j)
      (hx : x ∈ C i) (hy : y ∈ C j) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    change K.connectedComponentMk a = i at ha
    change K.connectedComponentMk b = j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by rwa [ha,hb]
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj (show K.Adj a b from he))⟩
  have hconn (i : I) : (G.induce (C i)).Connected := by
    let e : i.supp → C i := fun x => ⟨x.val.val,x.val,x.property,rfl⟩
    have hinj : Function.Injective e := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : C i => x.val) h))
    have hsurj : Function.Surjective e := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    let iso : K.induce i.supp ≃g G.induce (C i) :=
      ⟨Equiv.ofBijective e ⟨hinj,hsurj⟩,by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  obtain ⟨R,hR,hcol,hrow,hdist⟩ := separator_incidence_partial U C hCn hCo hCc
    (fun he hx hy => hCs he hx hy) ht
  let Ksep := G.induce (U : Set V)
  let H := separatorCompatibility Ksep R
  have hcompat (u v : U) (huv : u ≠ v) (h : Ksep.Adj u v ∨ (R u ∩ R v).Nonempty) :
      ((R u \ R v) ∪ (R v \ R u)).card ≤ vertexConnectivity G := by
    apply hdist u v huv
    rcases h with h | ⟨i,hi⟩
    · exact Or.inl h
    · obtain ⟨hu,hv⟩ := mem_inter.mp hi
      exact Or.inr ⟨i,hconn i,(hR u i).mp hu,(hR v i).mp hv⟩
  have hlabel (x : V) : ∃ u : U, (x ∈ U → u.val = x) ∧
      (∀ i, x ∈ C i → i ∈ R u) := by
    by_cases hxu : x ∈ U
    · exact ⟨⟨x,hxu⟩,fun _ => rfl,fun i h => (hCo i x h hxu).elim⟩
    · obtain ⟨i,hi⟩ := hCc x hxu
      have hpos := hk.trans_le (hcol i)
      obtain ⟨u,hu⟩ := card_pos.mp hpos
      have hu' := (mem_filter.mp hu).2
      refine ⟨u,fun h => (hxu h).elim,?_⟩
      intro j hj
      have he : i = j := by
        by_contra h
        exact (hCs h hi hj).1 rfl
      exact he ▸ hu'
  choose f hf using hlabel
  have hedge (x y : V) (he : G.Adj x y) :
      Ksep.Adj (f x) (f y) ∨ (R (f x) ∩ R (f y)).Nonempty := by
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · exact Or.inl (by change G.Adj (f x).val (f y).val; rwa [(hf x).1 hx,(hf y).1 hy])
      · obtain ⟨i,hi⟩ := hCc y hy
        have hm := (hf y).2 i hi
        have hn : i ∈ R (f x) := (hR _ _).mpr ⟨y,hi,by rwa [(hf x).1 hx]⟩
        exact Or.inr ⟨i,mem_inter.mpr ⟨hn,hm⟩⟩
    · obtain ⟨i,hi⟩ := hCc x hx
      have hm := (hf x).2 i hi
      by_cases hy : y ∈ U
      · have hn : i ∈ R (f y) := (hR _ _).mpr ⟨x,hi,by rw [(hf y).1 hy]; exact he.symm⟩
        exact Or.inr ⟨i,mem_inter.mpr ⟨hm,hn⟩⟩
      · obtain ⟨j,hj⟩ := hCc y hy
        have hij : i = j := by
          by_contra hn
          exact (hCs hn hi hj).2 he
        subst j
        exact Or.inr ⟨i,mem_inter.mpr ⟨hm,(hf y).2 i hj⟩⟩
  have hreach (u v : U) : H.Reachable u v := by
    have hf' (x : U) : f x.val = x := Subtype.ext ((hf x.val).1 x.property)
    have hh {x y : V} (h : Relation.ReflTransGen G.Adj x y) :
        H.Reachable (f x) (f y) := by
      induction h with
      | refl => exact Reachable.rfl
      | @tail a b _ hab ih =>
        by_cases he : f a = f b
        · exact he ▸ ih
        · exact ih.trans (show H.Adj (f a) (f b) from ⟨he,hedge a b hab⟩).reachable
    have h := hh ((G.reachable_iff_reflTransGen _ _).mp (hG u.val v.val))
    rwa [hf',hf'] at h
  have hoverlap (a b : U) (ha : (R a).card = vertexConnectivity G + 1)
      (hb : vertexConnectivity G ≤ (R b).card) : (R a ∩ R b).Nonempty := by
    by_contra! hn
    have hdisj : Disjoint (R a) (R b) := disjoint_iff_inter_eq_empty.mpr hn
    have hlarge : 2 * vertexConnectivity G < (R a).card + (R b).card := by omega
    obtain ⟨hne, hnot, hno2⟩ :=
      distant_rows_of_disjoint_large_sets R Ksep _ hcompat hdisj hlarge
    have hdl := connector_dist_ge_three (hreach a b) hne hnot hno2
    obtain ⟨d, center, hde, hf, hl, hstep, hgap⟩ :=
      separator_shortest_connector Ksep R (hreach a b)
    have hd : 3 ≤ d := hde.symm ▸ hdl
    have profile : DistantRowConnector G U C R d center :=
      ⟨hCn, hCo, hCc, @hCs, hconn, hR, hcol, hrow, hcompat, hd,
       hf.symm ▸ ha, hl.symm ▸ hb, hf.symm ▸ hl.symm ▸ hdisj, hstep, hgap⟩
    have ht' := large_tree_of_distant_rows profile
    omega
  simpa only [Fintype.card_coe] using
    incidence_cut_bound_of_full_overlap R Ksep.Adj _ hk hcol hrow hcompat hoverlap

/-- In the ambient graph the distant-row profile gives an induced tree
with at least four more vertices than the vertex connectivity. -/
theorem large_tree_of_distant_row_profile {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {I : Type u} [Fintype I] [DecidableEq I] {U : Finset V}
    {C : I → Set V} {R : U → Finset I} {d : ℕ} {center : Fin (d+1) ↪ U}
    (D : DistantRowConnector G U C R d center) :
    vertexConnectivity G + 4 ≤ largestInducedTreeSize G := by
  let c : Fin (d+1) ↪ V := center.trans ⟨Subtype.val,Subtype.val_injective⟩
  let S (i : Fin (d+1)) := R (center i)
  have ht (i : Fin (d+1)) (k : I) : k ∈ S i ↔ ∃ x ∈ C k, G.Adj (c i) x :=
    D.touches (center i) k
  have ho (i : Fin (d+1)) (k : I) : c i ∉ C k := by
    intro hi
    exact D.component_outside k _ hi (center i).property
  have hc (j : Fin d) : G.Adj (c j.castSucc) (c j.succ) ∨
      ∃ k, k ∈ S j.castSucc ∧ k ∈ S j.succ := by
    rcases D.consecutive j with h | ⟨k,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨k,mem_inter.mp hk⟩
  have hclose (i j : Fin (d+1)) (h : G.Adj (c i) (c j)) :
      i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 := by
    constructor
    · by_contra! he
      exact (D.separated_centers j i he).1 h.symm
    · by_contra! he
      exact (D.separated_centers i j he).1 h
  have hnear (i j : Fin (d+1)) (k : I) (hi : k ∈ S i) (hj : k ∈ S j) :
      i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 := by
    constructor
    · by_contra! he
      exact Finset.disjoint_left.mp (D.separated_centers j i he).2 hj hi
    · by_contra! he
      exact Finset.disjoint_left.mp (D.separated_centers i j he).2 hi hj
  have htree := large_tree_of_distant_rows (G := G) (by have := D.length_bound; omega)
    c C S ht ho (fun _ _ he _ hx _ hy => D.component_separated he hx hy)
    D.component_connected hc hclose hnear
  change 2*d + (R (center 0)).card + (R (center (Fin.last d))).card ≤
    2 * largestInducedTreeSize G at htree
  rw [D.first_full] at htree
  have hl := D.last_near_full
  have hd := D.length_bound
  omega

/-- The induced-tree hypothesis forces the component-count condition for
every deleted vertex set, at every positive vertex connectivity. -/
theorem all_separator_component_bound {V : Type u}
    [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
    (hG : G.Connected) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 :=
  all_separator_component_bound_of_distant_rows
    (fun D => Nat.le_trans (by omega) (large_tree_of_distant_row_profile D)) hG ht

#print axioms distant_rows_of_disjoint_large_sets
#print axioms all_separator_component_bound_of_distant_rows
#print axioms all_separator_component_bound
end Graph199
