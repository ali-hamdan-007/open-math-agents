import Graph199CompatibleSeparator
import Graph199DenseCutIncidence

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The component bound holds for separators of any order when each
deleted vertex meets at least κ components of the complement. -/
theorem separator_component_bound_of_min_row [Nontrivial V] (hG : G.Connected)
    (U : Finset V)
    (hmeet : ∀ u : U, vertexConnectivity G ≤
      {i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent | MeetsComponent U u.val i}.ncard)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
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
  let adj (u v : U) := G.Adj u.val v.val
  have hcompat (u v : U) (huv : u ≠ v) (h : adj u v ∨ (R u ∩ R v).Nonempty) :
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
  have hedge (x y : V) (he : G.Adj x y) : adj (f x) (f y) ∨ (R (f x) ∩ R (f y)).Nonempty := by
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
  have hreach (u v : U) :
      Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) u v := by
    have hf' (x : U) : f x.val = x := Subtype.ext ((hf x.val).1 x.property)
    have hh {x y : V} (h : Relation.ReflTransGen G.Adj x y) :
        Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) (f x) (f y) := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hxy ih => exact ih.tail (hedge _ _ hxy)
    have h := hh ((G.reachable_iff_reflTransGen _ _).mp (hG u.val v.val))
    rwa [hf',hf'] at h
  have hrlo (u : U) : vertexConnectivity G ≤ (R u).card := by
    have he : {i : I | MeetsComponent U u.val i} = (R u : Set I) := by
      ext i
      change MeetsComponent U u.val i ↔ i ∈ R u
      rw [hR]
      constructor
      · rintro ⟨y,hy,he⟩
        exact ⟨y.val,⟨y,hy,rfl⟩,he⟩
      · rintro ⟨x,⟨y,hy,rfl⟩,he⟩
        exact ⟨y,hy,he⟩
    have h := hmeet u
    change vertexConnectivity G ≤ {i : I | MeetsComponent U u.val i}.ncard at h
    rwa [he,Set.ncard_coe_finset] at h
  simpa only [Fintype.card_coe] using
    incidence_cut_bound_of_min_row R adj (vertexConnectivity G) hk hcol
      (fun u => ⟨hrlo u,hrow u⟩) hcompat hreach

#print axioms separator_component_bound_of_min_row
end Graph199
