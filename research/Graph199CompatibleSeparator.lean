import Graph199CliqueSeparatorBound

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A separator vertex meets a component of the graph after separator deletion. -/
abbrev MeetsComponent (U : Finset V) (u : V)
    (i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent) : Prop :=
  ∃ x : ↥((U : Set V)ᶜ), x ∈ i.supp ∧ G.Adj u x.val

/-- A separator has the same component-count bound if every distinct pair
of its vertices is adjacent or meets a common complementary component. -/
theorem compatible_separator_component_bound (U : Finset V)
    (hcompat : ∀ u v : U, u ≠ v →
      G.Adj u.val v.val ∨ ∃ i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent,
        MeetsComponent U u.val i ∧ MeetsComponent U v.val i)
    (hk : 0 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
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
  have hCn (i : I) : (C i).Nonempty :=
    ⟨i.out.val,i.out,i.out_eq,rfl⟩
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
  obtain ⟨R,hcol,hrow,hdist⟩ := separator_incidence_of_common_component U C hCn hCo hCc
    (fun he hx hy => hCs he hx hy) (by
      intro u v huv
      rcases hcompat u v huv with he | ⟨i,⟨x,hx,hux⟩,⟨y,hy,hvy⟩⟩
      · exact Or.inl he
      · exact Or.inr ⟨i,hconn i,⟨x.val,⟨x,hx,rfl⟩,hux⟩,⟨y.val,⟨y,hy,rfl⟩,hvy⟩⟩) ht
  simpa only [Fintype.card_coe] using incidence_clique_bound R (vertexConnectivity G) hk hcol hrow hdist

/-- A separator having one full complementary component satisfies the
component-count bound in WOWII #199. -/
theorem full_component_separator_bound (U : Finset V)
    (hfull : ∃ i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent,
      ∀ u : U, MeetsComponent U u.val i)
    (hk : 0 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  obtain ⟨i,hi⟩ := hfull
  exact compatible_separator_component_bound U
    (fun u v _ => Or.inr ⟨i,hi u,hi v⟩) hk ht

/-- Minimality for a fixed disconnected pair forces each separator vertex
to meet the complementary component containing the first vertex. -/
theorem full_component_of_minimal_pair_separator (U : Finset V)
    (a b : ↥((U : Set V)ᶜ))
    (hsep : ¬ (G.induce ((U : Set V)ᶜ)).Reachable a b)
    (hmin : ∀ u : U,
      (G.induce (↑(U.erase u.val) : Set V)ᶜ).Reachable
        ⟨a.val,fun h => a.property (mem_of_mem_erase h)⟩
        ⟨b.val,fun h => b.property (mem_of_mem_erase h)⟩) :
    ∃ i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent,
      ∀ u : U, MeetsComponent U u.val i := by
  classical
  let K := G.induce ((U : Set V)ᶜ)
  let i := K.connectedComponentMk a
  refine ⟨i,?_⟩
  intro u
  by_contra hn
  let W := ↥((↑(U.erase u.val) : Set V)ᶜ)
  let H := G.induce ((↑(U.erase u.val) : Set V)ᶜ)
  let a' : W := ⟨a.val,fun h => a.property (mem_of_mem_erase h)⟩
  let b' : W := ⟨b.val,fun h => b.property (mem_of_mem_erase h)⟩
  have hclosed {y : W} (hy : Relation.ReflTransGen H.Adj a' y) :
      ∃ d : ↥((U : Set V)ᶜ), d.val = y.val ∧ K.Reachable a d := by
    induction hy with
    | refl => exact ⟨a,rfl,Reachable.refl _⟩
    | tail _ hxy ih =>
      rename_i x y _
      obtain ⟨d,hd,had⟩ := ih
      have hAdj : G.Adj d.val y.val := hd.symm ▸ (show G.Adj x.val y.val from hxy)
      have hyU : y.val ∉ U := by
        intro hy
        have hyu : y.val = u.val := by
          by_contra hne
          exact y.property (mem_erase.mpr ⟨hne,hy⟩)
        have hm : d ∈ i.supp := by
          change K.connectedComponentMk d = K.connectedComponentMk a
          exact (ConnectedComponent.sound had).symm
        exact hn ⟨d,hm,hyu ▸ hAdj.symm⟩
      let q : ↥((U : Set V)ᶜ) := ⟨y.val,hyU⟩
      exact ⟨q,rfl,had.trans (show K.Adj d q from hAdj).reachable⟩
  obtain ⟨q,hqb,haq⟩ := hclosed ((H.reachable_iff_reflTransGen a' b').mp (hmin u))
  exact hsep (Subtype.ext hqb ▸ haq)

/-- Every inclusion-minimal separator for a fixed pair obeys the
component-count bound under WOWII #199's induced-tree hypothesis. -/
theorem minimal_pair_separator_component_bound (U : Finset V)
    (a b : ↥((U : Set V)ᶜ))
    (hsep : ¬ (G.induce ((U : Set V)ᶜ)).Reachable a b)
    (hmin : ∀ u : U,
      (G.induce (↑(U.erase u.val) : Set V)ᶜ).Reachable
        ⟨a.val,fun h => a.property (mem_of_mem_erase h)⟩
        ⟨b.val,fun h => b.property (mem_of_mem_erase h)⟩)
    (hk : 0 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 :=
  full_component_separator_bound U (full_component_of_minimal_pair_separator U a b hsep hmin) hk ht

#print axioms minimal_pair_separator_component_bound
#print axioms compatible_separator_component_bound
#print axioms full_component_separator_bound
end Graph199
