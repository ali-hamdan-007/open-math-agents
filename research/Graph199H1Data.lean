import Graph199RootedH1

namespace Graph199
open SimpleGraph Finset

universe u

/-- The rooted block decomposition of the nonclique side of an H1 minimum cut. -/
structure H1FarData {V : Type u} (G : SimpleGraph V) (v w : V) (A : Set V) where
  n : ℕ
  positive : 0 < n
  far : Fin n → Set V
  near : Fin n → Set V
  spare : Set V
  far_nonempty : ∀ i, (far i).Nonempty
  near_nonempty : ∀ i, (near i).Nonempty
  far_clique : ∀ i, G.IsClique (far i)
  far_facts : ∀ i x, x ∈ far i → x ∈ A ∧ ¬ G.Adj v x
  near_facts : ∀ i x, x ∈ near i → x ∈ A ∧ G.Adj v x
  spare_facts : ∀ x ∈ spare, x ∈ A ∧ G.Adj v x
  far_separated : ∀ {i j} {x y}, i ≠ j → x ∈ far i → y ∈ far j → x ≠ y ∧ ¬ G.Adj x y
  near_disjoint : ∀ {i j} {x}, i ≠ j → x ∈ near i → x ∉ near j
  spare_disjoint : ∀ i x, x ∈ spare → x ∉ near i
  blocks_cover : ∀ x ∈ A, x ∈ spare ∨ ∃ i, x ∈ far i ∨ x ∈ near i
  same_attachment_complete : ∀ i x y, x ∈ near i → y ∈ far i → G.Adj x y
  cross_attachment_complete : ∀ {i j} {x y}, i ≠ j → x ∈ near i → y ∈ near j → G.Adj x y
  spare_attachment_complete : ∀ i x y, x ∈ spare → y ∈ near i → G.Adj x y
  near_no_independent_triple : ∀ x y z : V, x ∈ A → y ∈ A → z ∈ A →
    G.Adj v x → G.Adj v y → G.Adj v z → x ≠ y → x ≠ z → y ≠ z →
    ¬ G.Adj x y → ¬ G.Adj x z → ¬ G.Adj y z → False
  singleton_hooks : ∀ i a, near i = {a} → ∃ x ∈ far i, G.Adj w x
  at_most_two_singleton : {i | ∃ a, near i = {a}}.ncard ≤ 2

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem independent_four_spokes (v a b c d : V)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) (hd : G.Adj v d)
    (hab : a ≠ b ∧ ¬ G.Adj a b) (hac : a ≠ c ∧ ¬ G.Adj a c)
    (had : a ≠ d ∧ ¬ G.Adj a d) (hbc : b ≠ c ∧ ¬ G.Adj b c)
    (hbd : b ≠ d ∧ ¬ G.Adj b d) (hcd : c ≠ d ∧ ¬ G.Adj c d)
    (ht : largestInducedTreeSize G ≤ 4) : False := by
  have hind : (↑({a,b,c,d} : Finset V) : Set V).Pairwise (fun x y => ¬ G.Adj x y) := by
    intro x hx y hy hne
    simp only [mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | contradiction
            | exact hab.2 | exact hac.2 | exact had.2 | exact hbc.2 | exact hbd.2 | exact hcd.2
            | exact (fun he => hab.2 he.symm) | exact (fun he => hac.2 he.symm)
            | exact (fun he => had.2 he.symm) | exact (fun he => hbc.2 he.symm)
            | exact (fun he => hbd.2 he.symm) | exact (fun he => hcd.2 he.symm)
  have hcard : ({a,b,c,d} : Finset V).card = 4 := by
    rw [card_insert_of_notMem (by simp [hab.1,hac.1,had.1]), card_insert_of_notMem (by simp [hbc.1,hbd.1]),
      card_insert_of_notMem (by simp [hcd.1]), card_singleton]
  have h := star_bound v {a,b,c,d} hind (by simp [ha,hb,hc,hd])
  omega

/-- Construct the finite rooted decomposition from an actual minimum two-cut. -/
noncomputable def h1FarData (v w : V) (A B : Set V)
    (houtA : v ∉ A ∧ w ∉ A)
    (hcover : ∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B)
    (hA : (G.induce A).Connected) (hB : B.Nonempty)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y ∧ ¬ G.Adj x y)
    (hvB : ∀ y ∈ B, G.Adj v y) (hwB : ∀ y ∈ B, G.Adj w y)
    (hvA : ∃ x ∈ A, G.Adj v x) (hnot : ∃ x ∈ A, ¬ G.Adj v x)
    (hκ : 2 ≤ vertexConnectivity G) (ht : largestInducedTreeSize G ≤ 4) :
    H1FarData G v w A := by
  classical
  let z := Classical.choose hB
  have hz : z ∈ B := Classical.choose_spec hB
  have hzA (x : V) (hx : x ∈ A) : z ≠ x ∧ ¬ G.Adj z x :=
    ⟨(hsep x hx z hz).1.symm, fun h => (hsep x hx z hz).2 h.symm⟩
  let T := {x | x ∈ A ∧ ¬ G.Adj v x}
  let K := G.induce T
  let J := K.ConnectedComponent
  let _ : Finite J := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype J := Fintype.ofFinite J
  let n := Fintype.card J
  let e := Fintype.equivFin J
  let F (i : Fin n) : Set V := Subtype.val '' (e.symm i).supp
  have hf (i : Fin n) (x : V) (hx : x ∈ F i) : x ∈ A ∧ ¬ G.Adj v x := by
    obtain ⟨q,_,rfl⟩ := hx
    exact q.property
  have hfcov (x : V) (hx : x ∈ A) (hxa : ¬ G.Adj v x) : ∃ i, x ∈ F i := by
    let q : T := ⟨x,hx,hxa⟩
    exact ⟨e (K.connectedComponentMk q), q, by simp, rfl⟩
  have hn : 0 < n := by
    obtain ⟨x,hx,hxa⟩ := hnot
    obtain ⟨i,_⟩ := hfcov x hx hxa
    exact Nat.zero_lt_of_lt i.isLt
  have hfn (i : Fin n) : (F i).Nonempty := by
    let c := e.symm i
    exact ⟨c.out.val,c.out,c.out_eq,rfl⟩
  have hfs {i j : Fin n} {x y : V} (hij : i ≠ j) (hx : x ∈ F i) (hy : y ∈ F j) :
      x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    change K.connectedComponentMk a = e.symm i at ha
    change K.connectedComponentMk b = e.symm j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by
      rw [ha,hb]
      exact e.symm.injective.ne hij
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj (show K.Adj a b from he))⟩
  have hfk (i : Fin n) : (G.induce (F i)).Connected := by
    let c := e.symm i
    let f : c.supp → F i := fun x => ⟨x.val.val,x.val,x.property,rfl⟩
    have hf' : Function.Injective f := by
      intro a b he
      exact Subtype.ext (Subtype.ext (congrArg (fun x : F i => x.val) he))
    have hf'' : Function.Surjective f := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    let iso : K.induce c.supp ≃g G.induce (F i) :=
      ⟨Equiv.ofBijective f ⟨hf',hf''⟩, by intro a b; rfl⟩
    exact iso.connected_iff.mp c.maximal_connected_induce_supp.1
  obtain ⟨hfar,unique⟩ := rooted_far_component_structure v z A F (hvB z hz) houtA.1 hzA hA
    hvA hf hfcov (fun h hx hy => hfs h hx hy) hfk ht
  let N (i : Fin n) := {x | x ∈ A ∧ G.Adj v x ∧ ∃ y ∈ F i, G.Adj x y}
  let N₀ := {x | x ∈ A ∧ G.Adj v x ∧ ∀ i y, y ∈ F i → ¬ G.Adj x y}
  have hN (i : Fin n) : (N i).Nonempty := by
    obtain ⟨a,ha,hva,hall⟩ := (hfar i).2
    obtain ⟨x,hx⟩ := hfn i
    exact ⟨a,ha,hva,x,hx,hall x hx⟩
  have hsame (i : Fin n) (x y : V) (hx : x ∈ N i) (hy : y ∈ F i) : G.Adj x y :=
    rooted_attachment_all v z x (F i) (hvB z hz) hx.2.1 (hzA x hx.1)
      (fun a ha => ⟨fun h => houtA.1 (h ▸ (hf i a ha).1),hzA a (hf i a ha).1,(hf i a ha).2⟩)
      (hfk i) hx.2.2 ht y hy
  have hcross (i : Fin n) (a a' : V) (ha : a ∈ N i)
      (ha' : a' ∈ A ∧ G.Adj v a') (hn' : a' ∉ N i) : G.Adj a a' := by
    obtain ⟨x,hx,hax⟩ := ha.2.2
    have hax' : ¬ G.Adj x a' := fun h => hn' ⟨ha'.1,ha'.2,x,hx,h.symm⟩
    exact rooted_cross_attachment v z a a' x (hvB z hz) ha.2.1 ha'.2 (hzA a ha.1)
      (hzA a' ha'.1) (hzA x (hf i x hx).1) (fun h => houtA.1 (h ▸ (hf i x hx).1))
      (hf i x hx).2 (fun h => hn' (h ▸ ha)) hax
      ⟨fun h => (hf i x hx).2 (h ▸ ha'.2),hax'⟩ ht
  have hdis {i j : Fin n} {x : V} (hij : i ≠ j) (hx : x ∈ N i) : x ∉ N j := by
    intro hy
    obtain ⟨a,ha,hxa⟩ := hx.2.2
    obtain ⟨b,hb,hxb⟩ := hy.2.2
    exact hij (unique x hx.1 hx.2.1 ha hb hxa hxb)
  have hnod (i : Fin n) (x : V) (hx : x ∈ N₀) : x ∉ N i := by
    rintro ⟨_,_,y,hy,hxy⟩
    exact hx.2.2 i y hy hxy
  have hhook (i : Fin n) (a : V) (hs : N i = {a}) : ∃ x ∈ F i, G.Adj w x := by
    have ha : a ∈ N i := by simp [hs]
    have hza : z ≠ a := (hzA a ha.1).1
    obtain ⟨x,hx⟩ := hfn i
    by_contra hn
    have hG : (G.induce ({a} : Set V)ᶜ).Connected := by
      have h := connected_of_card_lt_vertexConnectivity (G := G) ({a} : Finset V)
        (by simpa using Nat.lt_of_lt_of_le (by decide : 1 < 2) hκ)
      rwa [coe_singleton] at h
    let U := ↥(({a} : Set V)ᶜ)
    let S : Finset U := univ.filter (fun y => y.val ∈ F i)
    have hxs : x ≠ a := fun h => (hf i x hx).2 (h ▸ ha.2.1)
    have hSn : S.Nonempty := ⟨⟨x,fun h => hxs (Set.mem_singleton_iff.mp h)⟩,
      mem_filter.mpr ⟨mem_univ _,hx⟩⟩
    have hSu : S ≠ univ := by
      intro he
      let q : U := ⟨z,fun h => hza (Set.mem_singleton_iff.mp h)⟩
      have hm : q ∈ S := he ▸ mem_univ _
      exact (hzA z (hf i z (mem_filter.mp hm).2).1).1 rfl
    obtain ⟨q,hq,p,hp,hqp⟩ := hG.exists_adj_finset_compl hSn hSu
    have hpf : p.val ∈ F i := (mem_filter.mp hp).2
    have hqf : q.val ∉ F i := fun h => hq (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hqa : q.val ≠ a := fun h => q.property (Set.mem_singleton_iff.mpr h)
    have hpq : G.Adj p.val q.val := (induce_adj.mp hqp).symm
    by_cases hqv : q.val = v
    · exact (hf i p.val hpf).2 (hqv ▸ hpq.symm)
    have hqw : q.val ≠ w := by
      intro he
      exact hn ⟨p.val,hpf,he ▸ hpq.symm⟩
    rcases hcover q.val hqv hqw with hqA | hqB
    · by_cases h : G.Adj v q.val
      · have hnq : q.val ∈ N i := ⟨hqA,h,p.val,hpf,hpq.symm⟩
        rw [hs] at hnq
        exact hqa (Set.mem_singleton_iff.mp hnq)
      · obtain ⟨j,hj⟩ := hfcov q.val hqA h
        have hij : i ≠ j := by intro he; subst j; exact hqf hj
        exact (hfs hij hpf hj).2 hpq
    · exact (hsep p.val (hf i p.val hpf).1 q.val hqB).2 hpq
  have hcount : {i | ∃ a, N i = {a}}.ncard ≤ 2 := by
    by_contra! h
    obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := (Set.two_lt_ncard_iff (s := {i | ∃ a, N i = {a}})).mp h
    have ex {i : Fin n} (hi : i ∈ ({i | ∃ a, N i = {a}} : Set (Fin n))) :
        ∃ p ∈ F i, G.Adj w p := by
      obtain ⟨a,ha⟩ := hi
      exact hhook i a ha
    obtain ⟨a,ha,hwa⟩ := ex hi
    obtain ⟨b,hb,hwb⟩ := ex hj
    obtain ⟨c,hc,hwc⟩ := ex hk
    exact independent_four_spokes w z a b c (hwB z hz) hwa hwb hwc
      (hzA _ (hf i a ha).1) (hzA _ (hf j b hb).1) (hzA _ (hf k c hc).1)
      (hfs hij ha hb) (hfs hik ha hc) (hfs hjk hb hc) ht
  refine ⟨n,hn,F,N,N₀,hfn,hN,fun i => (hfar i).1,hf,?_,?_,?_,?_,hnod,?_,
    hsame,?_,?_,?_,hhook,hcount⟩
  · exact fun i x h => ⟨h.1,h.2.1⟩
  · exact fun x h => ⟨h.1,h.2.1⟩
  · exact fun h hx hy => hfs h hx hy
  · exact fun h hx => hdis h hx
  · intro x hx
    by_cases hvx : G.Adj v x
    · by_cases hN : ∃ i, x ∈ N i
      · obtain ⟨i,hi⟩ := hN
        exact Or.inr ⟨i,Or.inr hi⟩
      · exact Or.inl ⟨hx,hvx,fun i y hy h => hN ⟨i,hx,hvx,y,hy,h⟩⟩
    · obtain ⟨i,hi⟩ := hfcov x hx hvx
      exact Or.inr ⟨i,Or.inl hi⟩
  · intro i j x y hne hx hy
    exact hcross i x y hx ⟨hy.1,hy.2.1⟩ (hdis hne.symm hy)
  · intro i x y hx hy
    exact (hcross i y x hy ⟨hx.1,hx.2.1⟩ (hnod i x hx)).symm
  · intro x y t hx hy ht' hvx hvy hvt hxy hxt hyt hnxy hnxt hnyt
    exact independent_four_spokes v z x y t (hvB z hz) hvx hvy hvt
      (hzA x hx) (hzA y hy) (hzA t ht') ⟨hxy,hnxy⟩ ⟨hxt,hnxt⟩ ⟨hyt,hnyt⟩ ht

#print axioms h1FarData

end Graph199
