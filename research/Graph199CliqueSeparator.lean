import Graph199Cut
import Graph199MinimumCut
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem tree_add_leaves (T S : Finset V) (v : V)
    (hT : (G.induce (↑T : Set V)).IsTree) (hv : v ∈ T)
    (hdis : Disjoint S T) (hi : G.IsIndepSet (S : Set V))
    (ha : ∀ x ∈ S, G.Adj x v)
    (hu : ∀ x ∈ S, ∀ y ∈ T, G.Adj x y → y = v) :
    (G.induce (↑(T ∪ S) : Set V)).IsTree := by
  induction S using Finset.induction_on with
  | empty => rwa [Finset.union_empty]
  | @insert a S hx ih =>
    have hST : Disjoint S T := hdis.mono_left (subset_insert _ _)
    have hSi : G.IsIndepSet (S : Set V) :=
      hi.mono (by simpa only [coe_insert] using Set.subset_insert a (S : Set V))
    have htree := ih hST hSi (fun x hx => ha x (mem_insert_of_mem hx))
      (fun x hx y hy => hu x (mem_insert_of_mem hx) y hy)
    have haT : a ∉ T := fun h => Finset.disjoint_left.mp hdis (mem_insert_self _ _) h
    have haU : a ∉ (T ∪ S) := by simp [hx, haT]
    have hvU : v ∈ T ∪ S := mem_union.mpr (Or.inl hv)
    have hxa := ha a (mem_insert_self _ _)
    have hnew := htree.induce_insert_of_unique_adj haU hvU hxa (by
      intro y hy he
      rcases mem_union.mp hy with hy | hy
      · exact hu _ (mem_insert_self _ _) _ hy he
      · exact (hi (mem_insert_self a S) (mem_insert_of_mem hy) he.ne he).elim)
    rwa [union_insert]

omit [Fintype V] [DecidableEq V] in
private theorem tree_singleton (v : V) :
    (G.induce (↑({v} : Finset V) : Set V)).IsTree := by
  rw [coe_singleton]
  let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
  let _ : Subsingleton ↥({v} : Set V) := ⟨fun x y => Subtype.ext
    ((Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm)⟩
  exact IsTree.of_subsingleton

/-- Append two disjoint independent leaf classes to a connecting induced
tree. Each class has a single possible neighbor in the core. -/
theorem leaf_sets_on_induced_tree (B S T : Finset V) (u v : V)
    (hB : (G.induce (B : Set V)).IsTree) (hu : u ∈ B) (hv : v ∈ B)
    (hSB : Disjoint S B) (hTB : Disjoint T B)
    (hSi : G.IsIndepSet (S : Set V)) (hTi : G.IsIndepSet (T : Set V))
    (hST : ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y)
    (hS : ∀ x ∈ S, G.Adj x u) (hT : ∀ y ∈ T, G.Adj y v)
    (hSu : ∀ x ∈ S, ∀ y ∈ B, G.Adj x y → y = u)
    (hTv : ∀ x ∈ T, ∀ y ∈ B, G.Adj x y → y = v) :
    B.card + S.card + T.card ≤ largestInducedTreeSize G := by
  have hBS := tree_add_leaves B S u hB hu hSB hSi hS hSu
  have hTBS : Disjoint T (B ∪ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases mem_union.mp hy with hb | hs
    · exact Finset.disjoint_left.mp hTB hx hb
    · exact (hST x hs x hx).1 rfl
  have hBST := tree_add_leaves (B ∪ S) T v hBS (mem_union.mpr (Or.inl hv))
    hTBS hTi hT (by
      intro x hx y hy hxy
      rcases mem_union.mp hy with hy | hy
      · exact hTv x hx y hy hxy
      · exact ((hST y hy x hx).2 hxy.symm).elim)
  have hb := card_le_largestInducedTreeSize hBST
  simpa only [card_union_of_disjoint hTBS.symm,card_union_of_disjoint hSB.symm] using hb

omit [Fintype V] in
/-- Two distinct nonadjacent vertices meeting the same connected set have
an induced connecting tree inside the set and those vertices. -/
theorem connector_tree_of_common_component (u v : V) (C : Set V)
    (hne : u ≠ v) (hno : ¬ G.Adj u v) (hc : (G.induce C).Connected)
    (huC : ∃ x ∈ C, G.Adj u x) (hvC : ∃ x ∈ C, G.Adj v x) :
    ∃ B : Finset V, 3 ≤ B.card ∧ u ∈ B ∧ v ∈ B ∧
      (∀ x ∈ B, x = u ∨ x = v ∨ x ∈ C) ∧ (G.induce (B : Set V)).IsTree := by
  classical
  obtain ⟨a,ha,hua⟩ := huC
  obtain ⟨b,hb,hvb⟩ := hvC
  let S := insert u (insert v C)
  let K := G.induce S
  let u' : S := ⟨u,by simp [S]⟩
  let v' : S := ⟨v,by simp [S]⟩
  let a' : S := ⟨a,by simp [S,ha]⟩
  let b' : S := ⟨b,by simp [S,hb]⟩
  let i : G.induce C →g K :=
    ⟨fun x => ⟨x.val, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ x.property)⟩,
      fun h => h⟩
  have haReach : K.Reachable a' b' := (hc ⟨a,ha⟩ ⟨b,hb⟩).map i
  have huAdj : K.Adj u' a' := hua
  have hvAdj : K.Adj v' b' := hvb
  have hr : K.Reachable u' v' := huAdj.reachable.trans (haReach.trans hvAdj.symm.reachable)
  obtain ⟨p,hp,hpLen⟩ := hr.exists_path_of_dist
  let B₀ := p.support.toFinset
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let B := B₀.map f
  have hdist0 : K.dist u' v' ≠ 0 :=
    fun he => hne (congrArg Subtype.val (hr.dist_eq_zero_iff.mp he))
  have hdist1 : K.dist u' v' ≠ 1 := fun he =>
    hno (show K.Adj u' v' from dist_eq_one_iff_adj.mp he)
  have hBc : B.card = K.dist u' v' + 1 := by
    dsimp [B,B₀]
    rw [card_map,List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support,hpLen]
  have hBu : u ∈ B := mem_map.mpr ⟨u',List.mem_toFinset.mpr p.start_mem_support,rfl⟩
  have hBv : v ∈ B := mem_map.mpr ⟨v',List.mem_toFinset.mpr p.end_mem_support,rfl⟩
  have hSet (x : V) (hx : x ∈ B) : x = u ∨ x = v ∨ x ∈ C := by
    obtain ⟨y,_,rfl⟩ := mem_map.mp hx
    have hy : y.val ∈ insert u (insert v C) := y.property
    rcases Set.mem_insert_iff.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_insert_iff.mp h)
  have htree : (K.induce (B₀ : Set S)).IsTree :=
    p.induce_support_isTree_of_length_eq_dist hpLen
  let g : ↥(B₀ : Set S) → ↥(B : Set V) := fun a => ⟨a.val.val,
    mem_map.mpr ⟨a.val,a.property,rfl⟩⟩
  have hgi : Function.Injective g := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥(B : Set V) => x.val) he))
  have hgs : Function.Surjective g := by
    intro a
    obtain ⟨x,hx,he⟩ := mem_map.mp a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let iso : K.induce (B₀ : Set S) ≃g G.induce (B : Set V) :=
    ⟨Equiv.ofBijective g ⟨hgi,hgs⟩,by intro x y; rfl⟩
  exact ⟨B,by omega,hBu,hBv,hSet,iso.isTree_iff.mp htree⟩

/-- An edge with two sets of private, independent neighbors induces a tree
on the two centers and all selected neighbors. -/
theorem double_star_bound (u v : V) (huv : G.Adj u v) (S T : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hST : ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y)
    (hs : ∀ x ∈ S, G.Adj u x ∧ ¬ G.Adj v x)
    (ht : ∀ y ∈ T, G.Adj v y ∧ ¬ G.Adj u y)
    (hSv : v ∉ S) (hTu : u ∉ T) :
    S.card + T.card + 2 ≤ largestInducedTreeSize G := by
  let B : Finset V := {u,v}
  have hB : (G.induce (↑B : Set V)).IsTree :=
    (tree_singleton v).induce_insert_of_unique_adj
      (by simpa using huv.ne) (mem_singleton_self v) huv (by simp)
  have hSB : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro x hx h
    simp only [B,mem_insert,mem_singleton] at h
    rcases h with rfl | rfl
    · exact (hs _ hx).1.ne rfl
    · exact hSv hx
  have hTB : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro y hy h
    simp only [B,mem_insert,mem_singleton] at h
    rcases h with rfl | rfl
    · exact hTu hy
    · exact (ht _ hy).1.ne rfl
  have hBS : (G.induce (↑(B ∪ S) : Set V)).IsTree :=
    tree_add_leaves B S u hB (by simp [B]) hSB hS (fun x hx => (hs x hx).1.symm) (by
      intro x hx y hy hxy
      simp only [B,mem_insert,mem_singleton] at hy
      rcases hy with rfl | rfl
      · rfl
      · exact ((hs x hx).2 hxy.symm).elim)
  have hTBS : Disjoint T (B ∪ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases mem_union.mp hy with hb | hs'
    · exact Finset.disjoint_left.mp hTB hx hb
    · exact (hST x hs' x hx).1 rfl
  have hBST : (G.induce (↑((B ∪ S) ∪ T) : Set V)).IsTree :=
    tree_add_leaves (B ∪ S) T v hBS (by simp [B]) hTBS hT (fun y hy => (ht y hy).1.symm) (by
      intro y hy x hx hey
      rcases mem_union.mp hx with hxb | hxs
      · simp only [B,mem_insert,mem_singleton] at hxb
        rcases hxb with rfl | rfl
        · exact ((ht y hy).2 hey.symm).elim
        · rfl
      · exact ((hST x hxs y hy).2 hey.symm).elim)
  have hcardB : B.card = 2 := by
    dsimp [B]
    rw [card_insert_of_notMem (show u ∉ ({v} : Finset V) from by simpa using huv.ne),
      card_singleton]
  have hb := card_le_largestInducedTreeSize hBST
  rw [card_union_of_disjoint hTBS.symm,card_union_of_disjoint hSB.symm,hcardB] at hb
  omega

open scoped Classical in
/-- Every component of the complement of a separator meets at least κ
separator vertices, provided another component is present. -/
theorem component_neighbour_count {I : Type*} [Nontrivial I]
    (U : Finset V) (C : I → Set V) (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (i : I) :
    vertexConnectivity G ≤ (U.filter fun u => ∃ x ∈ C i, G.Adj u x).card := by
  classical
  let N := U.filter fun u => ∃ x ∈ C i, G.Adj u x
  change vertexConnectivity G ≤ N.card
  by_contra! hN
  have hK := connected_of_card_lt_vertexConnectivity N hN
  let W := ↥((N : Set V)ᶜ)
  let S : Finset W := univ.filter fun x => x.val ∈ C i
  have hSn : S.Nonempty := by
    obtain ⟨x,hx⟩ := hn i
    have hxN : x ∉ N := fun h => hout i x hx (mem_filter.mp h).1
    exact ⟨⟨x,hxN⟩, mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  have hSu : S ≠ univ := by
    obtain ⟨j,hj⟩ := exists_ne i
    obtain ⟨y,hy⟩ := hn j
    have hyN : y ∉ N := fun h => hout j y hy (mem_filter.mp h).1
    let q : W := ⟨y,hyN⟩
    intro he
    have hm : q ∈ S := he ▸ mem_univ _
    exact (hsep hj.symm (mem_filter.mp hm).2 hy).1 rfl
  obtain ⟨y,hy,x,hx,hyx⟩ := hK.exists_adj_finset_compl hSn hSu
  have hxi : x.val ∈ C i := (mem_filter.mp hx).2
  have hyi : y.val ∉ C i := fun h => hy (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hadj : G.Adj y.val x.val := induce_adj.mp hyx
  by_cases hyU : y.val ∈ U
  · exact y.property (mem_filter.mpr ⟨hyU,x.val,hxi,hadj⟩)
  · obtain ⟨j,hyj⟩ := hcover y.val hyU
    have hne : i ≠ j := fun he => hyi (he ▸ hyj)
    exact (hsep hne hxi hyj).2 hadj.symm

omit [Fintype V] in
private theorem touching_representatives {I : Type*} (C : I → Set V) (J : Finset I)
    (u : V)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hmeet : ∀ i ∈ J, ∃ x ∈ C i, G.Adj u x) :
    ∃ B : Finset V, B.card = J.card ∧ G.IsIndepSet (B : Set V) ∧
      (∀ x ∈ B, ∃ i ∈ J, x ∈ C i) ∧ (∀ x ∈ B, G.Adj u x) := by
  classical
  have hex (i : J) : ∃ x ∈ C i.val, G.Adj u x := hmeet i.val i.property
  choose f hf hAdj using hex
  have hfi : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hn
    exact (hsep hn (hf i) (hf j)).1 he
  let B := J.attach.image f
  refine ⟨B,by simp [B,card_image_of_injective _ hfi],?_,?_,?_⟩
  · intro x hx y hy hne
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hy
    exact (hsep (fun h => hne (congrArg f (Subtype.ext h))) (hf i) (hf j)).2
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact ⟨i.val,i.property,hf i⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact hAdj i

/-- Separator incidence obeys a pairwise difference bound for each pair of distinct
centers that is adjacent or meets a common component. -/
theorem separator_incidence_partial {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I]
    (U : Finset V) (C : I → Set V)
    (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ R : U → Finset I,
      (∀ u i, i ∈ R u ↔ ∃ x ∈ C i, G.Adj u.val x) ∧
      (∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card) ∧
      (∀ u, (R u).card ≤ vertexConnectivity G + 1) ∧
      (∀ u v, u ≠ v →
        (G.Adj u.val v.val ∨ ∃ i, (G.induce (C i)).Connected ∧
          (∃ x ∈ C i, G.Adj u.val x) ∧ (∃ x ∈ C i, G.Adj v.val x)) →
        (((R u \ R v) ∪ (R v \ R u))).card ≤ vertexConnectivity G) := by
  classical
  let R (u : U) := univ.filter fun i => ∃ x ∈ C i, G.Adj u.val x
  have hR (u : U) (i : I) : i ∈ R u ↔ ∃ x ∈ C i, G.Adj u.val x := by simp [R]
  refine ⟨R,hR,?_,?_,?_⟩
  · intro i
    have h := component_neighbour_count U C hn hout hcover (fun he hx hy => hsep he hx hy) i
    let emb : U ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have he : (univ.filter fun u : U => i ∈ R u).map emb =
        U.filter (fun u => ∃ x ∈ C i, G.Adj u x) := by
      ext x
      constructor
      · intro hx
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
        exact mem_filter.mpr ⟨y.property,(hR y i).mp (mem_filter.mp hy).2⟩
      · intro hx
        obtain ⟨hxU,hxc⟩ := mem_filter.mp hx
        refine mem_map.mpr ⟨⟨x,hxU⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
        exact (hR _ i).mpr hxc
    rwa [← he,card_map] at h
  · intro u
    obtain ⟨B,hB,hBin,_,hBAdj⟩ := touching_representatives C (R u) u.val
      (fun he hx hy => hsep he hx hy) (fun i hi => (hR u i).mp hi)
    have hstar := star_bound u.val B hBin hBAdj
    omega
  · intro u v huv hcompat
    let Iu := R u \ R v
    let Iv := R v \ R u
    have hdis : Disjoint Iu Iv := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
    obtain ⟨S,hSc,hSi,hSF,hSa⟩ := touching_representatives C Iu u.val
      (fun he hx hy => hsep he hx hy) (fun i hi => (hR u i).mp (mem_sdiff.mp hi).1)
    obtain ⟨T,hTc,hTi,hTF,hTa⟩ := touching_representatives C Iv v.val
      (fun he hx hy => hsep he hx hy) (fun i hi => (hR v i).mp (mem_sdiff.mp hi).1)
    have hST (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) : x ≠ y ∧ ¬ G.Adj x y := by
      obtain ⟨i,hi,hxc⟩ := hSF x hx
      obtain ⟨j,hj,hyc⟩ := hTF y hy
      have hne : i ≠ j := fun he => Finset.disjoint_left.mp hdis (he ▸ hi) hj
      exact hsep hne hxc hyc
    have hS (x : V) (hx : x ∈ S) : G.Adj u.val x ∧ ¬ G.Adj v.val x := by
      refine ⟨hSa x hx,?_⟩
      obtain ⟨i,hi,hxc⟩ := hSF x hx
      exact fun he => (mem_sdiff.mp hi).2 ((hR v i).mpr ⟨x,hxc,he⟩)
    have hT (x : V) (hx : x ∈ T) : G.Adj v.val x ∧ ¬ G.Adj u.val x := by
      refine ⟨hTa x hx,?_⟩
      obtain ⟨i,hi,hxc⟩ := hTF x hx
      exact fun he => (mem_sdiff.mp hi).2 ((hR u i).mpr ⟨x,hxc,he⟩)
    have hSv : v.val ∉ S := by
      intro hx
      obtain ⟨i,_,hxc⟩ := hSF _ hx
      exact hout i _ hxc v.property
    have hTu : u.val ∉ T := by
      intro hx
      obtain ⟨i,_,hxc⟩ := hTF _ hx
      exact hout i _ hxc u.property
    have htree : S.card + T.card + 2 ≤ largestInducedTreeSize G := by
      by_cases hAdj : G.Adj u.val v.val
      · exact double_star_bound u.val v.val hAdj S T hSi hTi hST hS hT hSv hTu
      obtain ⟨i,hCi,huI,hvI⟩ := hcompat.resolve_left hAdj
      have hune : u.val ≠ v.val := fun he => huv (Subtype.ext he)
      obtain ⟨B,hBc,hBu,hBv,hBC,hBtree⟩ :=
        connector_tree_of_common_component u.val v.val (C i) hune hAdj hCi huI hvI
      have leftFar (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ C i) :
          x ≠ y ∧ ¬ G.Adj x y := by
        obtain ⟨j,hj,hxC⟩ := hSF x hx
        have hji : j ≠ i := fun he => (mem_sdiff.mp hj).2 (he.symm ▸ (hR v i).mpr hvI)
        exact hsep hji hxC hy
      have rightFar (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ C i) :
          x ≠ y ∧ ¬ G.Adj x y := by
        obtain ⟨j,hj,hxC⟩ := hTF x hx
        have hji : j ≠ i := fun he => (mem_sdiff.mp hj).2 (he.symm ▸ (hR u i).mpr huI)
        exact hsep hji hxC hy
      have hSB : Disjoint S B := by
        apply Finset.disjoint_left.mpr
        intro x hx hb
        rcases hBC x hb with he | he | he
        · exact (hSa x hx).ne he.symm
        · exact hSv (he ▸ hx)
        · exact (leftFar x hx x he).1 rfl
      have hTB : Disjoint T B := by
        apply Finset.disjoint_left.mpr
        intro x hx hb
        rcases hBC x hb with he | he | he
        · exact hTu (he ▸ hx)
        · exact (hTa x hx).ne he.symm
        · exact (rightFar x hx x he).1 rfl
      have hSu (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ B) (he : G.Adj x y) :
          y = u.val := by
        rcases hBC y hy with hu | hv | hc
        · exact hu
        · exact ((hS x hx).2 (hv ▸ he.symm)).elim
        · exact ((leftFar x hx y hc).2 he).elim
      have hTv (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ B) (he : G.Adj x y) :
          y = v.val := by
        rcases hBC y hy with hu | hv | hc
        · exact ((hT x hx).2 (hu ▸ he.symm)).elim
        · exact hv
        · exact ((rightFar x hx y hc).2 he).elim
      have hh := leaf_sets_on_induced_tree B S T u.val v.val hBtree hBu hBv hSB hTB
        hSi hTi hST (fun x hx => (hSa x hx).symm) (fun x hx => (hTa x hx).symm) hSu hTv
      omega
    change (Iu ∪ Iv).card ≤ _
    rw [card_union_of_disjoint hdis,← hSc,← hTc]
    omega

/-- Separator incidence obeys the clique-style difference bound whenever every
pair of distinct separator vertices is adjacent or meets a common component. -/
theorem separator_incidence_of_common_component {I : Type*} [Fintype I] [DecidableEq I]
    [Nontrivial I] (U : Finset V) (C : I → Set V) (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hcompat : ∀ u v : U, u ≠ v →
      G.Adj u.val v.val ∨ ∃ i, (G.induce (C i)).Connected ∧
        (∃ x ∈ C i, G.Adj u.val x) ∧ (∃ x ∈ C i, G.Adj v.val x))
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ R : U → Finset I,
      (∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card) ∧
      (∀ u, (R u).card ≤ vertexConnectivity G + 1) ∧
      (∀ u v, u ≠ v → (((R u \ R v) ∪ (R v \ R u))).card ≤ vertexConnectivity G) := by
  obtain ⟨R,_,hc,hr,hd⟩ := separator_incidence_partial U C hn hout hcover
    (fun h hx hy => hsep h hx hy) ht
  exact ⟨R,hc,hr,fun u v h => hd u v h (hcompat u v h)⟩

/-- Every clique separator satisfies the pairwise compatibility hypothesis. -/
theorem clique_separator_incidence {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I]
    (U : Finset V) (hU : G.IsClique (U : Set V)) (C : I → Set V)
    (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ R : U → Finset I,
      (∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card) ∧
      (∀ u, (R u).card ≤ vertexConnectivity G + 1) ∧
      (∀ u v, u ≠ v → (((R u \ R v) ∪ (R v \ R u))).card ≤ vertexConnectivity G) :=
  separator_incidence_of_common_component U C hn hout hcover (fun he hx hy => hsep he hx hy)
    (fun u v h => Or.inl (hU u.property v.property (fun he => h (Subtype.ext he)))) ht

#print axioms separator_incidence_partial
#print axioms separator_incidence_of_common_component
#print axioms component_neighbour_count
#print axioms clique_separator_incidence
#print axioms double_star_bound
#print axioms connector_tree_of_common_component
#print axioms leaf_sets_on_induced_tree
end Graph199
