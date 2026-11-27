import Graph199Cut
import Graph199MinimumCut

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A star and an induced two-edge arm can be combined when the arm has no edges to the spokes. -/
theorem arm_star_bound (v a b : V) (S : Finset V)
    (hind : (S : Set V).Pairwise (fun x y => ¬ G.Adj x y))
    (hadj : ∀ x ∈ S, G.Adj v x) (hva : G.Adj v a) (hab : G.Adj a b)
    (hvb : ¬ G.Adj v b) (hbv : b ≠ v) (ha : a ∉ S) (hb : b ∉ S)
    (hba : ∀ x ∈ S, ¬ G.Adj b x) (haa : ∀ x ∈ S, ¬ G.Adj a x) :
    S.card + 3 ≤ largestInducedTreeSize G := by
  have hv : v ∉ S := fun h => (hadj v h).ne rfl
  have htree : (G.induce (↑(insert v S) : Set V)).IsTree := by
    induction S using Finset.induction_on with
    | empty =>
      have hs : (↑(insert v (∅ : Finset V)) : Set V) = {v} := by ext x; simp
      rw [hs]
      let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
      let _ : Subsingleton ↥({v} : Set V) := ⟨fun x y => Subtype.ext
        ((Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm)⟩
      exact IsTree.of_subsingleton
    | @insert x S hx ih =>
      have hvx := hadj x (mem_insert_self x S)
      have hi : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b) :=
        hind.mono (by simpa only [coe_insert] using Set.subset_insert x (S : Set V))
      have hind' := ih hi (fun y hy => hadj y (mem_insert_of_mem hy))
        (fun hy => ha (mem_insert_of_mem hy)) (fun hy => hb (mem_insert_of_mem hy))
        (fun y hy => hba y (mem_insert_of_mem hy)) (fun y hy => haa y (mem_insert_of_mem hy))
        (fun hy => hv (mem_insert_of_mem hy))
      rw [insert_comm]
      apply hind'.induce_insert_of_unique_adj (by simp [hx, hvx.ne.symm])
        (mem_insert_self v S) hvx.symm
      intro y hy hxy
      rcases mem_insert.mp hy with rfl | hy
      · rfl
      exact (hind (mem_insert_self x S) (mem_insert_of_mem hy) hxy.ne hxy).elim
  have hamem : a ∉ insert v S := by simp [hva.ne.symm, ha]
  have htree' := htree.induce_insert_of_unique_adj hamem (mem_insert_self v S) hva.symm (by
    intro x hx hax
    rcases mem_insert.mp hx with rfl | hx
    · rfl
    · exact (haa x hx hax).elim)
  have hbmem : b ∉ insert a (insert v S) := by simp [hab.ne.symm, hbv, hb]
  have htree'' := htree'.induce_insert_of_unique_adj hbmem (mem_insert_self a (insert v S))
    hab.symm (by
      intro x hx hbx
      rcases mem_insert.mp hx with rfl | hx
      · rfl
      rcases mem_insert.mp hx with rfl | hx
      · exact (hvb hbx.symm).elim
      · exact (hba x hx hbx).elim)
  have h := card_le_largestInducedTreeSize htree''
  rw [card_insert_of_notMem hbmem, card_insert_of_notMem hamem,
    card_insert_of_notMem hv] at h
  omega


/-- When the induced-tree bound is tight for a separator and its components, every
separator vertex meeting all components is adjacent to every vertex in them.
The same bound forces each component to be a clique. -/
theorem tight_cut_component_structure {I : Type*} [Fintype I] [DecidableEq I]
    (v : V) (C : I → Set V)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hout : ∀ i, v ∉ C i)
    (hconn : ∀ i, (G.induce (C i)).Connected)
    (hmeet : ∀ i, ∃ x ∈ C i, G.Adj v x)
    (ht : largestInducedTreeSize G ≤ Fintype.card I + 1) :
    (∀ i x, x ∈ C i → G.Adj v x) ∧
      (∀ i x y, x ∈ C i → y ∈ C i → x ≠ y → G.Adj x y) := by
  classical
  choose f hf hadjf using hmeet
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hn
    exact (hsep hn (hf i) (hf j)).1 he
  have sides (i : I) : ∃ S : Finset V,
      S.card = Fintype.card I - 1 ∧
      (∀ x ∈ S, ∃ j ≠ i, x ∈ C j) ∧
      (S : Set V).Pairwise (fun x y => ¬ G.Adj x y) ∧
      (∀ x ∈ S, G.Adj v x) := by
    let T := (univ : Finset I).erase i
    refine ⟨T.image f, ?_, ?_, ?_, ?_⟩
    · simp [T, card_image_of_injective _ hinj]
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      exact ⟨j, (mem_erase.mp hj).1, hf j⟩
    · intro x hx y hy hxy
      obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      obtain ⟨l, _, rfl⟩ := mem_image.mp hy
      exact (hsep (fun h => hxy (congrArg f h)) (hf j) (hf l)).2
    · intro x hx
      obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      exact hadjf j
  have hcomplete (i : I) (x : V) (hx : x ∈ C i) : G.Adj v x := by
    by_contra hnx
    let T : Finset (C i) := univ.filter (fun a => G.Adj v a.val)
    have hT : T.Nonempty := ⟨⟨f i, hf i⟩, by simp [T, hadjf]⟩
    have hTu : T ≠ univ := by
      intro he
      have h : (⟨x, hx⟩ : C i) ∈ T := he ▸ mem_univ _
      exact hnx (mem_filter.mp h).2
    obtain ⟨b, hb, a, ha, hba⟩ := (hconn i).exists_adj_finset_compl hT hTu
    have hva : G.Adj v a.val := (mem_filter.mp ha).2
    have hvb : ¬ G.Adj v b.val := fun h => hb (mem_filter.mpr ⟨mem_univ _, h⟩)
    obtain ⟨S, hSc, hsides, hind, hadjS⟩ := sides i
    have hsep' (y : V) (hy : y ∈ C i) (z : V) (hz : z ∈ S) :
        y ≠ z ∧ ¬ G.Adj y z := by
      obtain ⟨j, hj, hzc⟩ := hsides z hz
      exact hsep hj.symm hy hzc
    have h := arm_star_bound v a.val b.val S hind hadjS hva
      (induce_adj.mp hba).symm hvb
      (fun he => hout i (he ▸ b.property))
      (fun haS => (hsep' _ a.property _ haS).1 rfl)
      (fun hbS => (hsep' _ b.property _ hbS).1 rfl)
      (fun z hz => (hsep' _ b.property z hz).2)
      (fun z hz => (hsep' _ a.property z hz).2)
    let _ : Nonempty I := ⟨i⟩
    have hi : 0 < Fintype.card I := Fintype.card_pos
    omega
  refine ⟨hcomplete, ?_⟩
  intro i x y hx hy hxy
  by_contra hn
  obtain ⟨S, hSc, hsides, hind, hadjS⟩ := sides i
  have cross (a : V) (ha : a ∈ C i) (z : V) (hz : z ∈ S) :
      a ≠ z ∧ ¬ G.Adj a z := by
    obtain ⟨j, hj, hzc⟩ := hsides z hz
    exact hsep hj.symm ha hzc
  have hxS : x ∉ S := fun h => (cross x hx x h).1 rfl
  have hyS : y ∉ S := fun h => (cross y hy y h).1 rfl
  have hi' : (↑(insert y S) : Set V).Pairwise (fun a b => ¬ G.Adj a b) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem hyS hind
    intro z hz
    exact ⟨(cross y hy z hz).2, fun he => (cross y hy z hz).2 he.symm⟩
  have hxSy : x ∉ insert y S := by simp [hxy, hxS]
  have hi'' : (↑(insert x (insert y S)) : Set V).Pairwise (fun a b => ¬ G.Adj a b) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem hxSy hi'
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ⟨hn, fun he => hn he.symm⟩
    · exact ⟨(cross x hx z hz).2, fun he => (cross x hx z hz).2 he.symm⟩
  have h := star_bound v (insert x (insert y S)) hi'' (by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hcomplete i _ hx
    rcases mem_insert.mp hz with rfl | hz
    · exact hcomplete i _ hy
    · exact hadjS z hz)
  rw [card_insert_of_notMem hxSy, card_insert_of_notMem hyS] at h
  let _ : Nonempty I := ⟨i⟩
  have hi : 0 < Fintype.card I := Fintype.card_pos
  omega


/-- In a decomposition by a two-vertex cut, deleting only the other cut vertex
forces the remaining cut vertex to meet every component. -/
private theorem two_cut_neighbours (u v : V) (huv : u ≠ v) (C : Fin 3 → Set V)
    (hout : ∀ i, u ∉ C i ∧ v ∉ C i)
    (hcover : ∀ x, x ≠ u → x ≠ v → ∃ i, x ∈ C i)
    (hsep : ∀ {i j : Fin 3} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → ¬ G.Adj x y)
    (hc : ∀ i, (G.induce (C i)).Connected)
    (hG : (G.induce ({v} : Set V)ᶜ).Connected) (i : Fin 3) :
    ∃ x ∈ C i, G.Adj u x := by
  classical
  let W := ↥(({v} : Set V)ᶜ)
  let S : Finset W := univ.filter fun x => x.val ∈ C i
  have hS : S.Nonempty := by
    obtain ⟨x⟩ := (hc i).nonempty
    exact ⟨⟨x.val, fun he => (hout i).2 ((Set.mem_singleton_iff.mp he).symm ▸ x.property)⟩,
      mem_filter.mpr ⟨mem_univ _, x.property⟩⟩
  have hSu : S ≠ univ := by
    intro he
    let a : W := ⟨u, fun h => huv (Set.mem_singleton_iff.mp h)⟩
    have h : a ∈ S := he ▸ mem_univ a
    exact (hout i).1 (mem_filter.mp h).2
  obtain ⟨b, hb, a, ha, hba⟩ := hG.exists_adj_finset_compl hS hSu
  have hai : a.val ∈ C i := (mem_filter.mp ha).2
  have hbi : b.val ∉ C i := fun h => hb (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hbu : b.val = u := by
    by_contra hne
    obtain ⟨j, hj⟩ := hcover b.val hne (fun he => b.property (Set.mem_singleton_iff.mpr he))
    have hij : i ≠ j := by
      intro he
      subst j
      exact hbi hj
    exact hsep hij hai hj (induce_adj.mp hba).symm
  exact ⟨a.val, hai, hbu ▸ induce_adj.mp hba⟩

/-- The three-component case for a two-vertex cut in Written on the Wall II #199. -/
theorem hamiltonian_of_three_components (u v : V) (huv : u ≠ v) (C : Fin 3 → Set V)
    (hout : ∀ i, u ∉ C i ∧ v ∉ C i)
    (hcover : ∀ x, x ≠ u → x ≠ v → ∃ i, x ∈ C i)
    (hsep : ∀ {i j : Fin 3} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hc : ∀ i, (G.induce (C i)).Connected)
    (hGu : (G.induce ({u} : Set V)ᶜ).Connected)
    (hGv : (G.induce ({v} : Set V)ᶜ).Connected)
    (ht : largestInducedTreeSize G ≤ 4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have hbt : largestInducedTreeSize G ≤ Fintype.card (Fin 3) + 1 := by simpa using ht
  have ⟨hu, hclique⟩ := tight_cut_component_structure u C (@hsep)
    (fun i => (hout i).1) hc
    (two_cut_neighbours u v huv C hout hcover (fun h a b => (hsep h a b).2) hc hGv) hbt
  have ⟨hv, _⟩ := tight_cut_component_structure v C (@hsep)
    (fun i => (hout i).2) hc
    (two_cut_neighbours v u huv.symm C (fun i => (hout i).symm)
      (fun x hx hy => hcover x hy hx) (fun h a b => (hsep h a b).2) hc hGu) hbt
  let B (i : Fin 3) := (univ.filter (· ∈ C i)).toList
  have hmem (i : Fin 3) (x : V) : x ∈ B i ↔ x ∈ C i := by simp [B]
  have hnd (i : Fin 3) : (B i).Nodup := nodup_toList _
  have hchain (i : Fin 3) : (B i).IsChain G.Adj := by
    apply List.Pairwise.isChain
    apply List.pairwise_iff_get.mpr
    intro a b hab
    exact hclique i _ _ ((hmem i _).mp (List.get_mem _ _)) ((hmem i _).mp (List.get_mem _ _))
      (List.pairwise_iff_get.mp (hnd i) a b hab)
  have cons_chain (i : Fin 3) (x : V) (hz : ∀ z ∈ C i, G.Adj x z)
      (p : List V) (hp : (B i ++ p).IsChain G.Adj)
      (hp' : B i ≠ []) : (x :: (B i ++ p)).IsChain G.Adj := by
    apply hp.cons
    intro z hz'
    rw [List.head?_append_of_ne_nil _ hp'] at hz'
    exact hz z ((hmem i z).mp (List.mem_of_mem_head? hz'))
  have hnon (i : Fin 3) : B i ≠ [] := by
    obtain ⟨x⟩ := (hc i).nonempty
    exact List.ne_nil_of_mem ((hmem i x.val).mpr x.property)
  let L := B 0 ++ u :: (B 1 ++ v :: B 2)
  have hL : L.IsChain G.Adj := by
    apply (hchain 0).append
    · apply cons_chain 1 u (hu 1)
      · apply (hchain 1).append
        · exact (hchain 2).cons (fun z hz => hv 2 z ((hmem 2 z).mp (List.mem_of_mem_head? hz)))
        · intro x hx y hy
          have hy' : v = y := by simpa using hy
          exact hy' ▸ (hv 1 x ((hmem 1 x).mp (List.mem_of_mem_getLast? hx))).symm
      · exact hnon 1
    · intro x hx y hy
      have hy' : u = y := by simpa using hy
      exact hy' ▸ (hu 0 x ((hmem 0 x).mp (List.mem_of_mem_getLast? hx))).symm
  have hcsep (i j : Fin 3) (hij : i ≠ j) (x : V) (hx : x ∈ B i) : x ∉ B j :=
    fun hy => (hsep hij ((hmem i x).mp hx) ((hmem j x).mp hy)).1 rfl
  have hua (i : Fin 3) : u ∉ B i := fun hu => (hout i).1 ((hmem i u).mp hu)
  have hva (i : Fin 3) : v ∉ B i := fun hv => (hout i).2 ((hmem i v).mp hv)
  have hndL : L.Nodup := by
    simp only [L, List.nodup_append', List.nodup_cons, List.mem_append, List.mem_cons]
    refine ⟨hnd 0, ⟨?_, hnd 1, ⟨hva 2, hnd 2⟩, ?_⟩, ?_⟩
    · push Not
      exact ⟨hua 1, huv, hua 2⟩
    · intro x hx hxc
      rcases List.mem_cons.mp hxc with rfl | hxc
      · exact hva 1 hx
      · exact hcsep 1 2 (by decide) x hx hxc
    · intro x hx hxc
      rcases List.mem_cons.mp hxc with rfl | hxc
      · exact hua 0 hx
      · rcases List.mem_append.mp hxc with hxc | hxc
        · exact hcsep 0 1 (by decide) x hx hxc
        · rcases List.mem_cons.mp hxc with rfl | hxc
          · exact hva 0 hx
          · exact hcsep 0 2 (by decide) x hx hxc
  have hmemL (x : V) : x ∈ L := by
    by_cases hxu : x = u
    · simp [L, hxu]
    by_cases hxv : x = v
    · simp [L, hxv]
    obtain ⟨i, hi⟩ := hcover x hxu hxv
    have hm := (hmem i x).mpr hi
    fin_cases i
    · exact List.mem_append_left _ (show x ∈ B 0 from hm)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (show x ∈ B 1 from hm)))
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ (show x ∈ B 2 from hm))))
  have hnL : L ≠ [] := List.ne_nil_of_mem (hmemL u)
  let p := Walk.ofSupport L hnL hL
  have hs : p.support = L := Walk.support_ofSupport hnL hL
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hs]
  exact ⟨_, _, p, hp.isHamiltonian_of_mem (fun z => by rw [hs]; exact hmemL z)⟩

/-- Conjecture 199 for graphs of vertex connectivity two with a two-vertex cut
whose deletion leaves exactly three connected components. -/
theorem conjecture199_connectivity_two_three_components (u v : V) (huv : u ≠ v)
    (hκ : vertexConnectivity G = 2)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (C : Fin 3 → Set V)
    (hout : ∀ i, u ∉ C i ∧ v ∉ C i)
    (hcover : ∀ x, x ≠ u → x ≠ v → ∃ i, x ∈ C i)
    (hsep : ∀ {i j : Fin 3} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hc : ∀ i, (G.induce (C i)).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have delete_one (w : V) : (G.induce ({w} : Set V)ᶜ).Connected := by
    have h := connected_of_card_lt_vertexConnectivity (G := G) ({w} : Finset V)
      (by simp [hκ])
    rwa [coe_singleton] at h
  exact hamiltonian_of_three_components u v huv C hout hcover (@hsep) hc
    (delete_one u) (delete_one v) (by omega)

/-- Under the catalog hypothesis, a minimum cut leaves at most one more component
than its own size. This is the component-count condition for that cut. -/
theorem min_cut_component_count {I : Type*} [Fintype I]
    (S : Finset V) (v : V) (hv : v ∈ S) (hS : S.card = vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (C : I → Set V) (hne : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ S)
    (hcover : ∀ x ∉ S, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y) :
    Fintype.card I ≤ S.card + 1 := by
  classical
  by_contra hn
  have hi : 1 < Fintype.card I := by omega
  let _ : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hi
  have hadj (i : I) : ∃ x ∈ C i, G.Adj v x := by
    obtain ⟨x, hx⟩ := hne i
    obtain ⟨j, hj⟩ := exists_ne i
    obtain ⟨y, hy⟩ := hne j
    have hyi : y ∉ C i := fun he => (hsep hj.symm he hy).1 rfl
    obtain ⟨z, hz, _, hzv⟩ := minCut_adj_side S v hv hS.le (C i)
      ⟨x, hx, hout i x hx⟩ ⟨y, hyi, hout j y hy⟩ (by
        intro a ha b hb _ hbS
        obtain ⟨k, hk⟩ := hcover b hbS
        have hik : i ≠ k := by
          intro he
          subst k
          exact hb hk
        exact (hsep hik ha hk).2)
    exact ⟨z, hz, hzv⟩
  choose f hf hfadj using hadj
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hne
    exact (hsep hne (hf i) (hf j)).1 he
  let B := univ.image f
  have hind : (B : Set V).Pairwise (fun x y => ¬ G.Adj x y) := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    exact (hsep (fun he => hxy (congrArg f he)) (hf i) (hf j)).2
  have h := star_bound v B hind (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact hfadj i)
  have hc : B.card = Fintype.card I := by simp [B, card_image_of_injective _ hinj]
  omega

#print axioms min_cut_component_count
#print axioms conjecture199_connectivity_two_three_components
#print axioms arm_star_bound
#print axioms tight_cut_component_structure
#print axioms hamiltonian_of_three_components
end Graph199
