import Graph199CutBranches
import Graph199Independent

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem singleton_induced_tree (v : V) :
    (G.induce (↑({v} : Finset V) : Set V)).IsTree := by
  rw [coe_singleton]
  let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
  let _ : Subsingleton ↥({v} : Set V) := ⟨fun x y => Subtype.ext
    ((Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm)⟩
  exact IsTree.of_subsingleton

/-- Two induced arms in different components joined at the same cut vertex
force a five-vertex induced tree. -/
theorem two_arms_bound (v a b c d : V)
    (hva : G.Adj v a) (hab : G.Adj a b) (hvb : ¬ G.Adj v b)
    (hvc : G.Adj v c) (hcd : G.Adj c d) (hvd : ¬ G.Adj v d)
    (hbv : b ≠ v) (hdv : d ≠ v)
    (hac : a ≠ c ∧ ¬ G.Adj a c) (had : a ≠ d ∧ ¬ G.Adj a d)
    (hbc : b ≠ c ∧ ¬ G.Adj b c) (hbd : b ≠ d ∧ ¬ G.Adj b d) :
    5 ≤ largestInducedTreeSize G := by
  have hA : a ∉ ({v} : Finset V) := by simp [hva.ne.symm]
  have hT := (singleton_induced_tree (G := G) v).induce_insert_of_unique_adj
    hA (mem_singleton_self v) hva.symm (by simp)
  have hB : b ∉ ({a,v} : Finset V) := by simp [hab.ne.symm, hbv]
  have hT' := hT.induce_insert_of_unique_adj hB (mem_insert_self a {v}) hab.symm (by
    intro x hx h
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · exact (hvb h.symm).elim)
  have hC : c ∉ ({b,a,v} : Finset V) := by simp [hbc.1.symm, hac.1.symm, hvc.ne.symm]
  have hT'' := hT'.induce_insert_of_unique_adj hC (by simp : v ∈ ({b,a,v} : Finset V))
    hvc.symm (by
      intro x hx h
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (hbc.2 h.symm).elim
      · exact (hac.2 h.symm).elim
      · rfl)
  have hD : d ∉ ({c,b,a,v} : Finset V) := by simp [hcd.ne.symm, hbd.1.symm, had.1.symm, hdv]
  have hT''' := hT''.induce_insert_of_unique_adj hD (mem_insert_self c {b,a,v}) hcd.symm (by
    intro x hx h
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rfl
    · exact (hbd.2 h.symm).elim
    · exact (had.2 h.symm).elim
    · exact (hvd h.symm).elim)
  simpa only [card_insert_of_notMem hD, card_insert_of_notMem hC, card_insert_of_notMem hB,
    card_insert_of_notMem hA, card_singleton] using card_le_largestInducedTreeSize hT'''

private theorem arm_in_component (v : V) (A : Set V) (hA : (G.induce A).Connected)
    (hadj : ∃ x ∈ A, G.Adj v x) (hnadj : ∃ y ∈ A, ¬ G.Adj v y) :
    ∃ a ∈ A, ∃ b ∈ A, G.Adj v a ∧ G.Adj a b ∧ ¬ G.Adj v b := by
  classical
  let S : Finset A := univ.filter (fun x => G.Adj v x.val)
  have hS : S.Nonempty := by
    obtain ⟨x, hx, h⟩ := hadj
    exact ⟨⟨x,hx⟩, mem_filter.mpr ⟨mem_univ _,h⟩⟩
  have hSu : S ≠ univ := by
    obtain ⟨y, hy, h⟩ := hnadj
    intro he
    have ht : (⟨y,hy⟩ : A) ∈ S := he ▸ mem_univ _
    exact h (mem_filter.mp ht).2
  obtain ⟨b, hb, a, ha, hab⟩ := hA.exists_adj_finset_compl hS hSu
  exact ⟨a.val, a.property, b.val, b.property, (mem_filter.mp ha).2, (induce_adj.mp hab).symm,
    fun h => hb (mem_filter.mpr ⟨mem_univ _, h⟩)⟩

/-- A cut vertex meeting two separated connected sides is complete to at least one
side when the graph has no induced tree on five vertices. -/
theorem cut_universal_one_side (v : V) (A B : Set V)
    (houtA : v ∉ A) (houtB : v ∉ B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (ha : ∃ a ∈ A, G.Adj v a) (hb : ∃ b ∈ B, G.Adj v b)
    (ht : largestInducedTreeSize G ≤ 4) :
    (∀ a ∈ A, G.Adj v a) ∨ (∀ b ∈ B, G.Adj v b) := by
  by_contra! hn
  obtain ⟨a, ha', b, hb', hva, hab, hvb⟩ := arm_in_component v A hA ha hn.1
  obtain ⟨c, hc, d, hd, hvc, hcd, hvd⟩ := arm_in_component v B hB hb hn.2
  have h := two_arms_bound v a b c d hva hab hvb hvc hcd hvd
    (fun h => houtA (h ▸ hb')) (fun h => houtB (h ▸ hd))
    (hs a ha' c hc) (hs a ha' d hd) (hs b hb' c hc) (hs b hb' d hd)
  omega

/-- If a separator vertex is complete to one nonclique side, it must also
be complete to the other connected side. -/
theorem cut_universal_other_side (v : V) (A B : Set V)
    (houtB : v ∉ B) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (ha : ∀ a ∈ A, G.Adj v a) (hb : ∃ b ∈ B, G.Adj v b)
    (hnA : ¬ G.IsClique A) (ht : largestInducedTreeSize G ≤ 4) :
    ∀ b ∈ B, G.Adj v b := by
  intro x hx
  by_contra hnx
  have he : ∃ a b : A, a ≠ b ∧ ¬ G.Adj a.val b.val := by
    by_contra! h
    apply hnA
    intro a ha b hb hne
    exact h ⟨a,ha⟩ ⟨b,hb⟩ (fun hh => hne (congrArg Subtype.val hh))
  obtain ⟨a, b, hab, hnab⟩ := he
  obtain ⟨c, hc, d, hd, hvc, hcd, hvd⟩ := arm_in_component v B hB hb ⟨x,hx,hnx⟩
  let S : Finset V := {a.val,b.val}
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hS : S.card = 2 := by
    dsimp [S]
    rw [card_insert_of_notMem (show a.val ∉ ({b.val} : Finset V) from by simpa using hab'),
      card_singleton]
  have hinside : ∀ z ∈ S, z ∈ A := by
    intro z hz
    simp only [S, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact a.property
    · exact b.property
  have hind : (S : Set V).Pairwise (fun x y => ¬ G.Adj x y) := by
    intro x hx y hy hne
    simp only [S, mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hne rfl).elim
    · exact hnab
    · exact fun h => hnab h.symm
    · exact (hne rfl).elim
  have h := arm_star_bound v c d S hind (fun z hz => ha z (hinside z hz)) hvc hcd hvd
    (fun h => houtB (h ▸ hd))
    (fun h => (hs c (hinside c h) c hc).1 rfl)
    (fun h => (hs d (hinside d h) d hd).1 rfl)
    (fun z hz h => (hs z (hinside z hz) d hd).2 h.symm)
    (fun z hz h => (hs z (hinside z hz) c hc).2 h.symm)
  omega


private theorem spanning_list_of_universal_side (v : V) (A B : Set V)
    (hA : (G.induce A).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hu : ∀ a ∈ A, G.Adj v a) (hB : ∃ b ∈ B, G.Adj v b)
    (ht : largestInducedTreeSize G ≤ 4) :
    ∃ l : List V, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj ∧ ∀ x, x ∈ l ↔ x ∈ A := by
  classical
  obtain ⟨b, hb, hvb⟩ := hB
  have hno (a c d : A) (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
      (hnac : ¬ (G.induce A).Adj a c) (hnad : ¬ (G.induce A).Adj a d)
      (hncd : ¬ (G.induce A).Adj c d) : False := by
    have hna := (hs a.val a.property b hb)
    have hnc := (hs c.val c.property b hb)
    have hnd := (hs d.val d.property b hb)
    have hac' : a.val ≠ c.val := fun e => hac (Subtype.ext e)
    have had' : a.val ≠ d.val := fun e => had (Subtype.ext e)
    have hcd' : c.val ≠ d.val := fun e => hcd (Subtype.ext e)
    have hind : (↑({a.val,c.val,d.val,b} : Finset V) : Set V).Pairwise (fun x y => ¬ G.Adj x y) := by
      intro x hx y hy hne
      simp only [mem_coe, mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        first | contradiction
              | exact hnac | exact hnad | exact hncd
              | exact (fun h => hnac h.symm) | exact (fun h => hnad h.symm)
              | exact (fun h => hncd h.symm)
              | exact hna.2 | exact hnc.2 | exact hnd.2
              | exact (fun h => hna.2 h.symm) | exact (fun h => hnc.2 h.symm)
              | exact (fun h => hnd.2 h.symm)
    have hcard : ({a.val,c.val,d.val,b} : Finset V).card = 4 := by
      rw [card_insert_of_notMem (by simp [hac',had',hna.1]),
        card_insert_of_notMem (by simp [hcd',hnc.1]),
        card_insert_of_notMem (by simp [hnd.1]), card_singleton]
    have hbound := star_bound v {a.val,c.val,d.val,b} hind (by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hu _ a.property
      · exact hu _ c.property
      · exact hu _ d.property
      · exact hvb)
    omega
  obtain ⟨s,t,p,hp⟩ := hamiltonian_of_no_independent_triple hA hno
  let q := p.map (SimpleGraph.Embedding.induce A).toHom
  refine ⟨q.support, q.support_ne_nil, ?_, q.isChain_adj_support, ?_⟩
  · rw [Walk.support_map]
    exact hp.isPath.support_nodup.map Subtype.val_injective
  · intro x
    rw [Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨y,_,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩, hp.mem_support ⟨x,hx⟩, rfl⟩

/-- If the two cut vertices are complete to both components, the forbidden
five-vertex star makes each component traceable. Their paths can then be joined. -/
theorem hamiltonian_of_universal_two_cut (u v : V) (huv : u ≠ v) (A B : Set V)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (huA : ∀ a ∈ A, G.Adj u a) (huB : ∀ b ∈ B, G.Adj u b)
    (hvB : ∀ b ∈ B, G.Adj v b)
    (ht : largestInducedTreeSize G ≤ 4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨a⟩ := hA.nonempty
  obtain ⟨b⟩ := hB.nonempty
  have hs' (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ A) :
      x ≠ y ∧ ¬ G.Adj x y :=
    ⟨(hs y hy x hx).1.symm, fun h => (hs y hy x hx).2 h.symm⟩
  obtain ⟨L, _, hLn, hLc, hLm⟩ :=
    spanning_list_of_universal_side u A B hA hs huA ⟨b.val,b.property,huB _ b.property⟩ ht
  obtain ⟨M, hMe, hMn, hMc, hMm⟩ :=
    spanning_list_of_universal_side u B A hB hs' huB ⟨a.val,a.property,huA _ a.property⟩ ht
  let W := L ++ u :: (M ++ [v])
  have hlast : (M ++ [v]).IsChain G.Adj := by
    apply hMc.append (List.IsChain.singleton v)
    intro x hx y hy
    have he : v = y := by simpa using hy
    exact he ▸ (hvB x ((hMm x).mp (List.mem_of_mem_getLast? hx))).symm
  have hmid : (u :: (M ++ [v])).IsChain G.Adj := by
    apply hlast.cons
    intro x hx
    rw [List.head?_append_of_ne_nil _ hMe] at hx
    exact huB x ((hMm x).mp (List.mem_of_mem_head? hx))
  have hWc : W.IsChain G.Adj := by
    apply hLc.append hmid
    intro x hx y hy
    have he : u = y := by simpa using hy
    exact he ▸ (huA x ((hLm x).mp (List.mem_of_mem_getLast? hx))).symm
  have huM : u ∉ M := fun h => houtB.1 ((hMm u).mp h)
  have hvM : v ∉ M := fun h => houtB.2 ((hMm v).mp h)
  have hWn : W.Nodup := by
    refine List.nodup_append.mpr ⟨hLn, ?_, ?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨by simp [huv, huM], List.nodup_append.mpr ⟨hMn, by simp, ?_⟩⟩
      intro x hx y hy
      have hyv : y = v := by simpa using hy
      subst y
      exact fun he => hvM (he ▸ hx)
    · intro x hx y hy
      have hxA := (hLm x).mp hx
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun he => houtA.1 (he ▸ hxA)
      rcases List.mem_append.mp hy with hy | hy
      · exact (hs x hxA y ((hMm y).mp hy)).1
      · have he : y = v := by simpa using hy
        exact fun h => houtA.2 ((h.trans he) ▸ hxA)
  have hWm (x : V) : x ∈ W := by
    by_cases hu : x = u
    · simp [W, hu]
    by_cases hv : x = v
    · simp [W, hv]
    rcases hcover x hu hv with h | h
    · exact List.mem_append_left _ ((hLm x).mpr h)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ ((hMm x).mpr h)))
  have hWe : W ≠ [] := List.ne_nil_of_mem (hWm u)
  let p := Walk.ofSupport W hWe hWc
  have hp : p.support = W := Walk.support_ofSupport hWe hWc
  have hpath : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hp]
  exact ⟨_, _, p, hpath.isHamiltonian_of_mem (fun x => by rw [hp]; exact hWm x)⟩

/-- The H1 branch with two nonclique components is traceable. The four existence
hypotheses follow from the minimum-cut property. -/
theorem hamiltonian_of_two_nonclique_components (u v : V) (huv : u ≠ v) (A B : Set V)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (huA : ∃ a ∈ A, G.Adj u a) (huB : ∃ b ∈ B, G.Adj u b)
    (hvA : ∃ a ∈ A, G.Adj v a) (hvB : ∃ b ∈ B, G.Adj v b)
    (hnA : ¬ G.IsClique A) (hnB : ¬ G.IsClique B)
    (ht : largestInducedTreeSize G ≤ 4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hs' (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ A) :
      x ≠ y ∧ ¬ G.Adj x y :=
    ⟨(hs y hy x hx).1.symm, fun h => (hs y hy x hx).2 h.symm⟩
  have both (w : V) (hoA : w ∉ A) (hoB : w ∉ B)
      (hmA : ∃ a ∈ A, G.Adj w a) (hmB : ∃ b ∈ B, G.Adj w b) :
      (∀ a ∈ A, G.Adj w a) ∧ (∀ b ∈ B, G.Adj w b) := by
    rcases cut_universal_one_side w A B hoA hoB hA hB hs hmA hmB ht with hu | hv
    · exact ⟨hu, cut_universal_other_side w A B hoB hB hs hu hmB hnA ht⟩
    · exact ⟨cut_universal_other_side w B A hoA hA hs' hv hmA hnB ht, hv⟩
  exact hamiltonian_of_universal_two_cut u v huv A B houtA houtB hcover hA hB hs
    (both u houtA.1 houtB.1 huA huB).1 (both u houtA.1 houtB.1 huA huB).2
    (both v houtA.2 houtB.2 hvA hvB).2 ht

theorem minimum_two_cut_attachments (u v : V) (huv : u ≠ v)
    (A B : Set V) (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hκ : vertexConnectivity G = 2) :
    (∃ a ∈ A, G.Adj u a) ∧ (∃ b ∈ B, G.Adj u b) ∧
    (∃ a ∈ A, G.Adj v a) ∧ (∃ b ∈ B, G.Adj v b) := by
  let S : Finset V := {u,v}
  have hS : S.card ≤ vertexConnectivity G := by
    change ({u,v} : Finset V).card ≤ _
    rw [card_insert_of_notMem (show u ∉ ({v} : Finset V) from by simpa using huv), card_singleton]
    exact hκ.ge
  have notA (a : V) (ha : a ∈ A) : a ∉ S := by
    have hu : a ≠ u := fun h => houtA.1 (h ▸ ha)
    have hv : a ≠ v := fun h => houtA.2 (h ▸ ha)
    simp [S,hu,hv]
  have notB (b : V) (hb : b ∈ B) : b ∉ S := by
    have hu : b ≠ u := fun h => houtB.1 (h ▸ hb)
    have hv : b ≠ v := fun h => houtB.2 (h ▸ hb)
    simp [S,hu,hv]
  have covers (x : V) (h : x ∉ S) : x ∈ A ∨ x ∈ B := by
    have h' : x ≠ u ∧ x ≠ v := by simpa [S] using h
    exact hcover x h'.1 h'.2
  obtain ⟨a⟩ := hA.nonempty
  obtain ⟨b⟩ := hB.nonempty
  have hbA : b.val ∉ A := fun h => (hs _ h _ b.property).1 rfl
  have haB : a.val ∉ B := fun h => (hs _ a.property _ h).1 rfl
  have meetA (x : V) (hx : x ∈ S) : ∃ w ∈ A, G.Adj x w := by
    obtain ⟨w, hw, _, hedge⟩ := minCut_adj_side S x hx hS A
      ⟨a.val,a.property,notA _ a.property⟩ ⟨b.val,hbA,notB _ b.property⟩ (by
        intro z hz y hy _ hy'
        exact (hs z hz y ((covers y hy').resolve_left hy)).2)
    exact ⟨w,hw,hedge⟩
  have meetB (x : V) (hx : x ∈ S) : ∃ w ∈ B, G.Adj x w := by
    obtain ⟨w, hw, _, hedge⟩ := minCut_adj_side S x hx hS B
      ⟨b.val,b.property,notB _ b.property⟩ ⟨a.val,haB,notA _ a.property⟩ (by
        intro z hz y hy _ hy' hedge
        exact (hs y ((covers y hy').resolve_right hy) z hz).2 hedge.symm)
    exact ⟨w,hw,hedge⟩
  exact ⟨meetA u (by simp [S]), meetB u (by simp [S]),
    meetA v (by simp [S]), meetB v (by simp [S])⟩

/-- For a minimum two-cut, the extra adjacency assumptions in the two-nonclique
case follow directly from minimality of the cut. -/
theorem conjecture199_of_two_nonclique_components (u v : V) (huv : u ≠ v)
    (A B : Set V) (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hnA : ¬ G.IsClique A) (hnB : ¬ G.IsClique B)
    (hκ : vertexConnectivity G = 2)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨huA,huB,hvA,hvB⟩ := minimum_two_cut_attachments u v huv A B houtA houtB
    hcover hA hB hs hκ
  exact hamiltonian_of_two_nonclique_components u v huv A B houtA houtB hcover hA hB hs
    huA huB hvA hvB hnA hnB (by omega)

/-- If one separator vertex is complete to both sides and the other is
complete to one side, insert the latter side in a spanning path of the former. -/
theorem hamiltonian_of_one_universal_two_cut (u v : V) (huv : u ≠ v) (A B : Set V)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (huA : ∀ a ∈ A, G.Adj u a) (hvA : ∀ a ∈ A, G.Adj v a)
    (huB : ∀ b ∈ B, G.Adj u b) (hvB : ∃ b ∈ B, G.Adj v b)
    (ht : largestInducedTreeSize G ≤ 4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨a⟩ := hA.nonempty
  obtain ⟨b,hb,hvb⟩ := hvB
  have hs' (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ A) :
      x ≠ y ∧ ¬ G.Adj x y :=
    ⟨(hs y hy x hx).1.symm, fun h => (hs y hy x hx).2 h.symm⟩
  obtain ⟨L,hLe,hLn,hLc,hLm⟩ := spanning_list_of_universal_side u A B hA hs huA
    ⟨b,hb,huB b hb⟩ ht
  obtain ⟨M,_,hMn,hMc,hMm⟩ := spanning_list_of_universal_side u B A hB hs' huB
    ⟨a.val,a.property,huA _ a.property⟩ ht
  obtain ⟨P,Q,hpq⟩ := List.append_of_mem ((hMm b).mpr hb)
  subst M
  let M := b :: Q
  let W := P ++ u :: (L ++ v :: M)
  have hP (x : V) (hx : x ∈ P) : x ∈ B := (hMm x).mp (List.mem_append_left _ hx)
  have hM (x : V) (hx : x ∈ M) : x ∈ B := (hMm x).mp (List.mem_append_right _ hx)
  have hlast : (v :: M).IsChain G.Adj := by
    apply hMc.right_of_append.cons
    intro x hx
    have hbx : b = x := by simpa [M] using hx
    exact hbx ▸ hvb
  have hmiddle : (L ++ v :: M).IsChain G.Adj := by
    apply hLc.append hlast
    intro x hx y hy
    have he : v = y := by simpa using hy
    exact he ▸ (hvA x ((hLm x).mp (List.mem_of_mem_getLast? hx))).symm
  have hupper : (u :: (L ++ v :: M)).IsChain G.Adj := by
    apply hmiddle.cons
    intro x hx
    rw [List.head?_append_of_ne_nil _ hLe] at hx
    exact huA x ((hLm x).mp (List.mem_of_mem_head? hx))
  have hWc : W.IsChain G.Adj := by
    apply hMc.left_of_append.append hupper
    intro x hx y hy
    have he : u = y := by simpa using hy
    exact he ▸ (huB x (hP x (List.mem_of_mem_getLast? hx))).symm
  have hvM : v ∉ M := fun h => houtB.2 (hM v h)
  have htail : (L ++ v :: M).Nodup := by
    refine List.nodup_append.mpr ⟨hLn, List.nodup_cons.mpr ⟨hvM,hMn.of_append_right⟩, ?_⟩
    intro x hx y hy
    have hxA := (hLm x).mp hx
    rcases List.mem_cons.mp hy with rfl | hy
    · exact fun h => houtA.2 (h ▸ hxA)
    · exact (hs x hxA y (hM y hy)).1
  have huTail : u ∉ L ++ v :: M := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact houtA.1 ((hLm u).mp h)
    · rcases List.mem_cons.mp h with he | h
      · exact huv he
      · exact houtB.1 (hM u h)
  have hWn : W.Nodup := by
    refine List.nodup_append.mpr ⟨hMn.of_append_left, List.nodup_cons.mpr ⟨huTail,htail⟩,?_⟩
    intro x hx y hy
    have hxB := hP x hx
    rcases List.mem_cons.mp hy with rfl | hy
    · exact fun he => houtB.1 (he ▸ hxB)
    rcases List.mem_append.mp hy with hy | hy
    · exact (hs y ((hLm y).mp hy) x hxB).1.symm
    rcases List.mem_cons.mp hy with rfl | hy
    · exact fun he => houtB.2 (he ▸ hxB)
    · exact (List.nodup_append.mp hMn).2.2 x hx y hy
  have hWm (x : V) : x ∈ W := by
    by_cases hxu : x = u
    · simp [W,hxu]
    by_cases hxv : x = v
    · simp [W,hxv]
    rcases hcover x hxu hxv with h | h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ ((hLm x).mpr h)))
    · rcases List.mem_append.mp ((hMm x).mpr h) with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_cons_of_mem _ h)))
  have hWe : W ≠ [] := List.ne_nil_of_mem (hWm u)
  let p := Walk.ofSupport W hWe hWc
  have hp : p.support = W := Walk.support_ofSupport hWe hWc
  have hpath : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hp]
  exact ⟨_, _, p, hpath.isHamiltonian_of_mem (fun x => by rw [hp]; exact hWm x)⟩

/-- If the H1 configuration has no Hamiltonian path, exactly one side is a
clique. Both cut vertices are complete to that side and incomplete to the other. -/
theorem frontier_of_two_component_case (u v : V) (huv : u ≠ v) (A B : Set V)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hnc : ¬ G.IsClique A ∨ ¬ G.IsClique B)
    (hκ : vertexConnectivity G = 2) (ht : largestInducedTreeSize G ≤ 4)
    (hno : ¬ ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) :
    (G.IsClique A ∧ ¬ G.IsClique B ∧
      (∀ x ∈ A, G.Adj u x ∧ G.Adj v x) ∧
      (∃ y ∈ B, ¬ G.Adj u y) ∧ (∃ y ∈ B, ¬ G.Adj v y)) ∨
    (G.IsClique B ∧ ¬ G.IsClique A ∧
      (∀ x ∈ B, G.Adj u x ∧ G.Adj v x) ∧
      (∃ y ∈ A, ¬ G.Adj u y) ∧ (∃ y ∈ A, ¬ G.Adj v y)) := by
  obtain ⟨huA,huB,hvA,hvB⟩ := minimum_two_cut_attachments u v huv A B houtA houtB
    hcover hA hB hs hκ
  have hs' (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ A) :
      x ≠ y ∧ ¬ G.Adj x y :=
    ⟨(hs y hy x hx).1.symm, fun h => (hs y hy x hx).2 h.symm⟩
  have mix {C D : Set V}
      (houtC : u ∉ C ∧ v ∉ C) (houtD : u ∉ D ∧ v ∉ D)
      (hcover' : ∀ x, x ≠ u → x ≠ v → x ∈ C ∨ x ∈ D)
      (hC : (G.induce C).Connected) (hD : (G.induce D).Connected)
      (hsep : ∀ x ∈ C, ∀ y ∈ D, x ≠ y ∧ ¬ G.Adj x y)
      (hswap : ∀ x ∈ D, ∀ y ∈ C, x ≠ y ∧ ¬ G.Adj x y)
      (huC : ∃ x ∈ C, G.Adj u x) (huD : ∃ x ∈ D, G.Adj u x)
      (hvC : ∃ x ∈ C, G.Adj v x) (hvD : ∃ x ∈ D, G.Adj v x)
      (hDnc : ¬ G.IsClique D) :
      (∀ x ∈ C, G.Adj u x ∧ G.Adj v x) ∧
      (∃ y ∈ D, ¬ G.Adj u y) ∧ (∃ y ∈ D, ¬ G.Adj v y) := by
    have complete (w : V) (hoC : w ∉ C) (hoD : w ∉ D)
        (hmeetC : ∃ x ∈ C, G.Adj w x) (hmeetD : ∃ x ∈ D, G.Adj w x) :
        ∀ x ∈ C, G.Adj w x := by
      rcases cut_universal_one_side w C D hoC hoD hC hD hsep hmeetC hmeetD ht with h | h
      · exact h
      · exact cut_universal_other_side w D C hoC hC hswap h hmeetC hDnc ht
    have hu := complete u houtC.1 houtD.1 huC huD
    have hv := complete v houtC.2 houtD.2 hvC hvD
    refine ⟨fun x hx => ⟨hu x hx,hv x hx⟩,?_,?_⟩
    · by_contra! h
      exact hno (hamiltonian_of_one_universal_two_cut u v huv C D houtC houtD hcover'
        hC hD hsep hu hv h hvD ht)
    · by_contra! h
      exact hno (hamiltonian_of_one_universal_two_cut v u huv.symm C D houtC.symm houtD.symm
        (fun x hx hy => hcover' x hy hx) hC hD hsep hv hu h huD ht)
  by_cases hAc : G.IsClique A
  · have hBnc := hnc.resolve_left (not_not_intro hAc)
    exact Or.inl ⟨hAc,hBnc,mix houtA houtB hcover hA hB hs hs' huA huB hvA hvB hBnc⟩
  · have hBc : G.IsClique B := by
      by_contra hBnc
      exact hno (hamiltonian_of_two_nonclique_components u v huv A B houtA houtB hcover
        hA hB hs huA huB hvA hvB hAc hBnc ht)
    exact Or.inr ⟨hBc,hAc,mix houtB houtA (fun x hx hy => (hcover x hx hy).symm)
      hB hA hs' hs huB huA hvB hvA hAc⟩

#print axioms frontier_of_two_component_case
#print axioms hamiltonian_of_one_universal_two_cut
#print axioms conjecture199_of_two_nonclique_components
#print axioms cut_universal_one_side
#print axioms cut_universal_other_side
#print axioms hamiltonian_of_two_nonclique_components
end Graph199
