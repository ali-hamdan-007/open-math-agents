import OMAReductions.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1

/-!
# The minimum two-cut case with two components, including a nonclique component

Decompose the nonclique component into its attachment groups, far cliques, and spare
neighbors. Order the resulting regular and dangling paths around the other component.
-/

namespace OMA.Graph199H1

open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1

section

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

end

section

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

end

section

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

end

section

open SimpleGraph

universe u

/-- Neighbor subgroups in a rooted H1 decomposition have independence number
at most two, including each attachment class and the spare subgroup. -/
theorem H1FarData.indepNum_le_two {V : Type u} [Fintype V] {G : SimpleGraph V}
    {v w : V} {A : Set V} (D : H1FarData G v w A) (S : Set V)
    (hS : ∀ x ∈ S, x ∈ A ∧ G.Adj v x) : (G.induce S).indepNum ≤ 2 := by
  classical
  by_contra! hn
  obtain ⟨t,ht⟩ := (G.induce S).exists_isNIndepSet_indepNum
  have hc : 2 < t.card := by rwa [ht.card_eq]
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hc
  have ha' := hS a.val a.property
  have hb' := hS b.val b.property
  have hc' := hS c.val c.property
  exact D.near_no_independent_triple _ _ _ ha'.1 hb'.1 hc'.1 ha'.2 hb'.2 hc'.2
    (fun e => hab (Subtype.ext e)) (fun e => hac (Subtype.ext e)) (fun e => hbc (Subtype.ext e))
    (ht.isIndepSet ha hb hab) (ht.isIndepSet ha hc hac) (ht.isIndepSet hb hc hbc)

/-- The full H1 graph problem follows from the corresponding block-ordering
problem. The only residual graphs have a clique side and rooted far blocks
on the other side. -/
theorem two_component_step_of_far_data
    (solve :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (v w : V) (A B : Set V), v ≠ w →
        (v ∉ A ∧ w ∉ A) → (v ∉ B ∧ w ∉ B) →
        (∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B) →
        (∀ x ∈ A, ∀ y ∈ B, x ≠ y) →
        B.Nonempty → G.IsClique B → (∀ x ∈ B, G.Adj v x ∧ G.Adj w x) →
        H1FarData G v w A →
        ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian) :
    OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1.H1 := by
  intro V _ _ G hκ ht v w A B hvw hnA hnB hvA hwA hvB hwB hA hB hcover hsep hnc
  by_contra hno
  have hshape := frontier_of_two_component_case v w hvw A B ⟨hvA,hwA⟩ ⟨hvB,hwB⟩
    hcover hA hB hsep hnc hκ ht hno
  have hs (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ A) : x ≠ y ∧ ¬ G.Adj x y :=
    ⟨(hsep y hy x hx).1.symm, fun h => (hsep y hy x hx).2 h.symm⟩
  obtain ⟨hmA,hmB,_,_⟩ := minimum_two_cut_attachments v w hvw A B ⟨hvA,hwA⟩ ⟨hvB,hwB⟩
    hcover hA hB hsep hκ
  rcases hshape with ⟨hcl,_,hfull,hmiss,_⟩ | ⟨hcl,_,hfull,hmiss,_⟩
  · have hcov (x : V) (hx : x ≠ v) (hy : x ≠ w) : x ∈ B ∨ x ∈ A :=
      (hcover x hx hy).symm
    let D := h1FarData v w B A ⟨hvB,hwB⟩ hcov hB hnA hs
      (fun x hx => (hfull x hx).1) (fun x hx => (hfull x hx).2)
      hmB hmiss hκ.ge ht
    exact hno (solve G v w B A hvw ⟨hvB,hwB⟩ ⟨hvA,hwA⟩ hcov
      (fun x hx y hy => (hs x hx y hy).1) hnA hcl hfull D)
  · let D := h1FarData v w A B ⟨hvA,hwA⟩ hcover hA hnB hsep
      (fun x hx => (hfull x hx).1) (fun x hx => (hfull x hx).2)
      hmA hmiss hκ.ge ht
    exact hno (solve G v w A B hvw ⟨hvA,hwA⟩ ⟨hvB,hwB⟩ hcover
      (fun x hx y hy => (hsep x hx y hy).1) hnB hcl hfull D)

end

section

open SimpleGraph

/-- Nonempty path segments can be linked in any order for which consecutive
endpoints are adjacent. The pieces are allowed to consist of a single vertex. -/
theorem flatten_block_chain {V : Type*} {G : SimpleGraph V} (blocks : List (List V))
    (nonempty : ∀ l ∈ blocks, l ≠ [])
    (internal : ∀ l ∈ blocks, l.IsChain G.Adj)
    (links : blocks.IsChain (fun l r =>
      ∀ a ∈ l.getLast?, ∀ b ∈ r.head?, G.Adj a b)) :
    blocks.flatten.IsChain G.Adj := by
  induction blocks with
  | nil => simp
  | cons l rest ih =>
    cases rest with
    | nil => simpa using internal l (by simp)
    | cons r tail =>
      obtain ⟨first, later⟩ := List.isChain_cons_cons.mp links
      apply (internal l (by simp)).append
        (ih (fun s hs => nonempty s (List.mem_cons_of_mem _ hs))
          (fun s hs => internal s (List.mem_cons_of_mem _ hs)) later)
      intro x hx y hy
      rw [List.flatten_cons, List.head?_append_of_ne_nil _ (nonempty r (by simp))] at hy
      exact first x hx y hy

/-- A partition of the vertex set into ordered spanning-path segments gives
a Hamiltonian path as soon as consecutive endpoints have connecting edges. -/
theorem hamiltonian_of_ordered_blocks {V : Type*} [Nonempty V] [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (blocks : List (List V))
    (parts : ∀ l ∈ blocks, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj)
    (disjoint : blocks.Pairwise List.Disjoint)
    (cover : ∀ x : V, ∃ l ∈ blocks, x ∈ l)
    (links : blocks.IsChain (fun l r =>
      ∀ a ∈ l.getLast?, ∀ b ∈ r.head?, G.Adj a b)) :
    ∃ s t : V, ∃ p : G.Walk s t, p.IsHamiltonian := by
  classical
  have chain := flatten_block_chain blocks (fun l h => (parts l h).1)
    (fun l h => (parts l h).2.2) links
  have distinct := List.nodup_flatten.mpr ⟨fun l h => (parts l h).2.1,disjoint⟩
  have all_mem (x : V) : x ∈ blocks.flatten := List.mem_flatten.mpr (cover x)
  have ne := List.ne_nil_of_mem (all_mem (Classical.arbitrary V))
  let p := Walk.ofSupport blocks.flatten ne chain
  have support : p.support = blocks.flatten := Walk.support_ofSupport ne chain
  have path : p.IsPath := Walk.IsPath.mk' (by rwa [support])
  exact ⟨_, _, p, path.isHamiltonian_of_mem (fun x => by rw [support]; exact all_mem x)⟩

end

section

open SimpleGraph Finset

/-- Insert an arbitrary finite family of mutually compatible path pieces
after an anchor. The first vertex is preserved, and the last vertex belongs
either to the anchor's possible ends or to a port of an inserted piece. -/
theorem append_indexed_blocks {V ι : Type*} [DecidableEq ι] {G : SimpleGraph V}
    (I : Finset ι) (U E : Set V) (carrier port : ι → Set V)
    (L : List V) (a b : V)
    (hhead : L.head? = some a) (hlast : L.getLast? = some b) (hb : b ∈ E)
    (hn : L.Nodup) (hc : L.IsChain G.Adj) (hm : ∀ x, x ∈ L ↔ x ∈ U)
    (pieces : ∀ i ∈ I, ∃ s ∈ port i, ∃ t ∈ port i, ∃ P : List V,
      P.head? = some s ∧ P.getLast? = some t ∧ P.Nodup ∧ P.IsChain G.Adj ∧
      (∀ x, x ∈ P ↔ x ∈ carrier i))
    (apart : ∀ i ∈ I, Disjoint U (carrier i))
    (separate : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (carrier i) (carrier j))
    (starts : ∀ i ∈ I, ∀ x ∈ E, ∀ y ∈ port i, G.Adj x y)
    (joins : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ x ∈ port i, ∀ y ∈ port j, G.Adj x y) :
    ∃ d : V, ∃ W : List V, (d ∈ E ∨ ∃ i ∈ I, d ∈ port i) ∧
      W.head? = some a ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔ x ∈ U ∨ ∃ i ∈ I, x ∈ carrier i) := by
  classical
  let good (J : Finset ι) := ∃ d : V, ∃ W : List V, (d ∈ E ∨ ∃ i ∈ J, d ∈ port i) ∧
      W.head? = some a ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔ x ∈ U ∨ ∃ i ∈ J, x ∈ carrier i)
  have build (J : Finset ι) : J ⊆ I → good J := by
    induction J using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨b,L,Or.inl hb,hhead,hlast,hn,hc,fun x => by simpa using hm x⟩
    | @insert i J hi ih =>
      intro hsub
      have hiI := hsub (mem_insert_self i J)
      have hJI : J ⊆ I := fun j hj => hsub (mem_insert_of_mem hj)
      obtain ⟨e,Q,he,hQh,hQl,hQn,hQc,hQm⟩ := ih hJI
      obtain ⟨s,hs,t,ht,P,hPh,hPl,hPn,hPc,hPm⟩ := pieces i hiI
      have hQP : Q.Disjoint P := by
        intro x hx hx'
        have hxi := (hPm x).mp hx'
        rcases (hQm x).mp hx with hxU | ⟨j,hj,hxj⟩
        · exact Set.disjoint_left.mp (apart i hiI) hxU hxi
        · have hne : j ≠ i := fun h => hi (h ▸ hj)
          exact Set.disjoint_left.mp (separate j (hJI hj) i hiI hne) hxj hxi
      have hes : G.Adj e s := by
        rcases he with heE | ⟨j,hj,hej⟩
        · exact starts i hiI e heE s hs
        · exact joins j (hJI hj) i hiI (fun h => hi (h ▸ hj)) e hej s hs
      have hQne : Q ≠ [] := fun h => by simp [h] at hQh
      have hPne : P ≠ [] := fun h => by simp [h] at hPh
      refine ⟨t,Q ++ P,Or.inr ⟨i,mem_insert_self i J,ht⟩,?_,?_,?_,?_,?_⟩
      · rwa [List.head?_append_of_ne_nil _ hQne]
      · simp [List.getLast?_append, hPl]
      · exact List.nodup_append.mpr ⟨hQn,hPn,fun x hx y hy heq => hQP hx (heq ▸ hy)⟩
      · apply hQc.append hPc
        intro x hx y hy
        have he' : e = x := by simpa [hQl] using hx
        have hs' : s = y := by simpa [hPh] using hy
        exact he' ▸ hs' ▸ hes
      · intro x
        simp only [List.mem_append,hQm,hPm,Finset.mem_insert]
        aesop
  exact build I (fun _ h => h)

end

section

open Finset SimpleGraph

private theorem clique_list {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} (hS : S.Nonempty) (hc : G.IsClique S) :
    ∃ L : List V, L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj ∧ (∀ x, x ∈ L ↔ x ∈ S) := by
  classical
  let L := S.toFinset.toList
  have hm (x : V) : x ∈ L ↔ x ∈ S := by simp [L]
  have hn : L.Nodup := nodup_toList _
  obtain ⟨x, hx⟩ := hS
  refine ⟨L, List.ne_nil_of_mem ((hm x).mpr hx), hn, List.Pairwise.isChain ?_, hm⟩
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact hc ((hm _).mp (List.get_mem _ _)) ((hm _).mp (List.get_mem _ _))
    (List.pairwise_iff_get.mp hn i j hij)

private theorem two_chains {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hV : ∃ a b : V, a ≠ b) (hα : G.indepNum ≤ 2) :
    ∃ L R : List V, L ≠ [] ∧ R ≠ [] ∧ (L ++ R).Nodup ∧
      L.IsChain G.Adj ∧ R.IsChain G.Adj ∧ (∀ x, x ∈ L ++ R) := by
  classical
  obtain ⟨a, b, hab⟩ := hV
  by_cases hc : G.Connected
  · obtain ⟨s, t, p, hp⟩ := conjecture199_of_indepNum_le_two hc hα
    cases hL : p.support with
    | nil => exact (p.support_ne_nil hL).elim
    | cons x R =>
      have hm (y : V) : y ∈ x :: R := hL ▸ hp.mem_support y
      have hR : R ≠ [] := by
        intro hr
        have ha : a = x := by simpa [hr] using hm a
        have hb : b = x := by simpa [hr] using hm b
        exact hab (ha.trans hb.symm)
      have hchain : (x :: R).IsChain G.Adj := hL ▸ p.isChain_adj_support
      exact ⟨[x], R, by simp, hR, by simpa [hL] using hp.isPath.support_nodup, by simp, hchain.tail, hm⟩
  · let A : Set V := {x | G.Reachable a x}
    have ha : a ∈ A := Reachable.rfl
    have hB : Aᶜ.Nonempty := by
      by_contra hn
      apply hc
      have hreach (x : V) : G.Reachable a x := by
        by_contra hx
        exact hn ⟨x, hx⟩
      let _ : Nonempty V := ⟨a⟩
      exact ⟨fun x y => (hreach x).symm.trans (hreach y)⟩
    obtain ⟨c, hc⟩ := hB
    have hcross (x y : V) (hx : x ∈ A) (hy : y ∈ Aᶜ) : ¬ G.Adj x y :=
      fun h => hy (hx.trans h.reachable)
    have emptyTriple (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
        (hnxy : ¬ G.Adj x y) (hnxz : ¬ G.Adj x z) (hnyz : ¬ G.Adj y z) : False := by
      have hind : G.IsIndepSet ((↑({x,y,z} : Finset V)) : Set V) := by
        intro i hi j hj hne
        simp only [mem_coe, mem_insert, mem_singleton] at hi hj
        rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
          first | contradiction | exact hnxy | exact hnxz | exact hnyz
                | exact (fun h => hnxy h.symm) | exact (fun h => hnxz h.symm)
                | exact (fun h => hnyz h.symm)
      have hcard := hind.card_le_indepNum
      rw [card_insert_of_notMem (by simp [hxy,hxz]), card_insert_of_notMem (by simp [hyz]),
        card_singleton] at hcard
      omega
    have hclA : G.IsClique A := by
      intro x hx y hy hxy
      by_contra hn
      exact emptyTriple x y c hxy (fun h => hc (h ▸ hx)) (fun h => hc (h ▸ hy))
        hn (hcross x c hx hc) (hcross y c hy hc)
    have hclB : G.IsClique Aᶜ := by
      intro x hx y hy hxy
      by_contra hn
      exact emptyTriple a x y (fun h => hx (h ▸ ha)) (fun h => hy (h ▸ ha)) hxy
        (hcross a x ha hx) (hcross a y ha hy) hn
    obtain ⟨L, hLe, hLn, hLc, hLm⟩ := clique_list ⟨a, ha⟩ hclA
    obtain ⟨R, hRe, hRn, hRc, hRm⟩ := clique_list ⟨c, hc⟩ hclB
    refine ⟨L, R, hLe, hRe, List.nodup_append.mpr ⟨hLn, hRn, ?_⟩, hLc, hRc, ?_⟩
    · rintro x hx y hy rfl
      exact (hRm x).mp hy ((hLm x).mp hx)
    · intro x
      by_cases hx : x ∈ A
      · exact List.mem_append_left _ ((hLm x).mpr hx)
      · exact List.mem_append_right _ ((hRm x).mpr hx)

/-- If two disjoint blocks are joined completely, a nonempty clique block can
be inserted between two spanning chains of a block with independence at most two. -/
theorem block_path {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {S T : Set V} (hS : ∃ a ∈ S, ∃ b ∈ S, a ≠ b) (hT : T.Nonempty)
    (hST : Disjoint S T) (hα : (G.induce S).indepNum ≤ 2) (hclique : G.IsClique T)
    (hjoin : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ L : List V, L.head? = some a ∧ L.getLast? = some b ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ (∀ x, x ∈ L ↔ x ∈ S ∪ T) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hS
  obtain ⟨L₀,R₀,hL₀,hR₀,hnd,hLc,hRc,hm⟩ :=
    two_chains (G := G.induce S)
      ⟨⟨a,ha⟩, ⟨b,hb⟩, fun he => hab (congrArg Subtype.val he)⟩ hα
  obtain ⟨M,hMe,hMn,hMc,hMm⟩ := clique_list hT hclique
  let L := L₀.map Subtype.val
  let R := R₀.map Subtype.val
  have hl : L ≠ [] := by cases L₀ <;> simp_all [L]
  have hr : R ≠ [] := by cases R₀ <;> simp_all [R]
  have hmS (x : V) : x ∈ L ++ R ↔ x ∈ S := by
    change x ∈ L₀.map Subtype.val ++ R₀.map Subtype.val ↔ _
    rw [← List.map_append, List.mem_map]
    constructor
    · rintro ⟨y,_,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩, hm _, rfl⟩
  have hnLR : (L ++ R).Nodup := by
    change (L₀.map Subtype.val ++ R₀.map Subtype.val).Nodup
    rw [← List.map_append]
    exact hnd.map Subtype.val_injective
  have lim (x : V) (hx : x ∈ L) : x ∈ S := (hmS x).mp (List.mem_append_left _ hx)
  have rim (x : V) (hx : x ∈ R) : x ∈ S := (hmS x).mp (List.mem_append_right _ hx)
  have lc : L.IsChain G.Adj :=
    List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hLc
  have rc : R.IsChain G.Adj :=
    List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hRc
  let W := L ++ (M ++ R)
  refine ⟨L.head hl, lim _ (List.head_mem hl), R.getLast hr, rim _ (List.getLast_mem hr), W,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [W, List.head?_eq_some_head hl]
  · simp [W, List.getLast?_eq_some_getLast hr]
  · have hLR := List.nodup_append.mp hnLR
    have hMr : (M ++ R).Nodup := by
      refine List.nodup_append.mpr ⟨hMn,hLR.2.1,?_⟩
      rintro x hx y hy rfl
      exact Set.disjoint_left.mp hST (rim x hy) ((hMm x).mp hx)
    refine List.nodup_append.mpr ⟨hLR.1,hMr,?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · rintro rfl
      exact Set.disjoint_left.mp hST (lim x hx) ((hMm x).mp hy)
    · exact hLR.2.2 x hx y hy
  · have hMR : (M ++ R).IsChain G.Adj := by
      apply hMc.append rc
      intro x hx y hy
      exact (hjoin y (rim y (List.mem_of_mem_head? hy)) x ((hMm x).mp
        (List.mem_of_mem_getLast? hx))).symm
    apply lc.append hMR
    intro x hx y hy
    rw [List.head?_append_of_ne_nil _ hMe] at hy
    exact hjoin x (lim x (List.mem_of_mem_getLast? hx)) y ((hMm y).mp
      (List.mem_of_mem_head? hy))
  · intro x
    have h := hmS x
    simp only [List.mem_append] at h
    simp only [W, List.mem_append, Set.mem_union, ← h, hMm]
    tauto

private theorem spare_cover {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Set V} (hα : (G.induce S).indepNum ≤ 2) :
    ∃ P R : List V, (P ++ R).Nodup ∧ P.IsChain G.Adj ∧ R.IsChain G.Adj ∧
      (∀ x, x ∈ P ++ R ↔ x ∈ S) := by
  classical
  by_cases hpair : ∃ a ∈ S, ∃ b ∈ S, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hpair
    obtain ⟨P, R, _, _, hn, hp, hr, hm⟩ :=
      two_chains (G := G.induce S)
        ⟨⟨a,ha⟩, ⟨b,hb⟩, fun he => hab (congrArg Subtype.val he)⟩ hα
    refine ⟨P.map Subtype.val, R.map Subtype.val, ?_, ?_, ?_, ?_⟩
    · rw [← List.map_append]
      exact hn.map Subtype.val_injective
    · exact List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hp
    · exact List.isChain_map_of_isChain Subtype.val (fun _ _ h => induce_adj.mp h) hr
    · intro x
      rw [← List.map_append, List.mem_map]
      constructor
      · rintro ⟨y, _, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x,hx⟩, hm _, rfl⟩
  · by_cases hS : S.Nonempty
    · obtain ⟨a, ha⟩ := hS
      refine ⟨[a], [], by simp, by simp, by simp, ?_⟩
      intro x
      simp only [List.append_nil, List.mem_singleton]
      exact ⟨fun h => h.symm ▸ ha, fun hx => by
        by_contra hn
        exact hpair ⟨x, hx, a, ha, hn⟩⟩
    · refine ⟨[], [], by simp, by simp, by simp, ?_⟩
      intro x
      simp only [List.nil_append, List.not_mem_nil, false_iff]
      exact fun hx => hS ⟨x,hx⟩

/-- An ordered anchor path survives insertion of a disjoint spare set with
independence number at most two when both anchor endpoints see every spare vertex. -/
theorem spare_sandwich {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {S U : Set V} {L : List V} {a b : V}
    (hhead : L.head? = some a) (htail : L.getLast? = some b)
    (hn : L.Nodup) (hc : L.IsChain G.Adj) (hm : ∀ x, x ∈ L ↔ x ∈ U)
    (hSU : Disjoint S U) (hα : (G.induce S).indepNum ≤ 2)
    (ha : ∀ x ∈ S, G.Adj a x) (hb : ∀ x ∈ S, G.Adj b x) :
    ∃ c ∈ S ∪ ({a,b} : Set V), ∃ d ∈ S ∪ ({a,b} : Set V), ∃ W : List V,
      W.head? = some c ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔ x ∈ S ∪ U) := by
  obtain ⟨P,R,hnPR,hPc,hRc,hmS⟩ := spare_cover (G := G) hα
  have hP (x : V) (hx : x ∈ P) : x ∈ S := (hmS x).mp (List.mem_append_left _ hx)
  have hR (x : V) (hx : x ∈ R) : x ∈ S := (hmS x).mp (List.mem_append_right _ hx)
  have hePL : (P ++ L).getLast? = some b := by simp [htail]
  have hWc : ((P ++ L) ++ R).IsChain G.Adj := by
    apply (hPc.append hc ?_).append hRc
    · intro x hx y hy
      have hbx : b = x := by simpa [hePL] using hx
      exact hbx ▸ hb y (hR y (List.mem_of_mem_head? hy))
    · intro x hx y hy
      have hay : a = y := by simpa [hhead] using hy
      exact hay ▸ (ha x (hP x (List.mem_of_mem_getLast? hx))).symm
  have hWn : ((P ++ L) ++ R).Nodup := by
    have hnd := List.nodup_append.mp hnPR
    have hPL : (P ++ L).Nodup := by
      refine List.nodup_append.mpr ⟨hnd.1, hn, ?_⟩
      rintro x hx y hy rfl
      exact Set.disjoint_left.mp hSU (hP x hx) ((hm x).mp hy)
    refine List.nodup_append.mpr ⟨hPL, hnd.2.1, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact hnd.2.2 x hx y hy
    · rintro rfl
      exact Set.disjoint_left.mp hSU (hR x hy) ((hm x).mp hx)
  let W := (P ++ L) ++ R
  have hWe : W ≠ [] := List.ne_nil_of_mem
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_of_mem_head? hhead)))
  refine ⟨W.head hWe, ?_, W.getLast hWe, ?_, W, List.head?_eq_some_head hWe,
    List.getLast?_eq_some_getLast hWe, hWn, hWc, ?_⟩
  · by_cases hp : P = []
    · have he : W.head? = some a := by simp [W, hp, hhead]
      exact Or.inr (by simp [List.head_of_head?_eq_some he])
    · have he : W.head? = some (P.head hp) := by
        simp [W, List.head?_eq_some_head hp]
      exact Or.inl (by rw [List.head_of_head?_eq_some he]; exact hP _ (List.head_mem hp))
  · by_cases hr : R = []
    · have he : W.getLast? = some b := by simp [W, hr, htail]
      exact Or.inr (by simp [List.getLast_of_getLast?_eq_some he])
    · have he : W.getLast? = some (R.getLast hr) := by
        simp [W, List.getLast?_eq_some_getLast hr]
      exact Or.inl (by rw [List.getLast_of_getLast?_eq_some he]; exact hR _ (List.getLast_mem hr))
  · intro x
    have h := hmS x
    simp only [List.mem_append] at h
    simp only [W, List.mem_append, Set.mem_union, ← h, hm]
    tauto

end

section

open Finset SimpleGraph

private theorem chain_of_clique_list {V : Type*} {G : SimpleGraph V}
    {S : Set V} (hc : G.IsClique S) {L : List V} (hn : L.Nodup)
    (hm : ∀ x ∈ L, x ∈ S) : L.IsChain G.Adj := by
  apply List.Pairwise.isChain
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact hc (hm _ (List.get_mem _ _)) (hm _ (List.get_mem _ _))
    (List.pairwise_iff_get.mp hn i j hij)

/-- Enumerate a clique as a path ending at the prescribed vertex. -/
theorem clique_list_ending {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} {x : V} (hx : x ∈ S) (hc : G.IsClique S) :
    ∃ L : List V, L.getLast? = some x ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ y, y ∈ L ↔ y ∈ S) := by
  classical
  let L := (S.toFinset.erase x).toList ++ [x]
  have hm (y : V) : y ∈ L ↔ y ∈ S := by
    by_cases h : y = x <;> simp [L, h, hx]
  have hn : L.Nodup := by
    refine List.nodup_append.mpr ⟨nodup_toList _, by simp, ?_⟩
    rintro a ha b hb rfl
    have hax : a = x := by simpa using hb
    exact (mem_erase.mp (mem_toList.mp ha)).1 hax
  exact ⟨L, by simp [L], hn, chain_of_clique_list hc hn (fun y hy => (hm y).mp hy), hm⟩

/-- Enumerate a clique as a path starting at the prescribed vertex. -/
theorem clique_list_starting {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} {x : V} (hx : x ∈ S) (hc : G.IsClique S) :
    ∃ L : List V, L.head? = some x ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ y, y ∈ L ↔ y ∈ S) := by
  obtain ⟨L, hlast, hn, _, hm⟩ := clique_list_ending hx hc
  have hnr : L.reverse.Nodup := List.nodup_reverse.mpr hn
  have hmr (y : V) : y ∈ L.reverse ↔ y ∈ S := by simpa using hm y
  exact ⟨L.reverse, by simpa [List.head?_reverse] using hlast, hnr,
    chain_of_clique_list hc hnr (fun y hy => (hmr y).mp hy), hmr⟩

/-- Join two outside vertices through a nonempty clique to which both are complete. -/
theorem clique_bridge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (w v : V) {B : Set V} (hwv : w ≠ v) (hw : w ∉ B) (hv : v ∉ B)
    (hB : B.Nonempty) (hc : G.IsClique B)
    (hwb : ∀ b ∈ B, G.Adj w b) (hvb : ∀ b ∈ B, G.Adj v b) :
    ∃ L : List V, L.head? = some w ∧ L.getLast? = some v ∧ L.Nodup ∧
      L.IsChain G.Adj ∧ (∀ x, x ∈ L ↔ x ∈ insert w (insert v B)) := by
  obtain ⟨b, hb⟩ := hB
  obtain ⟨M, hlast, hn, hmc, hm⟩ := clique_list_ending hb hc
  have hMe : M ≠ [] := by
    intro h
    simp [h] at hlast
  have hMV : (M ++ [v]).IsChain G.Adj := by
    apply hmc.append (List.IsChain.singleton v)
    intro x hx y hy
    have hbx : b = x := by simpa [hlast] using hx
    have hvy : v = y := by simpa using hy
    exact hbx ▸ hvy ▸ (hvb b hb).symm
  refine ⟨w :: (M ++ [v]), by simp, ?_, ?_, hMV.cons ?_, ?_⟩
  · change ((w :: M) ++ [v]).getLast? = some v
    rw [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hn, by simp, ?_⟩⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact hw ((hm w).mp h)
      · exact hwv (List.mem_singleton.mp h)
    · rintro x hx y hy rfl
      have hxv : x = v := List.mem_singleton.mp hy
      exact hv (hxv ▸ (hm x).mp hx)
  · intro x hx
    rw [List.head?_append_of_ne_nil _ hMe] at hx
    exact hwb x ((hm x).mp (List.mem_of_mem_head? hx))
  · intro x
    simp [hm]
    tauto

/-- Start with a clique ending at a prescribed neighbour of w, then traverse
the clique bridge from w to v. -/
theorem clique_prefix_bridge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (w v : V) {B : Set V} (hwv : w ≠ v) (hw : w ∉ B) (hv : v ∉ B)
    (hB : B.Nonempty) (hc : G.IsClique B)
    (hwb : ∀ b ∈ B, G.Adj w b) (hvb : ∀ b ∈ B, G.Adj v b)
    {T : Set V} {x : V} (hx : x ∈ T) (hTc : G.IsClique T)
    (hTw : w ∉ T) (hTv : v ∉ T) (hTB : Disjoint T B) (hxw : G.Adj x w) :
    ∃ L : List V, L ≠ [] ∧ L.getLast? = some v ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ y, y ∈ L ↔ y ∈ T ∪ insert w (insert v B)) := by
  obtain ⟨M, hlast, hMn, hMc, hMm⟩ := clique_list_ending hx hTc
  obtain ⟨N, hNhead, hNtail, hNn, hNc, hNm⟩ := clique_bridge w v hwv hw hv hB hc hwb hvb
  have hlast' : (M ++ N).getLast? = some v := by simp [hNtail]
  refine ⟨M ++ N, ?_, hlast', ?_, ?_, ?_⟩
  · exact List.ne_nil_of_mem (List.mem_of_mem_getLast? hlast')
  · refine List.nodup_append.mpr ⟨hMn, hNn, ?_⟩
    rintro a ha b hb rfl
    have haT := (hMm a).mp ha
    have haB := (hNm a).mp hb
    simp only [Set.mem_insert_iff] at haB
    rcases haB with rfl | rfl | h
    · exact hTw haT
    · exact hTv haT
    · exact Set.disjoint_left.mp hTB haT h
  · apply hMc.append hNc
    intro a ha b hb
    have hxa : x = a := by simpa [hlast] using ha
    have hwb' : w = b := by simpa [hNhead] using hb
    exact hxa ▸ hwb' ▸ hxw
  · intro y
    simp [hMm, hNm]
    tauto

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {v w : V} {A : Set V}

private theorem regular_of_far_data (D : H1FarData G v w A) (i : Fin D.n)
    (hi : ¬ ∃ a, D.near i = {a}) :
    ∃ a ∈ D.near i, ∃ b ∈ D.near i, ∃ L : List V,
      L.head? = some a ∧ L.getLast? = some b ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ x, x ∈ L ↔ x ∈ D.near i ∪ D.far i) := by
  apply block_path _ (D.far_nonempty i) _ (D.indepNum_le_two _ (D.near_facts i))
    (D.far_clique i) (fun a ha b hb => D.same_attachment_complete i a b ha hb)
  · obtain ⟨a,ha⟩ := D.near_nonempty i
    refine ⟨a,ha,?_⟩
    by_contra! h
    apply hi
    refine ⟨a, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr ha)⟩
    intro b hb
    exact Set.mem_singleton_iff.mpr (h b hb).symm
  · apply Set.disjoint_left.mpr
    intro x hn hf
    exact (D.far_facts i x hf).2 (D.near_facts i x hn).2

/-- The central path uses one anchored block, the spare group, and all the
other regular blocks. A short anchor retains only its singleton near port. -/
theorem middle_of_far_data (D : H1FarData G v w A) (i : Fin D.n) (I : Finset (Fin D.n))
    (hI : ∀ j ∈ I, j ≠ i ∧ ¬ ∃ a, D.near j = {a})
    (short : Bool) (hcore : if short then (∃ a, D.near i = {a}) else ¬ ∃ a, D.near i = {a}) :
    ∃ a ∈ D.spare ∪ D.near i, ∃ d : V, ∃ W : List V,
      (d ∈ D.spare ∪ D.near i ∨ ∃ j ∈ I, d ∈ D.near j) ∧
      W.head? = some a ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔
        x ∈ D.spare ∪ (if short then D.near i else D.near i ∪ D.far i) ∨
          ∃ j ∈ I, x ∈ D.near j ∪ D.far j) := by
  let C := if short then D.near i else D.near i ∪ D.far i
  let E := D.spare ∪ D.near i
  have hanchor :
      ∃ a ∈ D.near i, ∃ b ∈ D.near i, ∃ L : List V,
        L.head? = some a ∧ L.getLast? = some b ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        (∀ x, x ∈ L ↔ x ∈ C) := by
    cases short with
    | false =>
      exact regular_of_far_data D i (by simpa using hcore)
    | true =>
      have hsingle : ∃ a, D.near i = {a} := by simpa using hcore
      obtain ⟨a,ha⟩ := hsingle
      refine ⟨a,by simp [ha],a,by simp [ha],[a],rfl,rfl,by simp,List.IsChain.singleton a,?_⟩
      intro x
      simp [C,ha]
  obtain ⟨a,ha,b,hb,L,hLh,hLl,hLn,hLc,hLm⟩ := hanchor
  have hcore_sep : Disjoint D.spare C := by
    apply Set.disjoint_left.mpr
    intro x hs hx
    cases short with
    | false =>
      rcases hx with hn | hf
      · exact D.spare_disjoint i x hs hn
      · exact (D.far_facts i x hf).2 (D.spare_facts x hs).2
    | true => exact D.spare_disjoint i x hs hx
  obtain ⟨s,hs,t,ht,Q,hQh,hQl,hQn,hQc,hQm⟩ :=
    spare_sandwich hLh hLl hLn hLc hLm hcore_sep
      (D.indepNum_le_two _ D.spare_facts)
      (fun x hx => (D.spare_attachment_complete i x a hx ha).symm)
      (fun x hx => (D.spare_attachment_complete i x b hx hb).symm)
  have hend {x : V} (hx : x ∈ D.spare ∪ ({a,b} : Set V)) : x ∈ E := by
    rcases hx with hx | hx
    · exact Or.inl hx
    · apply Or.inr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
  have separate {j k : Fin D.n} (hjk : j ≠ k) :
      Disjoint (D.near j ∪ D.far j) (D.near k ∪ D.far k) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact D.near_disjoint hjk hx hy
    · exact (D.far_facts k x hy).2 (D.near_facts j x hx).2
    · exact (D.far_facts j x hx).2 (D.near_facts k x hy).2
    · exact (D.far_separated hjk hx hy).1 rfl
  have csub : C ⊆ D.near i ∪ D.far i := by
    cases short with
    | false => exact fun _ h => h
    | true => exact fun _ h => Or.inl h
  have apart (j : Fin D.n) (hj : j ∈ I) : Disjoint (D.spare ∪ C) (D.near j ∪ D.far j) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hs | hx
    · rcases hy with hy | hy
      · exact D.spare_disjoint j x hs hy
      · exact (D.far_facts j x hy).2 (D.spare_facts x hs).2
    · exact Set.disjoint_left.mp (separate (hI j hj).1.symm) (csub hx) hy
  have starts (j : Fin D.n) (hj : j ∈ I) (x : V) (hx : x ∈ E)
      (y : V) (hy : y ∈ D.near j) : G.Adj x y := by
    rcases hx with hx | hx
    · exact D.spare_attachment_complete j x y hx hy
    · exact D.cross_attachment_complete (hI j hj).1.symm hx hy
  obtain ⟨d,W,hd,hWh,hWl,hWn,hWc,hWm⟩ :=
    append_indexed_blocks I (D.spare ∪ C) E (fun j => D.near j ∪ D.far j) D.near
      Q s t hQh hQl (hend ht) hQn hQc hQm
      (fun j hj => regular_of_far_data D j (hI j hj).2) apart
      (fun _ _ _ _ h => separate h) starts
      (fun _ _ _ _ h _ hx _ hy => D.cross_attachment_complete h hx hy)
  exact ⟨s,hend hs,d,W,hd,hWh,hWl,hWn,hWc,hWm⟩

end

section

open SimpleGraph Finset

universe u
variable {V : Type u} {G : SimpleGraph V}
  {v w : V} {A B : Set V}

private def Dangling (D : H1FarData G v w A) (i : Fin D.n) : Prop :=
  ∃ a, D.near i = {a}

private theorem choose_dangling_cases (D : H1FarData G v w A) :
    (∀ i, ¬ Dangling D i) ∨
    (∃ i, Dangling D i ∧ ∀ j, j ≠ i → ¬ Dangling D j) ∨
    (∃ i j, i ≠ j ∧ Dangling D i ∧ Dangling D j ∧
      ∀ k, k ≠ i → k ≠ j → ¬ Dangling D k) := by
  classical
  by_cases h : ∃ i, Dangling D i
  · obtain ⟨i, hi⟩ := h
    by_cases h' : ∃ j, j ≠ i ∧ Dangling D j
    · obtain ⟨j, hji, hj⟩ := h'
      refine Or.inr (Or.inr ⟨i,j,hji.symm,hi,hj,?_⟩)
      intro k hki hkj hk
      have hlt : 2 < {l | ∃ a, D.near l = {a}}.ncard :=
        (Set.two_lt_ncard_iff (s := {l | ∃ a, D.near l = {a}})).mpr
          ⟨i,j,k,hi,hj,hk,hji.symm,hki.symm,hkj.symm⟩
      exact (not_lt_of_ge D.at_most_two_singleton) hlt
    · exact Or.inr (Or.inl ⟨i,hi,fun j hji hj => h' ⟨j,hji,hj⟩⟩)
  · exact Or.inl (fun i hi => h ⟨i,hi⟩)

private def Core (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) : Set V :=
  if short then D.near i else D.near i ∪ D.far i

private def InitialFar (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) : Set V :=
  if short then D.far i else ∅

private def Middle (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) : Set V :=
  (D.spare ∪ Core D i short) ∪ {x | ∃ j ∈ I, x ∈ D.near j ∪ D.far j}

private def MiddlePorts (D : H1FarData G v w A) (i : Fin D.n) (I : Finset (Fin D.n)) : Set V :=
  (D.spare ∪ D.near i) ∪ {x | ∃ j ∈ I, x ∈ D.near j}

private theorem core_sub (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) :
    Core D i short ⊆ D.near i ∪ D.far i := by
  cases short <;> simp [Core]

private theorem initial_sub (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) :
    InitialFar D i short ⊆ D.far i := by
  cases short <;> simp [InitialFar]

private theorem near_far_disjoint (D : H1FarData G v w A) (i j : Fin D.n) :
    Disjoint (D.near i) (D.far j) := by
  rw [Set.disjoint_left]
  exact fun x hx hy => (D.far_facts j x hy).2 (D.near_facts i x hx).2

private theorem block_disjoint (D : H1FarData G v w A) {i j : Fin D.n} (hij : i ≠ j) :
    Disjoint (D.near i ∪ D.far i) (D.near j ∪ D.far j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact D.near_disjoint hij hx hy
  · exact Set.disjoint_left.mp (near_far_disjoint D i j) hx hy
  · exact Set.disjoint_left.mp (near_far_disjoint D j i) hy hx
  · exact (D.far_separated hij hx hy).1 rfl

private theorem spare_block_disjoint (D : H1FarData G v w A) (i : Fin D.n) :
    Disjoint D.spare (D.near i ∪ D.far i) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hy with hy | hy
  · exact D.spare_disjoint i x hx hy
  · exact (D.far_facts i x hy).2 (D.spare_facts x hx).2

private theorem block_subset (D : H1FarData G v w A) (i : Fin D.n) :
    D.near i ∪ D.far i ⊆ A := by
  intro x hx
  exact hx.elim (fun h => (D.near_facts i x h).1) (fun h => (D.far_facts i x h).1)

private theorem middle_subset (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) :
    Middle D i short I ⊆ A := by
  intro x hx
  rcases hx with (hx | hx) | ⟨j,_,hx⟩
  · exact (D.spare_facts x hx).1
  · exact block_subset D i (core_sub D i short hx)
  · exact block_subset D j hx

private theorem initial_middle_disjoint (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) (hI : i ∉ I) :
    Disjoint (InitialFar D i short) (Middle D i short I) := by
  cases short with
  | false => simp [InitialFar]
  | true =>
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x ∈ D.far i := initial_sub D i true hx
    rcases hy with (hy | hy) | ⟨j,hj,hy⟩
    · exact Set.disjoint_left.mp (spare_block_disjoint D i) hy (Or.inr hx')
    · exact Set.disjoint_left.mp (near_far_disjoint D i i) (by simpa [Core] using hy) hx'
    · have hij : i ≠ j := fun he => hI (he.symm ▸ hj)
      exact Set.disjoint_left.mp (block_disjoint D hij) (Or.inr hx') hy

private theorem middle_terminal_disjoint (D : H1FarData G v w A) (i j : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) (hij : i ≠ j) (hjI : j ∉ I) :
    Disjoint (Middle D i short I) (D.near j ∪ D.far j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with (hx | hx) | ⟨k,hk,hx⟩
  · exact Set.disjoint_left.mp (spare_block_disjoint D j) hx hy
  · exact Set.disjoint_left.mp (block_disjoint D hij) (core_sub D i short hx) hy
  · have hkj : k ≠ j := fun he => hjI (he ▸ hk)
    exact Set.disjoint_left.mp (block_disjoint D hkj) hx hy

private theorem initial_core_cover (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) {x : V} (hx : x ∈ D.near i ∪ D.far i) :
    x ∈ InitialFar D i short ∨ x ∈ Core D i short := by
  cases short <;> simpa [InitialFar, Core, or_comm] using hx

private theorem cuts_disjoint_A (houtA : v ∉ A ∧ w ∉ A)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y) :
    Disjoint (insert w (insert v B)) A := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [Set.mem_insert_iff] at hx
  rcases hx with rfl | rfl | hx
  · exact houtA.2 hy
  · exact houtA.1 hy
  · exact hsep x hy x hx rfl

private theorem list_disjoint_of_support {L R : List V} {S T : Set V}
    (hL : ∀ x, x ∈ L ↔ x ∈ S) (hR : ∀ x, x ∈ R ↔ x ∈ T)
    (hST : Disjoint S T) : L.Disjoint R :=
  fun x hx hy => Set.disjoint_left.mp hST ((hL x).mp hx) ((hR x).mp hy)

variable [Fintype V]

private theorem prefix_exists (D : H1FarData G v w A) (i : Fin D.n) (short : Bool)
    (hshort : short = true → Dangling D i)
    (hvw : v ≠ w) (houtA : v ∉ A ∧ w ∉ A) (houtB : v ∉ B ∧ w ∉ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y)
    (hB : B.Nonempty) (hcl : G.IsClique B) (hvb : ∀ x ∈ B, G.Adj v x ∧ G.Adj w x) :
    ∃ L : List V, L ≠ [] ∧ L.getLast? = some v ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ x, x ∈ L ↔ x ∈ InitialFar D i short ∪ insert w (insert v B)) := by
  cases short with
  | false =>
    obtain ⟨L,hh,ht,hn,hc,hm⟩ := clique_bridge w v hvw.symm houtB.2 houtB.1 hB hcl
      (fun x h => (hvb x h).2) (fun x h => (hvb x h).1)
    have hne : L ≠ [] := by intro he; simp [he] at hh
    exact ⟨L,hne,ht,hn,hc,by simpa [InitialFar] using hm⟩
  | true =>
    obtain ⟨a,ha⟩ := hshort rfl
    obtain ⟨x,hx,hxw⟩ := D.singleton_hooks i a ha
    have hTw : w ∉ D.far i := fun h => houtA.2 (D.far_facts i w h).1
    have hTv : v ∉ D.far i := fun h => houtA.1 (D.far_facts i v h).1
    have hTB : Disjoint (D.far i) B := Set.disjoint_left.mpr
      (fun x hx hy => hsep x (D.far_facts i x hx).1 x hy rfl)
    simpa [InitialFar] using clique_prefix_bridge w v hvw.symm houtB.2 houtB.1 hB hcl
      (fun x h => (hvb x h).2) (fun x h => (hvb x h).1) hx (D.far_clique i) hTw hTv hTB hxw.symm

private theorem terminal_exists (D : H1FarData G v w A) (j : Fin D.n)
    (hj : Dangling D j) :
    ∃ a ∈ D.near j, ∃ L : List V, L.head? = some a ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ x, x ∈ L ↔ x ∈ D.near j ∪ D.far j) := by
  obtain ⟨a,ha⟩ := hj
  have ha' : a ∈ D.near j := by simp [ha]
  obtain ⟨x,hx⟩ := D.far_nonempty j
  obtain ⟨L,hh,hn,hc,hm⟩ := clique_list_starting hx (D.far_clique j)
  have hn' : a ∉ L := fun h => Set.disjoint_left.mp (near_far_disjoint D j j) ha' ((hm a).mp h)
  refine ⟨a,ha',a::L,rfl, List.nodup_cons.mpr ⟨hn',hn⟩, ?_, ?_⟩
  · cases L with
    | nil => simp
    | cons y ys =>
      apply List.isChain_cons_cons.mpr
      exact ⟨D.same_attachment_complete j a y ha' ((hm y).mp (by simp)), hc⟩
  · intro y
    simp [hm,ha]

private theorem finish_from_middle [DecidableEq V]
    (D : H1FarData G v w A) (i : Fin D.n) (short : Bool)
    (I : Finset (Fin D.n)) (terminal : Option (Fin D.n))
    (hshort : short = true → Dangling D i)
    (hiI : i ∉ I) (hit : terminal ≠ some i)
    (hrest : ∀ j, j ≠ i → j ∉ I → terminal = some j)
    (hterm : ∀ j, terminal = some j → j ∉ I ∧ Dangling D j)
    (hvw : v ≠ w) (houtA : v ∉ A ∧ w ∉ A) (houtB : v ∉ B ∧ w ∉ B)
    (hcover : ∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y)
    (hB : B.Nonempty) (hcl : G.IsClique B) (hvb : ∀ x ∈ B, G.Adj v x ∧ G.Adj w x)
    (hM : ∃ a ∈ D.spare ∪ D.near i, ∃ d : V, ∃ W : List V,
      d ∈ MiddlePorts D i I ∧ W.head? = some a ∧ W.getLast? = some d ∧
      W.Nodup ∧ W.IsChain G.Adj ∧ (∀ x, x ∈ W ↔ x ∈ Middle D i short I)) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  let _ : Nonempty V := ⟨v⟩
  obtain ⟨P,hPne,hPt,hPn,hPc,hPm⟩ :=
    prefix_exists D i short hshort hvw houtA houtB hsep hB hcl hvb
  obtain ⟨a,ha,d,W,hd,hWh,hWt,hWn,hWc,hWm⟩ := hM
  have hWne : W ≠ [] := by intro he; simp [he] at hWh
  have hcuts := cuts_disjoint_A houtA hsep
  have hpw : P.Disjoint W := by
    apply list_disjoint_of_support hPm hWm
    rw [Set.disjoint_left]
    intro x hx hy
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp (initial_middle_disjoint D i short I hiI) hx hy
    · exact Set.disjoint_left.mp hcuts hx (middle_subset D i short I hy)
  have startAdj : G.Adj v a := ha.elim
    (fun h => (D.spare_facts a h).2) (fun h => (D.near_facts i a h).2)
  have linkPW : ∀ a' ∈ P.getLast?, ∀ b' ∈ W.head?, G.Adj a' b' := by
    intro x hx y hy
    have hxv : v = x := by simpa [hPt] using hx
    have hya : a = y := by simpa [hWh] using hy
    exact hxv ▸ hya ▸ startAdj
  have allCovered (x : V) :
      x ∈ P ∨ x ∈ W ∨ ∃ j, terminal = some j ∧ x ∈ D.near j ∪ D.far j := by
    by_cases hxv : x = v
    · exact Or.inl ((hPm x).2 (Or.inr (by simp [hxv])))
    by_cases hxw : x = w
    · exact Or.inl ((hPm x).2 (Or.inr (by simp [hxw])))
    rcases hcover x hxv hxw with hx | hx
    · rcases D.blocks_cover x hx with hs | ⟨j,hj⟩
      · exact Or.inr (Or.inl ((hWm x).2 (Or.inl (Or.inl hs))))
      · have hblock : x ∈ D.near j ∪ D.far j := hj.symm
        by_cases hji : j = i
        · subst j
          rcases initial_core_cover D i short hblock with hp | hm
          · exact Or.inl ((hPm x).2 (Or.inl hp))
          · exact Or.inr (Or.inl ((hWm x).2 (Or.inl (Or.inr hm))))
        · by_cases hjI : j ∈ I
          · exact Or.inr (Or.inl ((hWm x).2 (Or.inr ⟨j,hjI,hblock⟩)))
          · exact Or.inr (Or.inr ⟨j,hrest j hji hjI,hblock⟩)
    · exact Or.inl ((hPm x).2 (Or.inr (by simp [hx])))
  cases terminal with
  | none =>
    refine hamiltonian_of_ordered_blocks [P,W] ?_ ?_ ?_ ?_
    · intro L hL
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
      rcases hL with rfl | rfl
      · exact ⟨hPne,hPn,hPc⟩
      · exact ⟨hWne,hWn,hWc⟩
    · simp [hpw]
    · intro x
      rcases allCovered x with hx | hx | ⟨j,hj,_⟩
      · exact ⟨P,by simp,hx⟩
      · exact ⟨W,by simp,hx⟩
      · cases hj
    · exact List.isChain_cons_cons.mpr ⟨linkPW, by simp⟩
  | some j =>
    have hij : i ≠ j := fun h => hit (congrArg some h.symm)
    obtain ⟨hjI,hj⟩ := hterm j rfl
    obtain ⟨b,hb,T,hTh,hTn,hTc,hTm⟩ := terminal_exists D j hj
    have hTne : T ≠ [] := by intro he; simp [he] at hTh
    have hpt : P.Disjoint T := by
      apply list_disjoint_of_support hPm hTm
      rw [Set.disjoint_left]
      intro x hx hy
      rcases hx with hx | hx
      · exact Set.disjoint_left.mp (block_disjoint D hij)
          (Or.inr (initial_sub D i short hx)) hy
      · exact Set.disjoint_left.mp hcuts hx (block_subset D j hy)
    have hwt : W.Disjoint T :=
      list_disjoint_of_support hWm hTm (middle_terminal_disjoint D i j short I hij hjI)
    have endAdj : G.Adj d b := by
      rcases hd with (hs | hs) | ⟨k,hk,hs⟩
      · exact D.spare_attachment_complete j d b hs hb
      · exact D.cross_attachment_complete hij hs hb
      · have hkj : k ≠ j := fun he => hjI (he ▸ hk)
        exact D.cross_attachment_complete hkj hs hb
    have linkWT : ∀ a' ∈ W.getLast?, ∀ b' ∈ T.head?, G.Adj a' b' := by
      intro x hx y hy
      have hxd : d = x := by simpa [hWt] using hx
      have hyb : b = y := by simpa [hTh] using hy
      exact hxd ▸ hyb ▸ endAdj
    refine hamiltonian_of_ordered_blocks [P,W,T] ?_ ?_ ?_ ?_
    · intro L hL
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
      rcases hL with rfl | rfl | rfl
      · exact ⟨hPne,hPn,hPc⟩
      · exact ⟨hWne,hWn,hWc⟩
      · exact ⟨hTne,hTn,hTc⟩
    · simp [hpw,hpt,hwt]
    · intro x
      rcases allCovered x with hx | hx | ⟨k,hk,hx⟩
      · exact ⟨P,by simp,hx⟩
      · exact ⟨W,by simp,hx⟩
      · have he : j = k := Option.some.inj hk
        exact ⟨T,by simp,(hTm x).2 (he.symm ▸ hx)⟩
    · exact List.isChain_cons_cons.mpr ⟨linkPW, List.isChain_cons_cons.mpr ⟨linkWT, by simp⟩⟩

/-- Assemble the prefix, covered middle, and possible terminal dangling block. -/
theorem hamiltonian_of_h1FarData [DecidableEq V]
    (G : SimpleGraph V) (v w : V) (A B : Set V) (hvw : v ≠ w)
    (houtA : v ∉ A ∧ w ∉ A) (houtB : v ∉ B ∧ w ∉ B)
    (hcover : ∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y)
    (hB : B.Nonempty) (hcl : G.IsClique B)
    (hvb : ∀ x ∈ B, G.Adj v x ∧ G.Adj w x)
    (D : H1FarData G v w A) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  have assemble (i : Fin D.n) (short : Bool) (terminal : Option (Fin D.n))
      (hcore : if short then Dangling D i else ¬ Dangling D i)
      (hit : terminal ≠ some i) (hterm : ∀ j, terminal = some j → Dangling D j)
      (hregular : ∀ j, j ≠ i → terminal ≠ some j → ¬ Dangling D j) :
      ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
    let I := (univ : Finset (Fin D.n)).filter fun j => j ≠ i ∧ terminal ≠ some j
    have hmem (j : Fin D.n) : j ∈ I ↔ j ≠ i ∧ terminal ≠ some j := by simp [I]
    have hI (j : Fin D.n) (hj : j ∈ I) : j ≠ i ∧ ¬ Dangling D j :=
      let hh := (hmem j).mp hj
      ⟨hh.1,hregular j hh.1 hh.2⟩
    have hiI : i ∉ I := fun hi => ((hmem i).mp hi).1 rfl
    have hrest (j : Fin D.n) (hji : j ≠ i) (hjI : j ∉ I) : terminal = some j := by
      by_contra hn
      exact hjI ((hmem j).mpr ⟨hji,hn⟩)
    have hterm' (j : Fin D.n) (hj : terminal = some j) : j ∉ I ∧ Dangling D j :=
      ⟨fun hin => ((hmem j).mp hin).2 hj,hterm j hj⟩
    have hshort (h : short = true) : Dangling D i := by simpa [h] using hcore
    have hM := middle_of_far_data D i I hI short hcore
    have hM' : ∃ a ∈ D.spare ∪ D.near i, ∃ d : V, ∃ W : List V,
        d ∈ MiddlePorts D i I ∧ W.head? = some a ∧ W.getLast? = some d ∧
        W.Nodup ∧ W.IsChain G.Adj ∧ (∀ x, x ∈ W ↔ x ∈ Middle D i short I) := hM
    exact finish_from_middle D i short I terminal hshort hiI hit hrest hterm'
      hvw houtA houtB hcover hsep hB hcl hvb hM'
  rcases choose_dangling_cases D with hnone | ⟨i,hi,honly⟩ | ⟨i,j,hij,hi,hj,honly⟩
  · exact assemble ⟨0,D.positive⟩ false none (hnone _) (by simp)
      (by simp) (fun j _ _ => hnone j)
  · exact assemble i true none hi (by simp) (by simp) (fun j hji _ => honly j hji)
  · refine assemble i true (some j) hi (by simpa using hij.symm) ?_ ?_
    · intro k hk
      obtain rfl := Option.some.inj hk
      exact hj
    · intro k hki hkj
      exact honly k hki (fun h => hkj (congrArg some h.symm))

theorem h1_two_component_step : OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1.H1 :=
  two_component_step_of_far_data hamiltonian_of_h1FarData

end

end OMA.Graph199H1

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1.H1 :=
  OMA.Graph199H1.h1_two_component_step
