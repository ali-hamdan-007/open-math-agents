import Graph199ChvatalSplices
import Graph199MinimumCut

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private abbrev PathSucc (L : List V) (x y : V) : Prop :=
  ∃ P B : List V, L = P ++ x :: y :: B

omit [Fintype V] [DecidableEq V] in
private theorem pathSuccGivesMem {L : List V} {x y : V} (h : PathSucc L x y) :
    x ∈ L ∧ y ∈ L := by
  obtain ⟨P,B,rfl⟩ := h
  simp

omit [Fintype V] in
private theorem pathSuccIndex {L : List V} (hn : L.Nodup) {x y : V}
    (h : PathSucc L x y) : L.idxOf y = L.idxOf x + 1 := by
  obtain ⟨P,B,rfl⟩ := h
  have hp := List.nodup_append.mp hn
  have hx : x ∉ P := fun h => hp.2.2 x h x (by simp) rfl
  have hy : y ∉ P := fun h => hp.2.2 y h y (by simp) rfl
  have hxy : x ≠ y := fun h => (List.nodup_cons.mp hp.2.1).1 (by simp [h])
  rw [List.idxOf_append_of_notMem hx,List.idxOf_append_of_notMem hy]
  simp [List.idxOf_cons_ne _ hxy]

omit [Fintype V] in
private theorem eq_of_same_idx {L : List V} {x y : V}
    (hx : x ∈ L) (hy : y ∈ L) (h : L.idxOf x = L.idxOf y) : x = y := by
  have hx' := List.getElem?_idxOf hx
  have hy' := List.getElem?_idxOf hy
  rw [h,hy'] at hx'
  exact (Option.some.inj hx').symm

omit [Fintype V] in
private theorem pathSuccRightUnique {L : List V} (hn : L.Nodup) {x y z : V}
    (h : PathSucc L x y) (h' : PathSucc L x z) : y = z :=
  eq_of_same_idx (pathSuccGivesMem h).2 (pathSuccGivesMem h').2
    ((pathSuccIndex hn h).trans (pathSuccIndex hn h').symm)

omit [Fintype V] in
private theorem pathSuccLeftUnique {L : List V} (hn : L.Nodup) {x y z : V}
    (h : PathSucc L x z) (h' : PathSucc L y z) : x = y := by
  apply eq_of_same_idx (pathSuccGivesMem h).1 (pathSuccGivesMem h').1
  have hx := pathSuccIndex hn h
  have hy := pathSuccIndex hn h'
  omega

omit [Fintype V] [DecidableEq V] in
private theorem outside_path_list {C : Set V} (hc : (G.induce C).Connected)
    {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ L.head? = some a ∧
      L.getLast? = some b ∧ (∀ x ∈ L, x ∈ C) := by
  obtain ⟨p,hp⟩ := (hc ⟨a,ha⟩ ⟨b,hb⟩).exists_isPath
  let q := p.map (SimpleGraph.Embedding.induce C).toHom
  refine ⟨q.support, ?_, q.isChain_adj_support, ?_, ?_, ?_⟩
  · rw [Walk.support_map]
    exact hp.support_nodup.map Subtype.val_injective
  · rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
    rfl
  · rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
    rfl
  · intro x hx
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨z,_,rfl⟩ := hx
    exact z.property

/-- A vertex separator surrounding an off-path component has at least κ
vertices. -/
theorem longest_chain_attachment_card (L : List V) (C : Set V) (a : V)
    (hC : C.Nonempty) (hdis : ∀ x ∈ C, x ∉ L)
    (hclosed : ∀ x ∈ C, ∀ y ∉ L, G.Adj x y → y ∈ C)
    (ha : a ∈ L) (hna : ∀ x ∈ C, ¬ G.Adj a x)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ x ∈ L ∧ ∃ y ∈ C, G.Adj x y) :
    vertexConnectivity G ≤ S.card := by
  by_contra! hlt
  have hConn := connected_of_card_lt_vertexConnectivity S hlt
  obtain ⟨c,hc⟩ := hC
  have hcs : c ∉ S := fun h => hdis c hc ((hS c).mp h).1
  have has : a ∉ S := by
    intro hs
    obtain ⟨_,hx,hax⟩ := ((hS a).mp hs).2
    exact hna _ hx hax
  let W := ↥((S : Set V)ᶜ)
  let K := G.induce ((S : Set V)ᶜ)
  let c' : W := ⟨c,hcs⟩
  let a' : W := ⟨a,has⟩
  have chain_closed {y : W} (hy : Relation.ReflTransGen K.Adj c' y) : y.val ∈ C := by
    induction hy with
    | refl => exact hc
    | tail _ hxy ih =>
      rename_i x y _
      have he : G.Adj x.val y.val := hxy
      have hyL : y.val ∉ L := fun h => y.property ((hS y.val).mpr ⟨h,x.val,ih,he.symm⟩)
      exact hclosed _ ih _ hyL he
  exact hdis a (chain_closed ((K.reachable_iff_reflTransGen _ _).mp (hConn c' a'))) ha

omit [Fintype V] [DecidableEq V] in
private theorem pathSucc_of_attachment {L : List V} {C : Set V} {x : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hdis : ∀ x ∈ C, x ∉ L) (hx : x ∈ L) (hxc : ∃ c ∈ C, G.Adj x c) :
    ∃ y, PathSucc L x y := by
  obtain ⟨P,B,hL⟩ := List.append_of_mem hx
  obtain ⟨c,hcC,hAdj⟩ := hxc
  cases B with
  | nil =>
    have hl : L.getLast? = some x := by simp [hL]
    exact ((longest_chain_endpoints hn hc hm (hdis c hcC)).2 _ hl hAdj).elim
  | cons y B => exact ⟨y,P,B,hL⟩

omit [Fintype V] [DecidableEq V] in
private theorem pathSucc_not_attachment {L : List V} {C : Set V} {x y : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hs : PathSucc L x y) (hx : ∃ c ∈ C, G.Adj x c) :
    ¬ ∃ d ∈ C, G.Adj y d := by
  intro hy
  obtain ⟨P,B,rfl⟩ := hs
  obtain ⟨c,hcC,hxc⟩ := hx
  obtain ⟨d,hdC,hyd⟩ := hy
  obtain ⟨M,hMn,hMc,hMh,hMl,hMC⟩ := outside_path_list hC hcC hdC
  let A := P ++ [x]
  let D := y :: B
  have hL : A ++ D = P ++ x :: y :: B := by simp [A,D,List.append_assoc]
  have hADn : (A ++ D).Nodup := by rwa [hL]
  have hADc : (A ++ D).IsChain G.Adj := by rwa [hL]
  have hDM : M.Disjoint (A ++ D) := by
    intro z hz hz'
    exact hdis z (hMC z hz) (hL ▸ hz')
  exact longest_chain_no_detour_gap hADn.of_append_left hADn.of_append_right hMn
    hADc.left_of_append hADc.right_of_append hMc hADn.disjoint
    (fun _ ha hm => hDM hm (List.mem_append_left _ ha))
    (fun _ hm hd => hDM hm (List.mem_append_right _ hd))
    (by simp [A]) rfl hMh hMl hxc hyd.symm (by rw [hL]; exact hm)

omit [Fintype V] in
private theorem pathSucc_pair_no_adjacency_aux {L : List V} {C : Set V} {x x' y y' : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hs : PathSucc L x y) (hs' : PathSucc L x' y')
    (hx : ∃ c ∈ C, G.Adj x c) (hx' : ∃ d ∈ C, G.Adj x' d)
    (hind : L.idxOf x < L.idxOf x') :
    ¬ G.Adj y y' := by
  have hney : x' ≠ y := fun he => pathSucc_not_attachment hn hc hm hC hdis hs hx (he ▸ hx')
  have hne : x' ≠ x := fun he => (Nat.ne_of_lt hind) (congrArg L.idxOf he).symm
  obtain ⟨P,B,hP⟩ := hs
  have hmem := (pathSuccGivesMem hs').1
  have hnod : (P ++ x :: y :: B).Nodup := hP ▸ hn
  have hnot : x' ∉ P := by
    intro hp
    have hxP : x ∉ P := fun h =>
      (List.nodup_append.mp hnod).2.2 _ h _ (by simp) rfl
    have hxi : L.idxOf x = P.length := by
      rw [hP,List.idxOf_append_of_notMem hxP]
      simp
    have hl : P.idxOf x' < P.length := List.idxOf_lt_length_iff.mpr hp
    rw [hxi,hP,List.idxOf_append_of_mem hp] at hind
    omega
  have hxB : x' ∈ B := by
    rw [hP,List.mem_append,List.mem_cons,List.mem_cons] at hmem
    exact ((hmem.resolve_left hnot).resolve_left hne).resolve_left hney
  obtain ⟨Q,R,hBR⟩ := List.append_of_mem hxB
  have hR : R ≠ [] := by
    intro he
    have hl : L.getLast? = some x' := by
      rw [hP,hBR,he]
      simp [List.getLast?_cons]
    obtain ⟨d,hd,hdx⟩ := hx'
    exact (longest_chain_endpoints hn hc hm (hdis d hd)).2 _ hl hdx
  cases R with
  | nil => contradiction
  | cons t D =>
    let A := P ++ [x]
    let B' := (y :: Q) ++ [x']
    have hEq : L = (A ++ B') ++ t :: D := by
      simp only [hP,hBR,A,B',List.append_assoc,List.cons_append,List.nil_append]
    have hsT : PathSucc L x' t := by
      refine ⟨P ++ [x,y] ++ Q,D,?_⟩
      simp [hP,hBR,List.append_assoc]
    have he : t = y' := pathSuccRightUnique hn hsT hs'
    obtain ⟨c,hcC,hxc⟩ := hx
    obtain ⟨d,hdC,hxd⟩ := hx'
    obtain ⟨M,hMn,hMc,hMh,hMl,hMC⟩ := outside_path_list hC hcC hdC
    have hdisM : M.Disjoint ((A ++ B') ++ t :: D) :=
      fun z hz hz' => hdis z (hMC z hz) (hEq.symm ▸ hz')
    rw [← he]
    exact longest_chain_no_detour_chord (by simp [A]) (by simp [B'])
      (by change ((y :: Q) ++ [x']).getLast? = some x';
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or])
      rfl hMh hMl (hEq ▸ hn) (hEq ▸ hc) hMn hMc hdisM hxc hxd.symm
      (by rw [← hEq]; exact hm)

/-- A longest path with an outside component forces an independent set of at
least two more vertices than the vertex connectivity. -/
theorem indepNum_at_least_of_longest_outside (L : List V) (a : V) (C : Set V)
    (hhead : L.head? = some a) (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hclosed : ∀ x ∈ C, ∀ y ∉ L, G.Adj x y → y ∈ C) :
    vertexConnectivity G + 2 ≤ G.indepNum := by
  classical
  let S := L.toFinset.filter (fun x => ∃ y ∈ C, G.Adj x y)
  have hS (x : V) : x ∈ S ↔ x ∈ L ∧ ∃ y ∈ C, G.Adj x y := by simp [S]
  have haL : a ∈ L := List.mem_of_mem_head? hhead
  have hna (x : V) (hx : x ∈ C) : ¬ G.Adj a x :=
    (longest_chain_endpoints hn hc hm (hdis x hx)).1 _ hhead
  obtain ⟨c⟩ := hC.nonempty
  have hκ := longest_chain_attachment_card L C a ⟨c.val,c.property⟩ hdis hclosed haL hna S hS
  have hsucc (x : S) : ∃ y, PathSucc L x.val y :=
    pathSucc_of_attachment hn hc hm hdis ((hS x.val).mp x.property).1 ((hS x.val).mp x.property).2
  choose f hf using hsucc
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact pathSuccLeftUnique hn (hf x) (he ▸ hf y)
  let Y := S.attach.image f
  have hY : Y.card = S.card := by simp [Y,card_image_of_injective _ hfi]
  have hfL (x : V) (hx : x ∈ Y) : x ∈ L := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact (pathSuccGivesMem (hf y)).2
  have hfc (x : V) (hx : x ∈ Y) : ¬ G.Adj x c.val := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    intro he
    exact pathSucc_not_attachment hn hc hm hC hdis (hf y) ((hS y.val).mp y.property).2
      ⟨c.val,c.property,he⟩
  have hfa (x : V) (hx : x ∈ Y) : ¬ G.Adj a x := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    obtain ⟨P,B,hPB⟩ := hf y
    obtain ⟨z,hz,haz⟩ := ((hS y.val).mp y.property).2
    apply longest_chain_head_misses_successor P B a y.val (f y) z
    · rwa [← hPB]
    · rwa [← hPB]
    · rwa [← hPB]
    · rw [← hPB]; exact hm
    · rw [← hPB]; exact hdis z hz
    · exact haz
  have hYa : a ∉ Y := by
    intro he
    obtain ⟨x,_,hfx⟩ := mem_image.mp he
    have hidx := pathSuccIndex hn (hf x)
    rw [hfx] at hidx
    have ha0 : L.idxOf a = 0 := by
      cases L with
      | nil => simp at hhead
      | cons h t =>
        have he : h = a := Option.some.inj hhead
        subst h
        simp
    omega
  have hYc : c.val ∉ Y := fun h => hdis c.val c.property (hfL _ h)
  have hYind : G.IsIndepSet (Y : Set V) := by
    intro x hx y hy hne
    obtain ⟨x',_,rfl⟩ := mem_image.mp hx
    obtain ⟨y',_,rfl⟩ := mem_image.mp hy
    have hxc := ((hS x'.val).mp x'.property).2
    have hyc := ((hS y'.val).mp y'.property).2
    rcases lt_trichotomy (L.idxOf x'.val) (L.idxOf y'.val) with h | h | h
    · exact pathSucc_pair_no_adjacency_aux hn hc hm hC hdis (hf x') (hf y') hxc hyc h
    · have hxy : x' = y' := Subtype.ext (eq_of_same_idx
        (pathSuccGivesMem (hf x')).1 (pathSuccGivesMem (hf y')).1 h)
      exact (hne (congrArg f hxy)).elim
    · exact fun he => pathSucc_pair_no_adjacency_aux hn hc hm hC hdis (hf y') (hf x') hyc hxc h he.symm
  have hI : G.IsIndepSet (↑(insert c.val Y) : Set V) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem hYc hYind
    intro x hx
    exact ⟨fun he => hfc x hx he.symm,hfc x hx⟩
  have hca : a ≠ c.val := fun he => hdis c.val c.property (he ▸ haL)
  have haI : a ∉ insert c.val Y := by simp [hca,hYa]
  have hI' : G.IsIndepSet (↑(insert a (insert c.val Y)) : Set V) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem haI hI
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨hna _ c.property,fun h => hna _ c.property h.symm⟩
    · exact ⟨hfa x hx,fun h => hfa x hx h.symm⟩
  have hbig := hI'.card_le_indepNum
  rw [card_insert_of_notMem haI,card_insert_of_notMem hYc,hY] at hbig
  omega

/-- The traceability form of the Chvátal–Erdős theorem. -/
theorem hamiltonian_of_indepNum_le_vertexConnectivity_add_one
    (hG : G.Connected) (hα : G.indepNum ≤ vertexConnectivity G + 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let _ : Nonempty V := hG.nonempty
  obtain ⟨L,hLe,hn,hc,hm⟩ := exists_longest_chain (G := G)
  let a := L.head hLe
  have ha : L.head? = some a := List.head?_eq_some_head hLe
  let p := Walk.ofSupport L hLe hc
  have hp : p.support = L := Walk.support_ofSupport hLe hc
  have hpath : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hp]
  refine ⟨_,_,p,hpath.isHamiltonian_of_mem ?_⟩
  intro x
  rw [hp]
  by_contra hx
  let T := {x | x ∉ L}
  let K := G.induce T
  let q : T := ⟨x,hx⟩
  let i := K.connectedComponentMk q
  let C : Set V := Subtype.val '' i.supp
  have hdis (z : V) (hz : z ∈ C) : z ∉ L := by
    obtain ⟨y,_,rfl⟩ := hz
    exact y.property
  have hclosed (z : V) (hz : z ∈ C) (y : V) (hy : y ∉ L) (he : G.Adj z y) : y ∈ C := by
    obtain ⟨s,hs,rfl⟩ := hz
    let t : T := ⟨y,hy⟩
    have hst : K.Adj s t := he
    exact ⟨t,i.mem_supp_of_adj_mem_supp hs hst,rfl⟩
  have hC : (G.induce C).Connected := by
    let f : i.supp → C := fun x => ⟨x.val.val,x.val,x.property,rfl⟩
    have hinj : Function.Injective f := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : C => x.val) h))
    have hsurj : Function.Surjective f := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    let iso : K.induce i.supp ≃g G.induce C :=
      ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩, by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  have h := indepNum_at_least_of_longest_outside L a C ha hn hc hm hC hdis hclosed
  omega

#print axioms hamiltonian_of_indepNum_le_vertexConnectivity_add_one
#print axioms indepNum_at_least_of_longest_outside
#print axioms longest_chain_attachment_card
#print axioms pathSucc_pair_no_adjacency_aux
end Graph199
