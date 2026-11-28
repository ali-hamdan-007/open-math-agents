import Graph189UpstreamBondy

open SimpleGraph
namespace Graph189FanLinkage
variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- A simple link meets the two terminal sets only at the corresponding ends. -/
structure Link (G : SimpleGraph V) (A B : Set V) (L : List V) : Prop where
  nodup : L.Nodup
  chain : L.IsChain G.Adj
  fromA : ∃ a ∈ A, L.head? = some a
  toB : ∃ b ∈ B, L.getLast? = some b
  onlyA : ∀ x ∈ L, x ∈ A → L.head? = some x
  onlyB : ∀ x ∈ L, x ∈ B → L.getLast? = some x

private theorem Link.reverse {L : List V} (h : Link G A B L) : Link G B A L.reverse := by
  refine ⟨List.nodup_reverse.mpr h.nodup,List.isChain_reverse.mpr (h.chain.imp fun _ _ e => e.symm),?_,?_,?_,?_⟩
  · simpa using h.toB
  · simpa using h.fromA
  · intro x hx b
    simpa using h.onlyB x (List.mem_reverse.mp hx) b
  · intro x hx a
    simpa using h.onlyA x (List.mem_reverse.mp hx) a

/-- Exchange a prefix at the first intersection. The initial end of the new link
comes from the middle path, and its terminal end is the old link's terminal end. -/
private theorem splice {I J U T : List V} {z : V}
    (hm : Link G A B (I ++ z :: J)) (hp : Link G A B (U ++ z :: T))
    (fresh : I.Disjoint (U ++ z :: T)) :
    Link G A B (I ++ z :: T) ∧ (I ++ z :: T).head? = (I ++ z :: J).head? ∧
      (I ++ z :: T).getLast? = (U ++ z :: T).getLast? := by
  have head : (I ++ z :: T).head? = (I ++ z :: J).head? := by simp [List.head?_append]
  have last : (I ++ z :: T).getLast? = (U ++ z :: T).getLast? := by simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil z T)]
  refine ⟨⟨hm.nodup.of_append_left.append hp.nodup.of_append_right (fun a ha h => fresh ha (List.mem_append_right _ h)),
    List.isChain_append.mpr ⟨hm.chain.left_of_append,hp.chain.right_of_append,
      (List.isChain_append.mp hm.chain).2.2⟩,?_,?_,?_,?_⟩,head,last⟩
  · rw [head]; exact hm.fromA
  · rw [last]; exact hp.toB
  · intro v hv a
    rw [head]
    rcases List.mem_append.mp hv with hi|hz
    · exact hm.onlyA v (List.mem_append_left _ hi) a
    rcases List.mem_cons.mp hz with rfl|ht
    · exact hm.onlyA v (by simp) a
    have he := hp.onlyA v (by simp [ht]) a
    let W := U ++ [z]
    have eq : W ++ T = U ++ z :: T := by simp [W]
    have wn : W ≠ [] := by simp [W]
    rw [←eq,List.head?_append_of_ne_nil _ wn] at he
    have nd : (W ++ T).Nodup := eq ▸ hp.nodup
    exact (nd.disjoint (List.mem_of_mem_head? he) ht).elim
  · intro v hv b
    rw [last]
    rcases List.mem_append.mp hv with hi|ht
    · have he := hm.onlyB v (List.mem_append_left _ hi) b
      have vj : v ∈ z :: J := List.mem_of_getLast? (by simpa only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil z J)] using he)
      exact (hm.nodup.disjoint hi vj).elim
    exact hp.onlyB v (List.mem_append_right _ ht) b

private theorem force_hit [Fintype V] [DecidableEq V] {M P Q : List V} (hm : Link G A B M) (hp : Link G A B P)
    (hq : Link G A B Q) (dis : P.Disjoint Q) (hit : ∃ z ∈ M, z ∈ P ∨ z ∈ Q) :
    ∃ U W : List V, Link G A B U ∧ Link G A B W ∧ U.Disjoint W ∧
      (U.head? = M.head? ∨ W.head? = M.head?) ∧ U.getLast? = P.getLast? ∧ W.getLast? = Q.getLast? := by
  obtain ⟨I,z,J,rfl,meets,first⟩ := OMA.BondyK.exists_first _ M hit
  have freshP : I.Disjoint P := fun a ai ap => first a ai (Or.inl ap)
  have freshQ : I.Disjoint Q := fun a ai aq => first a ai (Or.inr aq)
  rcases meets with zp|zq
  · obtain ⟨U,T,rfl⟩ := List.append_of_mem zp
    obtain ⟨path,head,last⟩ := splice hm hp freshP
    refine ⟨_,_,path,hq,?_,Or.inl head,last,rfl⟩
    intro a ha aq
    exact (List.mem_append.mp ha).elim (fun ai => freshQ ai aq) (fun at_ => dis (List.mem_append_right _ at_) aq)
  · obtain ⟨U,T,rfl⟩ := List.append_of_mem zq
    obtain ⟨path,head,last⟩ := splice hm hq freshQ
    refine ⟨_,_,hp,path,?_,Or.inr head,rfl,last⟩
    intro a ap ha
    exact (List.mem_append.mp ha).elim (fun ai => freshP ai ap) (fun at_ => dis ap (List.mem_append_right _ at_))

/-- Two disjoint trimmed links can be chosen to include both ends of a third
trimmed link, without prescribing which of the two pairs these end vertices. -/
theorem force_ends [Fintype V] [DecidableEq V] {M P Q : List V} (hm : Link G A B M) (hp : Link G A B P)
    (hq : Link G A B Q) (dis : P.Disjoint Q) :
    ∃ U W : List V, Link G A B U ∧ Link G A B W ∧ U.Disjoint W ∧
      (U.head? = M.head? ∨ W.head? = M.head?) ∧ (U.getLast? = M.getLast? ∨ W.getLast? = M.getLast?) := by
  classical
  by_cases hit : ∃ z ∈ M, z ∈ P ∨ z ∈ Q
  · obtain ⟨U,W,hu,hw,uw,heads,_,_⟩ := force_hit hm hp hq dis hit
    obtain ⟨a,_,ma⟩ := hm.fromA
    have again : ∃ z ∈ M.reverse, z ∈ U.reverse ∨ z ∈ W.reverse := by
      refine ⟨a,List.mem_reverse.mpr (List.mem_of_mem_head? ma),?_⟩
      exact heads.imp (fun e => List.mem_reverse.mpr (List.mem_of_mem_head? (e.trans ma)))
        (fun e => List.mem_reverse.mpr (List.mem_of_mem_head? (e.trans ma)))
    have revDis : U.reverse.Disjoint W.reverse := fun a hu hw => uw (List.mem_reverse.mp hu) (List.mem_reverse.mp hw)
    obtain ⟨X,Y,hx,hy,xy,starts,lastX,lastY⟩ := force_hit hm.reverse hu.reverse hw.reverse revDis again
    refine ⟨X.reverse,Y.reverse,hx.reverse,hy.reverse,fun _ h k => xy (List.mem_reverse.mp h) (List.mem_reverse.mp k),?_,?_⟩
    · simpa only [List.head?_reverse,lastX,lastY,List.getLast?_reverse] using heads
    · simpa using starts
  · exact ⟨M,Q,hm,hq,fun z hz hq => hit ⟨z,hz,Or.inr hq⟩,Or.inl rfl,Or.inl rfl⟩

private theorem of_trimmed [DecidableEq V] {A B : Finset V} {L : List V}
    (p : OMA.BondyK.ABP G A B L) (apartA : ∀ x ∈ L.tail, x ∉ A)
    (apartB : ∀ x ∈ L.dropLast, x ∉ B) : Link G (A : Set V) B L := by
  obtain ⟨nd,ch,start,stop⟩ := p
  refine ⟨nd,ch,start,stop,?_,?_⟩
  · intro x hx xa
    cases L with
    | nil => simp at hx
    | cons a T =>
      rcases List.mem_cons.mp hx with rfl|h
      · rfl
      exact (apartA x h xa).elim
  · intro x hx xb
    obtain ⟨z,_,ze⟩ := stop
    have nn : L ≠ [] := List.ne_nil_of_mem hx
    have last : L.getLast nn = z := Option.some.inj ((List.getLast?_eq_some_getLast nn).symm.trans ze)
    have all := L.dropLast_append_getLast nn
    have pos : x ∈ L.dropLast ++ [L.getLast nn] := by rw [all]; exact hx
    rcases List.mem_append.mp pos with hd|hl
    · exact (apartB x hd xb).elim
    have xz : x = z := (List.mem_singleton.mp hl).trans last
    exact xz ▸ ze

/-- In a two-connected finite graph, two trimmed links between two sets of at
least two vertices can be chosen to meet both endpoint requirements of the
specified middle path. The links remain vertex-disjoint including their ends. -/
theorem two_anchored_links [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (two : G.IsKConnected 2) (A B : Finset V) (wideA : 2 ≤ A.card) (wideB : 2 ≤ B.card)
    {M : List V} (middle : Link G (A : Set V) B M) :
    ∃ U W : List V, Link G (A : Set V) B U ∧ Link G (A : Set V) B W ∧ U.Disjoint W ∧
      (U.head? = M.head? ∨ W.head? = M.head?) ∧ (U.getLast? = M.getLast? ∨ W.getLast? = M.getLast?) := by
  classical
  obtain ⟨P,links,apart⟩ := OMA.BondyK.menger_trim (G:=G) A B 2 (by
    intro S barrier
    by_contra! small
    obtain ⟨a,aA,offA⟩ := Finset.exists_mem_notMem_of_card_lt_card (small.trans_le wideA)
    obtain ⟨b,bB,offB⟩ := Finset.exists_mem_notMem_of_card_lt_card (small.trans_le wideB)
    obtain ⟨q,hq⟩ := (two.2 S small).exists_isPath (⟨a,offA⟩ : {v : V | v ∉ S}) ⟨b,offB⟩
    obtain ⟨z,hz,zS⟩ := barrier (q.support.map Subtype.val) ⟨hq.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr q.isChain_adj_support,
      ⟨a,aA,by rw [←q.cons_tail_support,List.map_cons,List.head?_cons]⟩,
      ⟨b,bB,by rw [List.getLast?_map,List.getLast?_eq_some_getLast q.support_ne_nil,q.getLast_support]; rfl⟩⟩
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
    exact v.property zS)
  have link (i : Fin 2) := of_trimmed (links i).1 (links i).2.1 (links i).2.2
  exact force_ends middle (link 0) (link 1) (fun v hv other => apart 0 1 (by decide) v hv other)

end Graph189FanLinkage
#print axioms Graph189FanLinkage.force_ends

#print axioms Graph189FanLinkage.two_anchored_links
