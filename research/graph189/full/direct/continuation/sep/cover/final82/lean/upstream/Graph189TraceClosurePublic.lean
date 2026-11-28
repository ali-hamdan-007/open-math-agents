module
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup

public section
namespace Graph189
open SimpleGraph Finset

private theorem append_chain {V : Type*} {G : SimpleGraph V} {L R : List V}
    {a b : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (ha : L.getLast? = some a) (hb : R.head? = some b) (h : G.Adj a b) :
    (L ++ R).IsChain G.Adj := by
  apply hl.append hr
  intro x hx y hy
  rw [ha] at hx
  rw [hb] at hy
  have hax : a = x := by simpa using hx
  have hby : b = y := by simpa using hy
  exact hax ▸ hby ▸ h

private theorem reverse_chain {V : Type*} {G : SimpleGraph V} {L : List V}
    (h : L.IsChain G.Adj) : L.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (h.imp fun _ _ h => h.symm)

private theorem split_at_pair {V : Type*} (l : List V) (i : ℕ) (hi : i + 1 < l.length) :
    ∃ P Q, l = P ++ l[i]'(by omega) :: l[i + 1] :: Q := by
  refine ⟨l.take i, l.drop (i + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega : i < l.length), List.drop_eq_getElem_cons hi]

private theorem trace_of_list {V : Type*} [DecidableEq V] {G : SimpleGraph V} (l : List V)
    (hn : l.Nodup) (hc : l.IsChain G.Adj) (hall : ∀ z : V, z ∈ l) (hne : l ≠ []) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hc
  have hs : p.support = l := Walk.support_ofSupport hne hc
  exact ⟨_, _, p, (Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun z => by
    rw [hs]
    exact hall z)⟩

private theorem trace_of_permuted_chain {V : Type*} [DecidableEq V] {G : SimpleGraph V} {l W : List V}
    (hn : l.Nodup) (hall : ∀ z : V, z ∈ l) (h : W.Perm l) (hc : W.IsChain G.Adj)
    (x : V) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hm (z : V) : z ∈ W := h.mem_iff.mpr (hall z)
  exact trace_of_list W (h.nodup_iff.mpr hn) hc hm (List.ne_nil_of_mem (hm x))

private theorem augmented_chain_excluding {V : Type*} {G : SimpleGraph V} {l : List V}
    {x y : V} (hc : l.IsChain (G ⊔ edge x y).Adj) (h : x ∉ l ∨ y ∉ l) :
    l.IsChain G.Adj := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b P Q he
  have ha : a ∈ l := by rw [he]; simp
  have hb : b ∈ l := by rw [he]; simp
  have hab := List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hab with hab | hab
  · exact hab
  · have hr := (edge_adj x y a b).mp hab
    rcases hr.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (h.elim (fun hn => hn ha) (fun hn => hn hb)).elim
    · exact (h.elim (fun hn => hn hb) (fun hn => hn ha)).elim

/-- Repair at an edge within the left path by reversing its trailing piece. -/
private theorem repair_left {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : L = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  let L₁ := P ++ [u]
  let L₂ := v :: Q
  have hl12 : L = L₁ ++ L₂ := by simpa [L₁,L₂,List.append_assoc] using hcut
  have hl₁ : L₁.IsChain G.Adj := (hl12 ▸ hl).left_of_append
  have hl₂ : L₂.IsChain G.Adj := (hl12 ▸ hl).right_of_append
  have hx₂ : L₂.getLast? = some x := by
    rw [hl12, List.getLast?_append_of_ne_nil _ (by simp [L₂])] at hx
    exact hx
  have hv₂ : L₂.head? = some v := by simp [L₂]
  have hrevH : L₂.reverse.head? = some x := by rwa [List.head?_reverse]
  have hrevL : L₂.reverse.getLast? = some v := by rwa [List.getLast?_reverse]
  have hlast : L₁.getLast? = some u := by simp [L₁]
  refine ⟨L₁ ++ (L₂.reverse ++ R), ?_, ?_⟩
  · apply (((List.reverse_perm L₂).append_right R).append_left L₁).trans
    exact List.Perm.of_eq ((List.append_assoc L₁ L₂ R).symm.trans
      (congrArg (· ++ R) hl12.symm))
  · have hjoin := append_chain (reverse_chain hl₂) hr hrevL hy hyv.symm
    apply append_chain hl₁ hjoin hlast _ hxu.symm
    simp [hrevH]

/-- Repair at an edge within the right path by reflecting both paths. -/
private theorem repair_right {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : R = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  have hy' : R.reverse.getLast? = some y := by rwa [List.getLast?_reverse]
  have hx' : L.reverse.head? = some x := by rwa [List.head?_reverse]
  have hcut' : R.reverse = Q.reverse ++ v :: u :: P.reverse := by
    rw [hcut]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  obtain ⟨W, hW, hc⟩ :=
    repair_left (reverse_chain hr) (reverse_chain hl) hy' hx' hyv hxu hcut'
  refine ⟨W, hW.trans ?_, hc⟩
  rw [← List.reverse_append]
  exact List.reverse_perm _

private theorem split_closure {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (P Q : List V) (hn : (P ++ x :: y :: Q).Nodup)
    (hc : (P ++ x :: y :: Q).IsChain (G ⊔ edge x y).Adj)
    (hall : ∀ z : V, z ∈ P ++ x :: y :: Q) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let L := P ++ [x]
  let R := y :: Q
  let l := L ++ R
  have hLRe : l = P ++ x :: y :: Q := by simp [l,L,R,List.append_assoc]
  rw [← hLRe] at hn hc hall
  have hno_x : x ∉ R := by
    intro h
    exact (List.nodup_append.mp hn).2.2 x (by simp [L]) x h rfl
  have hno_y : y ∉ L := by
    intro h
    exact (List.nodup_append.mp hn).2.2 y h y (by simp [R]) rfl
  have hl := augmented_chain_excluding (x := x) (y := y) hc.left_of_append (Or.inr hno_y)
  have hr := augmented_chain_excluding (x := x) (y := y) hc.right_of_append (Or.inl hno_x)
  have hx : L.getLast? = some x := by simp [L]
  have hy : R.head? = some y := by simp [R]
  have hLe : L ≠ [] := by simp [L]
  have hRe : R ≠ [] := by simp [R]
  let s := L.head hLe
  let t := R.getLast hRe
  have hs : L.head? = some s := List.head?_eq_some_head hLe
  have ht : R.getLast? = some t := List.getLast?_eq_some_getLast hRe
  have hst : l.head? = some s := by simp [l,hs]
  have htt : l.getLast? = some t := by simp [l,ht]
  by_cases hxt : G.Adj x t
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm R).append_left L) _ x
    apply append_chain hl (reverse_chain hr) hx _ hxt
    rwa [List.head?_reverse]
  by_cases hys : G.Adj y s
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm L).append_right R) _ x
    apply append_chain (reverse_chain hl) hr _ hy hys.symm
    rwa [List.getLast?_reverse]
  have hlen : l.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hn]
    have he : l.toFinset = univ := by ext z; simp [hall]
    simp [he]
  let I := Fin (l.length - 1)
  let u (i : I) : V := l[i.val]'(by have := i.isLt; omega)
  let v (i : I) : V := l[i.val+1]'(by have := i.isLt; omega)
  let S : Finset I := univ.filter fun i => G.Adj x (u i)
  let T : Finset I := univ.filter fun i => G.Adj y (v i)
  have hS : G.degree x ≤ S.card := by
    have hsub : G.neighborFinset x ⊆ S.image u := by
      intro z hz
      have hzx := (mem_neighborFinset G x z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hjlt : j < l.length - 1 := by
        by_contra! hh
        have hj' : j + 1 = l.length := by omega
        have hz : l[j] = t := by
          have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
          have hget : l.getLast hlne = t := List.getLast_of_getLast?_eq_some htt
          rw [List.getLast_eq_getElem] at hget
          have he : j = l.length - 1 := by omega
          exact he ▸ hget
        exact hxt (hz ▸ hzx)
      refine mem_image.mpr ⟨⟨j,hjlt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact hzx
    exact (card_le_card hsub).trans card_image_le
  have hT : G.degree y ≤ T.card := by
    have hsub : G.neighborFinset y ⊆ T.image v := by
      intro z hz
      have hzy := (mem_neighborFinset G y z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hj0 : 0 < j := by
        by_contra! hh
        have he : j = 0 := by omega
        have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
        have hget : l.head hlne = s := List.head_of_head?_eq_some hst
        rw [List.head_eq_getElem] at hget
        subst j
        exact hys (hget ▸ hzy)
      have hjlt : j - 1 < l.length - 1 := by omega
      let i : I := ⟨j - 1, hjlt⟩
      have hi : v i = l[j] := by
        change l[j - 1 + 1]'(by omega) = l[j]
        congr 1
        omega
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi.symm ▸ hzy⟩, hi⟩
    exact (card_le_card hsub).trans card_image_le
  have hpidx : P.length < l.length - 1 := by rw [hLRe]; simp
  let i₀ : I := ⟨P.length, hpidx⟩
  have hu₀ : u i₀ = x := by
    change (L ++ R)[P.length]'(by simp [L, R]) = x
    rw [List.getElem_append_left (by simp [L]), List.getElem_append_right le_rfl]
    simp
  have hv₀ : v i₀ = y := by
    change (L ++ R)[P.length + 1]'(by simp [L, R]) = y
    rw [List.getElem_append_right (by simp [L])]
    simp [L, R]
  have hout : i₀ ∉ S ∪ T := by
    simp [S,T,hu₀,hv₀]
  have hcap : (S ∪ T).card < l.length - 1 := by
    have hne : S ∪ T ≠ (univ : Finset I) := fun h => hout (h ▸ mem_univ _)
    have hh := card_lt_card (ssubset_univ_iff.mpr hne)
    simpa [I] using hh
  obtain ⟨i, hiS, hiT⟩ : ∃ i, i ∈ S ∧ i ∈ T := by
    by_contra! h
    have hdis : Disjoint S T := disjoint_left.mpr h
    have hcard := card_union_of_disjoint hdis
    omega
  have hxu : G.Adj x (u i) := (mem_filter.mp hiS).2
  have hyv : G.Adj y (v i) := (mem_filter.mp hiT).2
  have hin : i.val ≠ P.length := by
    intro h
    have hi0 : i = i₀ := Fin.ext h
    exact hout (mem_union_left _ (hi0 ▸ hiS))
  have hit := i.isLt
  have hLv : L.length = P.length + 1 := by simp [L]
  rcases lt_or_gt_of_ne hin with hbefore | hafter
  · have hixy : i.val + 1 < L.length := by omega
    obtain ⟨A,B,hAB⟩ := split_at_pair L i.val hixy
    have hu : u i = L[i.val]'(by omega) := List.getElem_append_left (by omega)
    have hv : v i = L[i.val+1] := List.getElem_append_left hixy
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_left hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
  · let j := i.val - L.length
    have hlen' : l.length = L.length + R.length := List.length_append
    have hj : j + 1 < R.length := by dsimp [j]; omega
    obtain ⟨A,B,hAB⟩ := split_at_pair R j hj
    have hu : u i = R[j]'(by omega) := List.getElem_append_right (by omega)
    have hv : v i = R[j+1] := by
      unfold v
      change (L ++ R)[i.val+1] = R[j+1]
      rw [List.getElem_append_right (by omega)]
      congr 1
      dsimp [j]
      omega
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_right hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x

/-- Hamiltonian-path closure at a nonedge whose end degrees sum to at least n−1. -/
theorem traceable_of_sup_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (_hne : x ≠ y) (_hxy : ¬ G.Adj x y)
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hpath : ∃ a b : V, ∃ p : (G ⊔ edge x y).Walk a b, p.IsHamiltonian) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a,b,p,hp⟩ := hpath
  let l := p.support
  have hn := hp.isPath.support_nodup
  have hall := hp.mem_support
  have hc := p.isChain_adj_support
  by_cases hG : l.IsChain G.Adj
  · exact trace_of_list l hn hG hall p.support_ne_nil
  obtain ⟨i, hi, hbad⟩ := List.exists_not_getElem_of_not_isChain hG
  obtain ⟨P,Q,he⟩ := split_at_pair l i hi
  have hu : (G ⊔ edge x y).Adj l[i] l[i+1] :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hu with h | h
  · exact (hbad h).elim
  have hh := (edge_adj x y _ _).mp h
  rcases hh.1 with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy] at he
    exact split_closure hd P Q (he ▸ hn) (he ▸ hc) (he ▸ hall)
  · rw [hx,hy] at he
    have hc' : l.IsChain (G ⊔ edge y x).Adj := by simpa only [edge_comm y x] using hc
    exact split_closure (by omega) P Q (he ▸ hn) (he ▸ hc') (he ▸ hall)

#print axioms traceable_of_sup_edge
end Graph189
