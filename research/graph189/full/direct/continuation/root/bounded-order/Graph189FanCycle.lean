import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.GetD

/-! The index-set crossing argument and cyclic-list construction below are adapted
from @philipsaint's checked proof `Arxiv.2606.03696.bondy_conjecture.variants.one`.
The endpoint selection allows one vertex of degree below the threshold. -/

open SimpleGraph Finset
namespace Graph189FanCycle
variable {V : Type*} {G : SimpleGraph V}

/-- A cyclic list: consecutive entries are adjacent, and so are the last and the first. -/
private def Cyc (G : SimpleGraph V) (c : List V) : Prop :=
  c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b

private lemma rot {c : List V} (hc : Cyc G c) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

private lemma edge_not_mem {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  cases p with
  | nil => simp at hlen
  | @cons _ w _ hadj p' =>
    intro hmem
    rw [Walk.edges_cons, List.mem_cons] at hmem
    have hnd := hp.support_nodup
    rw [Walk.support_cons, List.nodup_cons] at hnd
    rcases hmem with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · subst h2
        have hp' : p'.IsPath := hp.of_cons
        have : p'.length = 0 := by
          rcases p' with _ | ⟨h'', p''⟩
          · rfl
          · exfalso
            have := hp'.support_nodup
            simp at this
        simp [this] at hlen
      · subst h1
        exact hadj.ne rfl
    · exact hnd.1 (Walk.fst_mem_support_of_mem_edges p' h)

private lemma cycle_of_list (c : List V) (hnd : c.Nodup) (hc : Cyc G c) (h3 : 3 ≤ c.length) :
    ∃ x, ∃ Q : G.Walk x x, Q.IsCycle ∧ Q.length = c.length := by
  have hne : c ≠ [] := by
    rintro rfl
    simp at h3
  set W := Walk.ofSupport c hne hc.1
  have hW : W.support = c := Walk.support_ofSupport hne hc.1
  have hWl : W.length = c.length - 1 := Walk.length_ofSupport hne hc.1
  have hpath : W.IsPath := Walk.IsPath.mk' (by rw [hW]; exact hnd)
  have hadj : G.Adj (c.head hne) (c.getLast hne) := by
    refine (?_ : G.Adj (c.getLast hne) (c.head hne)).symm
    apply hc.2
    · exact List.getLast?_eq_some_getLast hne
    · exact List.head?_eq_some_head hne
  refine ⟨c.head hne, Walk.cons hadj W.reverse, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hpath.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    exact edge_not_mem W hpath (by omega)
  · rw [Walk.length_cons, Walk.length_reverse, hWl]
    omega

private lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

private lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

/-- Rotate the low endpoint of a longest path across a second incident edge.
The resulting longest path has both endpoints distinct from the exceptional vertex. -/
private theorem rotate_low {low : V} {first : V} {T : List V}
    (nd : (low :: first :: T).Nodup) (ch : (low :: first :: T).IsChain G.Adj)
    (maximal : ∀ L : List V, L.Nodup → L.IsChain G.Adj → L.length ≤ (low :: first :: T).length)
    {w : V} (ew : G.Adj low w) (diff : w ≠ first) :
    ∃ L : List V, L.Perm (low :: first :: T) ∧ L.IsChain G.Adj ∧
      L.head? ≠ some low ∧ L.getLast? ≠ some low := by
  classical
  have mem : w ∈ T := by
    by_contra h
    have outside : w ∉ low :: first :: T := by simp [ew.ne.symm,diff,h]
    have ext := maximal (w :: low :: first :: T) (nd.cons outside)
      (List.IsChain.cons_of_ne_nil (by simp) ch ew.symm)
    simp at ext
  obtain ⟨A,B,rfl⟩ := List.append_of_mem mem
  let S := low :: first :: A
  let R := w :: B
  change (S ++ R).Nodup at nd
  change (S ++ R).IsChain _ at ch
  have rev : S.reverse.IsChain G.Adj := List.isChain_reverse.mpr
    (ch.left_of_append.imp fun _ _ e => e.symm)
  have chain : (S.reverse ++ R).IsChain G.Adj := by
    apply rev.append ch.right_of_append
    intro a ha b hb
    have av : low = a := by simpa [S] using ha
    have bv : w = b := by simpa [R] using hb
    exact av ▸ bv ▸ ew
  have outside : low ∉ (first :: A) ++ R := (List.nodup_cons.mp nd).1
  have head : (S.reverse ++ R).head? ≠ some low := by
    intro h
    rw [List.head?_append_of_ne_nil _ (by simp [S]),List.head?_reverse] at h
    have last : (first :: A).getLast? = some low := by simpa [S] using h
    exact outside (List.mem_append_left _ (List.mem_of_getLast? last))
  have last : (S.reverse ++ R).getLast? ≠ some low := by
    intro h
    have lastR : R.getLast? = some low := by simpa [R,List.getLast?_append] using h
    exact outside (List.mem_append_right _ (List.mem_of_getLast? lastR))
  exact ⟨_,(List.reverse_perm S).append_right R,chain,head,last⟩

variable [Fintype V] [DecidableEq V]

/-- Select a globally longest path list whose two endpoints avoid `low`. -/
theorem longest_high_ends [DecidableRel G.Adj] (low : V) (atLeastTwo : 2 ≤ G.degree low) :
    ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ 3 ≤ l.length ∧
      l.head? ≠ some low ∧ l.getLast? ≠ some low ∧
      ∀ t : List V, t.Nodup → t.IsChain G.Adj → t.length ≤ l.length := by
  classical
  have count : 1 < (G.neighborFinset low).card := by rw [G.card_neighborFinset_eq_degree]; omega
  obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp count
  have ea := (G.mem_neighborFinset _ _).mp hu
  have eb := (G.mem_neighborFinset _ _).mp hv
  let Good := fun n => ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ L.length = n
  have nd3 : [u,low,v].Nodup := by simp [ea.ne.symm,eb.ne,uv]
  have base : Good 3 := ⟨[u,low,v],nd3,by simpa using And.intro ea.symm eb,rfl⟩
  obtain ⟨L,nd,ch,sz⟩ := Nat.findGreatest_spec (by simpa using nd3.length_le_card) base
  have maximal (t : List V) (tn : t.Nodup) (tc : t.IsChain G.Adj) : t.length ≤ L.length := by
    rw [sz]; exact Nat.le_findGreatest tn.length_le_card (show Good t.length from ⟨t,tn,tc,rfl⟩)
  have three := maximal _ nd3 (show [u,low,v].IsChain G.Adj by simpa using And.intro ea.symm eb)
  change 3 ≤ L.length at three
  have orient (A : List V) (perm : A.Perm L) (ac : A.IsChain G.Adj) (head : A.head? = some low) :
      ∃ t : List V, t.Perm L ∧ t.IsChain G.Adj ∧ t.head? ≠ some low ∧ t.getLast? ≠ some low := by
    cases A with
    | nil => simp at head
    | cons a A =>
      have ae : a = low := by simpa using head
      subst a
      cases A with
      | nil => have e := perm.length_eq; simp at e; omega
      | cons b T =>
        have bound (t : List V) (ht : t.Nodup) (hc : t.IsChain G.Adj) := (maximal t ht hc).trans_eq perm.length_eq.symm
        have rotate (w : V) (hw : G.Adj low w) (dw : w ≠ b) :=
          rotate_low (perm.nodup_iff.mpr nd) ac bound hw dw
        obtain ⟨t,tt,tc,t0,t1⟩ := (show ∃ t : List V, t.Perm (low :: b :: T) ∧ t.IsChain G.Adj ∧
            t.head? ≠ some low ∧ t.getLast? ≠ some low from by
          by_cases e : u = b
          · exact rotate v eb (fun h => uv (e.trans h.symm))
          exact rotate u ea e)
        exact ⟨t,tt.trans perm,tc,t0,t1⟩
  obtain ⟨l,perm,chain,h0,h1⟩ : ∃ l : List V, l.Perm L ∧ l.IsChain G.Adj ∧
      l.head? ≠ some low ∧ l.getLast? ≠ some low := by
    by_cases h0 : L.head? = some low
    · exact orient L (.refl _) ch h0
    by_cases h1 : L.getLast? = some low
    · exact orient L.reverse (List.reverse_perm _) (List.isChain_reverse.mpr (ch.imp fun _ _ e => e.symm)) (by simpa using h1)
    exact ⟨L,.refl _,ch,h0,h1⟩
  exact ⟨l,perm.nodup_iff.mpr nd,chain,three.trans_eq perm.length_eq.symm,h0,h1,
    fun t tn tc => (maximal t tn tc).trans_eq perm.length_eq.symm⟩

/-- If all but one vertex have at least half the order as degree and the exceptional
vertex has two neighbors, a connected graph contains a Hamiltonian cycle. -/
theorem small_cycle [DecidableRel G.Adj] (low : V) (atLeastTwo : 2 ≤ G.degree low)
    (conn : G.Preconnected) (high : ∀ v, v ≠ low → Fintype.card V ≤ 2 * G.degree v) :
    ∃ a, ∃ Q : G.Walk a a, Q.IsHamiltonianCycle := by
  classical
  obtain ⟨l,hlnd,hlch,h3,head,last,hmax⟩ := longest_high_ends low atLeastTwo
  let n := Fintype.card V
  have hl_ne : l ≠ [] := by rintro rfl; simp at h3
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have hmn : l.length ≤ n := hlnd.length_le_card
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hl_ne hlch ((hy).symm))
    simp at this
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hl_ne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch
    simp at this
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  -- the two index sets
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hdq := high q0 (fun eq => head ((List.head?_eq_some_head hl_ne).trans (congrArg some eq)))
  have hdz := high z (fun eq => last ((List.getLast?_eq_some_getLast hl_ne).trans (congrArg some eq)))
  obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∈ T := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint S T := Finset.disjoint_left.mpr hcon
    have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at this
    change m ≤ Fintype.card V at hmn
    omega
  rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
  obtain ⟨hjm, hA⟩ := hjS
  obtain ⟨-, hB⟩ := hjT
  -- the cycle
  set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
  have hperm : c.Perm l := by
    have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
    rw [List.take_append_drop] at this
    exact this
  have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
  have hj1 : j < m := by omega
  have hj2 : j + 1 < m := by omega
  have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
    rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
    simp [List.getElem?_eq_getElem hj1]
  have e2 : (l.drop (j + 1)).reverse.head? = some z := by
    rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
  have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
    rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
      List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
    rfl
  have e4 : c.head? = some q0 := by
    rw [hcdef, List.head?_append, List.head?_take]
    simp [List.head?_eq_some_head hl_ne, q0]
  have hcyc : Cyc G c := by
    refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
    · rw [List.isChain_reverse]
      exact (hlch.drop _).imp (fun a b h => h.symm)
    · intro x hx y hy
      rw [e1] at hx
      rw [e2] at hy
      simp at hx hy
      subst hx hy
      exact hB
    · intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
  -- every vertex lies on the path
  have hall : ∀ w, w ∈ l := by
    intro w
    by_contra hw
    obtain ⟨p⟩ := conn q0 w
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
    have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
    obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
    have hnd' : (d.snd :: c').Nodup := by
      refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
      intro hmem
      exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
    have hch' : (d.snd :: c').IsChain G.Adj := by
      refine List.isChain_cons.2 ⟨?_, hc'ch⟩
      intro y hy
      rw [hc'h] at hy
      simp at hy
      subst hy
      exact (d.adj).symm
    have := hmax _ hnd' hch'
    rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
    omega
  have hmn' : m = n := by
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hall w]
    have h2 := List.toFinset_card_of_nodup hlnd
    rw [h1, Finset.card_univ] at h2
    omega
  obtain ⟨a,Q,hQ,size⟩ := cycle_of_list c hcnd hcyc (by rw [hperm.length_eq]; exact h3)
  exact ⟨a,Q,Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hQ,size.trans (hperm.length_eq.trans hmn')⟩⟩

/-- The degree inside a finite induced subgraph, computed in the ambient type. -/
private theorem internal_degree [DecidableRel G.Adj] (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = (G.neighborFinset v.val ∩ S).card := by
  classical
  let H := G.induce (S : Set V)
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have eq : (H.neighborFinset v).map f = G.neighborFinset v.val ∩ S := by
    ext t
    constructor
    · intro ht
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ht
      exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hu),u.property⟩
    · intro ht
      obtain ⟨adj,inside⟩ := mem_inter.mp ht
      exact mem_map.mpr ⟨⟨t,inside⟩,(H.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp adj),rfl⟩
  have h := congrArg Finset.card eq
  rwa [card_map,H.card_neighborFinset_eq_degree] at h

/-- A finite two-connected induced graph of order at most `2*q` has a spanning
cycle if its vertices except `z` have internal degree at least `q`. Its ambient
walk and support can be passed directly to an exterior-cycle length bound. -/
theorem induced_small_cycle [DecidableRel G.Adj] (S : Finset V) {z : V} (zS : z ∈ S)
    (three : 3 ≤ S.card) {q : ℕ} (size : S.card ≤ 2*q)
    (noncut : ∀ u ∈ S, (G.induce (S.erase u : Set V)).Preconnected)
    (high : ∀ u ∈ S, u ≠ z → q ≤ (G.neighborFinset u ∩ S).card) :
    ∃ a, ∃ Q : G.Walk a a, Q.IsCycle ∧ (∀ v ∈ Q.support, v ∈ S) ∧ Q.length = S.card := by
  classical
  let H := G.induce (S : Set V)
  let Z : S := ⟨z,zS⟩
  have conn : H.Preconnected := by
    intro a b
    have few : ({a.val,b.val} : Finset V).card < S.card :=
      (card_insert_le _ _).trans_lt (by simp; omega)
    obtain ⟨x,xS,sep⟩ := exists_mem_notMem_of_card_lt_card few
    have ae : a.val ∈ S.erase x := mem_erase.mpr ⟨fun e => sep (by simp [e]),a.property⟩
    have be : b.val ∈ S.erase x := mem_erase.mpr ⟨fun e => sep (by simp [e]),b.property⟩
    let f := (G.induceHomOfLE (show (S.erase x : Set V) ⊆ S from fun _ h => (mem_erase.mp h).2)).toHom
    exact ((noncut x xS) ⟨_,ae⟩ ⟨_,be⟩).map f
  have alternate (u : V) (uS : u ∈ S) (uz : u ≠ z) : ∃ a ∈ S, a ≠ u ∧ G.Adj z a := by
    let D := S.erase u
    have width : 1 < Fintype.card D := by rw [Fintype.card_coe,card_erase_of_mem uS]; omega
    let _ : Nontrivial D := Fintype.one_lt_card_iff_nontrivial.mp width
    let z' : D := ⟨z,mem_erase.mpr ⟨uz.symm,zS⟩⟩
    obtain ⟨v,adj⟩ := (noncut _ uS).exists_adj_of_nontrivial z'
    exact ⟨v.val,(mem_erase.mp v.property).2,(mem_erase.mp v.property).1,adj⟩
  obtain ⟨u,uS,uz⟩ := exists_mem_ne (show 1 < S.card by omega) z
  obtain ⟨a,aS,_,za⟩ := alternate u uS uz
  obtain ⟨b,bS,ba,zb⟩ := alternate a aS za.ne.symm
  have minimum : 2 ≤ H.degree Z := by
    rw [internal_degree S Z]
    exact one_lt_card.mpr ⟨a,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr za,aS⟩,
      b,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr zb,bS⟩,ba.symm⟩
  have deg (v : S) (vz : v ≠ Z) : Fintype.card S ≤ 2*H.degree v := by
    rw [Fintype.card_coe,internal_degree]
    have := high v.val v.property (fun eq => vz (Subtype.ext eq))
    omega
  obtain ⟨a,Q,hQ⟩ := small_cycle Z minimum conn deg
  let f := (Embedding.induce (G:=G) (S : Set V)).toHom
  refine ⟨f a,Q.map f,hQ.isCycle.map Subtype.val_injective,?_,?_⟩
  · intro u hu
    rw [Walk.support_map f Q] at hu
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hu
    exact v.property
  exact (Walk.length_map f Q).trans (hQ.length_eq.trans (Fintype.card_coe S))

end Graph189FanCycle
#print axioms Graph189FanCycle.longest_high_ends
#print axioms Graph189FanCycle.small_cycle
#print axioms Graph189FanCycle.induced_small_cycle
