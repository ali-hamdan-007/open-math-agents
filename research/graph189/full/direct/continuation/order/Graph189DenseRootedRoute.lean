import Graph189SidePathDegree

open SimpleGraph Finset
namespace Graph189DenseRootedRoute
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/- The Ore crossing-chord count and list rotation are adapted from the R2
proof by @carl2sheriff, including list helpers from @philipsaint. -/
private lemma rot {c : List V} (hc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) {q : V} (hq : q ∈ c) :
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

private lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

private lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

/-- A prescribed vertex starts a spanning path at Dirac's half-degree threshold. -/
theorem from_vertex [Nontrivial V] [DecidableRel G.Adj] (start : V) {d : ℕ}
    (minimum : ∀ v, d≤G.degree v) (order : Fintype.card V≤2*d) :
    ∃ y, ∃ q : G.Walk start y, q.IsHamiltonian := by
  classical
  obtain ⟨a,b,p,hp⟩ := Graph189PortPath.of_degree minimum (by omega)
  let l := p.support
  have hne : l≠[] := p.support_ne_nil
  have hlnd : l.Nodup := hp.isPath.support_nodup
  have hlch : l.IsChain G.Adj := p.isChain_adj_support
  let q0 := l.head hne
  let z := l.getLast hne
  have ext_head (y : V) (_ : G.Adj q0 y) : y∈l := hp.mem_support y
  have ext_last (y : V) (_ : G.Adj z y) : y∈l := hp.mem_support y
  have size : l.length=Fintype.card V := hp.length_support
  have h2 : 2≤l.length := size.trans_ge (Fintype.one_lt_card (α:=V))
  have hl_ne := hne
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  have htwo : 2 ≤ m := h2
  have hneEnds : q0 ≠ z := by
    intro he
    have ieq : l[0]'(by omega) = l[m-1]'(by omega) := by
      rw [← List.getD_eq_getElem (d := q0), ← List.getD_eq_getElem (d := q0), hq0, hz]
      exact he
    have hh := hlnd.getElem_inj_iff.mp ieq
    omega
  -- The two index sets of possible crossing chords.
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
  obtain ⟨j,hjS,hjT⟩ : ∃ j, j∈S ∧ j∈T := by
    by_contra! dis
    have sep := Finset.disjoint_left.mpr dis
    have sub : S∪T⊆range (m-1) := union_subset (filter_subset _ _) (filter_subset _ _)
    have count := card_le_card sub
    rw [card_union_of_disjoint sep,card_range] at count
    have left := minimum q0
    have right := minimum z
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
  have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
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
  obtain ⟨v,perm,chain,head⟩ := rot hcyc (hperm.mem_iff.mpr (hp.mem_support start))
  have ne : v≠[] := by rintro rfl; simp at head
  let q := Walk.ofSupport v ne chain
  have supp : q.support=v := Walk.support_ofSupport ne chain
  have path : q.IsPath := Walk.IsPath.mk' (by rw [supp]; exact perm.nodup_iff.mpr hcnd)
  have ham : q.IsHamiltonian := path.isHamiltonian_of_mem (fun w => by
    rw [supp]
    exact (perm.trans hperm).mem_iff.mpr (hp.mem_support w))
  have ident : v.head ne=start := by simpa [List.head?_eq_some_head ne] using head
  subst start
  exact ⟨_,q,ham⟩

#print axioms from_vertex
end Graph189DenseRootedRoute
