import Mathlib.Data.List.GetD
import Graph189PortPath

open SimpleGraph Finset
namespace Graph189SidePathDegree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/- The following path-rotation and Ore count are from the original R2 reduction
by @carl2sheriff, with the list helpers adapted there from @philipsaint.
See Graph189ParentAssembly.lean, section Paths, through lemma4. -/
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

/-- Existence of a longest path, as a nodup chain list. -/
private lemma exists_longest [Nonempty V] [DecidableRel G.Adj] :
    ∃ l : List V, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj ∧
      ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = k
  have h1 : PP 1 := ⟨[v0], ⟨by simp, List.isChain_singleton _⟩, rfl⟩
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos
  set M := Nat.findGreatest PP (Fintype.card V)
  obtain ⟨l, ⟨hlnd, hlch⟩, hlM⟩ : PP M := Nat.findGreatest_spec hpos h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ M :=
    fun l' h1 h2 => Nat.le_findGreatest h1.length_le_card ⟨l', ⟨h1, h2⟩, rfl⟩
  have hM1 : 1 ≤ M := Nat.le_findGreatest hpos h1
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp at hlM
    omega
  exact ⟨l, hl_ne, hlnd, hlch, fun l' a b => hlM ▸ hmax l' a b⟩

/-- Lemma 4 (Ore cycle on a longest path). -/
private lemma lemma4 [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (h2 : 2 ≤ l.length) :
    (∀ y, G.Adj (l.head hne) y → y ∈ l) ∧ (∀ y, G.Adj (l.getLast hne) y → y ∈ l) ∧
      G.degree (l.head hne) + G.degree (l.getLast hne) + 1 ≤ l.length ∧
      (∀ j, j + 1 < l.length → G.Adj (l.head hne) (l.getD (j + 1) (l.head hne)) →
        ¬ G.Adj (l.getD j (l.head hne)) (l.getLast hne)) ∧
      G.degree (l.head hne) ≤ ((Finset.range (l.length - 1)).filter
        (fun j => G.Adj (l.head hne) (l.getD (j + 1) (l.head hne)))).card ∧
      G.degree (l.getLast hne) ≤ ((Finset.range (l.length - 1)).filter
        (fun j => G.Adj (l.getD j (l.head hne)) (l.getLast hne))).card := by
  classical
  set n := Fintype.card V with hn
  have hlnd := hnd
  have hlch := hch
  set q0 := l.head hne
  set z := l.getLast hne
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hne hlch ((hy).symm))
    simp only [List.length_cons] at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hne] at hx
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
    simp only [List.length_append, List.length_singleton] at this
    omega
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
  have hdisj : ∀ j, j ∈ S → j ∈ T → False := by
    intro j hjS hjT
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
    -- every vertex lies on the path
    have hall : ∀ w, w ∈ l := by
      intro w
      by_contra hw
      obtain ⟨p⟩ := hconn q0 w
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
    omega
  have hdisj' : Disjoint S T := Finset.disjoint_left.mpr (fun j h1 h2 => hdisj j h1 h2)
  have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj', Finset.card_range] at hcard
  refine ⟨ext_head, ext_last, by omega, ?_, hS, hT⟩
  intro j hj hA hB
  apply hdisj j
  · simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hA⟩
  · simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hB⟩

variable [DecidableRel G.Adj]

/-- A connected graph with minimum degree d has a longest path on at
least min(n,2d+1) vertices. The Ore count is from the accepted reduction R2. -/
theorem longest_order (con : G.Connected) {d : ℕ} (positive : 1≤d) (min : ∀ u, d≤G.degree u) :
    ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧ (∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length≤p.length) ∧
      (p.support.length=Fintype.card V ∨ 2*d+1≤p.support.length) := by
  classical
  letI : Nonempty V := con.nonempty
  obtain ⟨L,ne,nd,chain,maximal⟩ := exists_longest (G:=G)
  let p := Walk.ofSupport L ne chain
  have ps : p.support=L := Walk.support_ofSupport ne chain
  refine ⟨_,_,p,Walk.IsPath.mk' (by rwa [ps]),?_,?_⟩
  · intro a b q hq
    have bound := maximal q.support hq.support_nodup q.isChain_adj_support
    have m := p.length_support
    have k := q.length_support
    rw [ps] at m
    omega
  rw [ps]
  by_cases full : L.length=Fintype.card V
  · exact Or.inl full
  right
  have less := nd.length_le_card
  let x := L.head ne
  obtain ⟨v,edge⟩ := (G.degree_pos_iff_exists_adj x).mp (by have h:=min x; omega)
  have two := maximal [x,v] (by simpa using edge.ne) (by simpa using edge)
  have count := (lemma4 con
    L ne nd chain maximal (by omega) (by simpa using two)).2.2.1
  have a := min (L.head ne)
  have b := min (L.getLast ne)
  omega

#print axioms longest_order
end Graph189SidePathDegree
