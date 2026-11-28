import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1

-- Diameter three with a minimum vertex of degree at most two.
-- Degree-two and protected-exterior arguments and cut-vertex proof by @ali-hamdan-007.
-- Small-order and longest-path arguments by @carl2sheriff (PRs 11081 and 22587),
-- drawing on @computerfreak97 (PR 2971) and philipsaint. Step split by @loris-olsem.
section
open SimpleGraph
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∃ c : V, ¬ (G.induce {x | x ≠ c}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq]
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))
section Transfer
variable {W : Type*} [Fintype W] [DecidableEq W] {G' : SimpleGraph W}
lemma dist_iso (φ : G ≃g G') (hc : G.Connected) (x y : V) :
    G'.dist (φ x) (φ y) = G.dist x y := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨q,hq⟩ := (φ.connected_iff.mp hc).exists_walk_length_eq_dist (φ x) (φ y)
  have h1 := dist_le (p.map φ.toHom)
  have h2 := dist_le (q.map φ.symm.toHom)
  simp only [Walk.length_map,hp] at h1
  simpa [Walk.length_map,hq] using le_antisymm h1 (by simpa [Walk.length_map,hq] using h2)
lemma even_iso (φ : G ≃g G') (hc : G.Connected) (x : V) :
    distEven G' (φ x) = distEven G x := by
  classical
  simp only [distEven, Finset.card_filter]
  rw [← φ.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [show G'.dist (φ x) (φ.toEquiv y) = G.dist x y from dist_iso φ hc x y]
lemma second_iso [DecidableRel G.Adj] [DecidableRel G'.Adj] (φ : G ≃g G') :
    secondSmallestDegree G' = secondSmallestDegree G := by
  change ((Finset.univ.val.map (fun y : W => G'.degree y)).sort (· ≤ ·)).getD 1 0 =
    ((Finset.univ.val.map (fun x : V => G.degree x)).sort (· ≤ ·)).getD 1 0
  congr 2
  rw [← Finset.map_univ_equiv φ.toEquiv]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def]
  congr 1
  exact funext (φ.degree_eq ·)
end Transfer
section Paths
lemma rot {c : List V} (hc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) {q : V} (hq : q ∈ c) :
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
lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl
lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]
lemma ham_of_list [DecidableRel G.Adj] (l : List V) (hne : l ≠ []) (hnd : l.Nodup)
    (hch : l.IsChain G.Adj) (hlen : l.length = Fintype.card V) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by simpa [p, Walk.support_ofSupport] using hnd)
  exact ⟨_, _, p, Walk.isHamiltonian_iff_isPath_and_length_eq.mpr
    ⟨hp, by simpa [p, Walk.length_ofSupport, hlen]⟩⟩
lemma exists_longest [Nonempty V] [DecidableRel G.Adj] :
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
lemma lemma4 [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
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
lemma lemma4g [DecidableRel G.Adj] (x₀ : V) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∉ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∉ l' → l'.length ≤ l.length)
    (hout : ∃ v ∈ l, ∃ y, y ∉ l ∧ G.Adj v y ∧ y ≠ x₀) (h2 : 2 ≤ l.length) :
    (∀ y, G.Adj (l.head hne) y → y ∈ l ∨ y = x₀) ∧
      (∀ y, G.Adj (l.getLast hne) y → y ∈ l ∨ y = x₀) ∧
      ∃ s t : ℕ, G.degree (l.head hne) ≤ s + 1 ∧
        (¬ G.Adj (l.head hne) x₀ → G.degree (l.head hne) ≤ s) ∧
        G.degree (l.getLast hne) ≤ t + 1 ∧
        (¬ G.Adj (l.getLast hne) x₀ → G.degree (l.getLast hne) ≤ t) ∧ s + t + 1 ≤ l.length := by
  classical
  have hlnd := hnd
  have hlch := hch
  set q0 := l.head hne
  set z := l.getLast hne
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l ∨ y = x₀ := by
    intro y hy
    by_contra hyl
    push Not at hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl.1, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hne hlch ((hy).symm))
      (by simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hyl.2, hx⟩)
    simp only [List.length_cons] at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l ∨ y = x₀ := by
    intro y hy
    by_contra hyl
    push Not at hyl
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
      exact hyl.1 ha
    have := hmax _ hnd hch (by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hx, Ne.symm hyl.2⟩)
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
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : (G.neighborFinset q0).erase x₀ ⊆ S.image (fun j => l.getD (j + 1) q0) := by
    intro y hy
    rw [Finset.mem_erase, mem_neighborFinset] at hy
    obtain ⟨hyx, hy⟩ := hy
    rcases ext_head y hy with hyl | hyl
    swap
    · exact absurd hyl hyx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hyl
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
  have hT : (G.neighborFinset z).erase x₀ ⊆ T.image (fun j => l.getD j q0) := by
    intro y hy
    rw [Finset.mem_erase, mem_neighborFinset] at hy
    obtain ⟨hyx, hy⟩ := hy
    rcases ext_last y hy with hyl | hyl
    swap
    · exact absurd hyl hyx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hyl
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
  have hSd : G.degree q0 ≤ S.card + 1 := by
    rw [← card_neighborFinset_eq_degree]
    have h1 := Finset.card_le_card hS
    have h2 := Finset.card_image_le (s := S) (f := fun j => l.getD (j + 1) q0)
    have h3 := Finset.pred_card_le_card_erase (s := G.neighborFinset q0) (a := x₀)
    omega
  have hSd' : ¬ G.Adj q0 x₀ → G.degree q0 ≤ S.card := by
    intro hn
    rw [← card_neighborFinset_eq_degree]
    have : x₀ ∉ G.neighborFinset q0 := by rwa [mem_neighborFinset]
    rw [Finset.erase_eq_of_notMem this] at hS
    exact (Finset.card_le_card hS).trans Finset.card_image_le
  have hTd : G.degree z ≤ T.card + 1 := by
    rw [← card_neighborFinset_eq_degree]
    have h1 := Finset.card_le_card hT
    have h2 := Finset.card_image_le (s := T) (f := fun j => l.getD j q0)
    have h3 := Finset.pred_card_le_card_erase (s := G.neighborFinset z) (a := x₀)
    omega
  have hTd' : ¬ G.Adj z x₀ → G.degree z ≤ T.card := by
    intro hn
    rw [← card_neighborFinset_eq_degree]
    have : x₀ ∉ G.neighborFinset z := by rwa [mem_neighborFinset]
    rw [Finset.erase_eq_of_notMem this] at hT
    exact (Finset.card_le_card hT).trans Finset.card_image_le
  have hdisj : ∀ j, j ∈ S → j ∈ T → False := by
    intro j hjS hjT
    rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
    obtain ⟨hjm, hA⟩ := hjS
    obtain ⟨-, hB⟩ := hjT
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
    obtain ⟨v, hv, y, hyl, hvy, hyx⟩ := hout
    have hqc : v ∈ c := hperm.mem_iff.mpr hv
    obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
    have hnd' : (y :: c').Nodup := by
      refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
      intro hmem
      exact hyl ((hc'p.trans hperm).mem_iff.mp hmem)
    have hch' : (y :: c').IsChain G.Adj := by
      refine List.isChain_cons.2 ⟨?_, hc'ch⟩
      intro w hw
      rw [hc'h] at hw
      simp at hw
      subst hw
      exact hvy.symm
    have hxc' : x₀ ∉ y :: c' := by
      simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm hyx, fun hh => hx ((hc'p.trans hperm).mem_iff.mp hh)⟩
    have := hmax _ hnd' hch' hxc'
    rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
    omega
  have hdisj' : Disjoint S T := Finset.disjoint_left.mpr (fun j h1 h2 => hdisj j h1 h2)
  have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj', Finset.card_range] at hcard
  exact ⟨ext_head, ext_last, S.card, T.card, hSd, hSd', hTd, hTd', by omega⟩
lemma longer_of_perm (l : List V) (hnd : l.Nodup)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) {c : List V} (hc : c.Perm (y :: l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : c.Nodup := hc.nodup_iff.mpr (List.nodup_cons.2 ⟨hy, hnd⟩)
  have := hmax c hnd' hch
  rw [hc.length_eq] at this
  simp only [List.length_cons] at this
  omega
lemma no_insert (l : List V) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (k : ℕ) (hk0 : 0 < k) (hk : k < l.length)
    (h1 : G.Adj (l[k - 1]'(by omega)) y) (h2 : G.Adj y (l[k]'hk)) : False := by
  refine longer_of_perm l hnd hmax y hy (c := l.take k ++ y :: l.drop k)
    (List.perm_middle.trans ?_) ?_
  · rw [List.take_append_drop]
  · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
    · refine List.isChain_cons.2 ⟨?_, hch.drop _⟩
      intro z hz
      rw [List.head?_drop, List.getElem?_eq_getElem hk] at hz
      simp only [Option.mem_def, Option.some.injEq] at hz
      subst hz
      exact h2
    · intro x hx z hz
      rw [List.getLast?_take, if_neg (by omega)] at hx
      simp only [List.getElem?_eq_getElem (by omega : k - 1 < l.length), Option.some_or,
        Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hx hz
      exact h1
lemma lemma5ab [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (j : ℕ) (hj : j < l.length) (hadj : G.Adj y (l.getD j y)) :
    0 < j ∧ j + 1 < l.length ∧ ¬ G.Adj y (l.getD (j + 1) y) ∧ ¬ G.Adj y (l.getD (j - 1) y) ∧
      ¬ G.Adj (l.head hne) (l.getD (j + 1) y) ∧ ¬ G.Adj (l.getLast hne) (l.getD (j - 1) y) := by
  have hjd : l.getD j y = l[j] := List.getD_eq_getElem _ _ hj
  rw [hjd] at hadj
  have hlast : l.getLast hne = l[l.length - 1]'(by omega) := List.getLast_eq_getElem _
  have hhead : l.head hne = l[0]'(by omega) := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have h0 : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    subst hj0
    refine longer_of_perm l hnd hmax y hy (c := y :: l) (List.Perm.refl _) ?_
    refine List.IsChain.cons_of_ne_nil hne hch ?_
    rw [hhead]
    exact hadj
  have h1 : j + 1 < l.length := by
    by_contra h
    have hjl : j = l.length - 1 := by omega
    subst hjl
    refine longer_of_perm l hnd hmax y hy (c := l ++ [y]) (List.perm_append_comm.trans (List.Perm.refl _)) ?_
    refine List.isChain_append.2 ⟨hch, List.isChain_singleton _, ?_⟩
    intro x hx y' hy'
    rw [List.getLast?_eq_some_getLast hne] at hx
    simp at hx hy'
    subst hx hy'
    rw [hlast]
    exact hadj.symm
  refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ h1]
    intro hadj2
    exact no_insert l hnd hch hmax y hy (j + 1) (by omega) h1 (by simpa using hadj.symm) hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length)]
    intro hadj2
    exact no_insert l hnd hch hmax y hy j h0 hj hadj2.symm hadj
  · rw [List.getD_eq_getElem _ _ h1, hhead]
    intro hadj2
    refine longer_of_perm l hnd hmax y hy
      (c := y :: ((l.take (j + 1)).reverse ++ l.drop (j + 1))) ?_ ?_
    · refine List.Perm.cons _ ?_
      exact ((List.reverse_perm _).append_right _).trans (by rw [List.take_append_drop])
    · refine List.isChain_cons.2 ⟨?_, ?_⟩
      · intro z hz
        rw [List.head?_append, List.head?_reverse] at hz
        have e : (l.take (j + 1)).getLast? = some l[j] := by
          rw [List.getLast?_take]
          simp [List.getElem?_eq_getElem hj]
        rw [e] at hz
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hz
        subst hz
        exact hadj.symm.symm
      · refine List.isChain_append.2 ⟨?_, hch.drop _, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.take _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [List.getLast?_reverse] at hx
          rw [List.head?_drop, List.getElem?_eq_getElem h1] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hz
          have : (l.take (j + 1)).head? = some l[0] := by
            rw [List.head?_take, if_neg (by omega), List.head?_eq_some_head hne, hhead]
          rw [this] at hx
          simp only [Option.some.injEq] at hx
          subst hx
          exact hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length), hlast]
    intro hadj2
    refine longer_of_perm l hnd hmax y hy
      (c := (l.take j ++ (l.drop j).reverse) ++ [y]) ?_ ?_
    · refine List.perm_append_singleton _ _ |>.trans (List.Perm.cons _ ?_)
      exact (List.Perm.append_left _ (List.reverse_perm _)).trans (by rw [List.take_append_drop])
    · have e1 : (l.take j).getLast? = some l[j - 1] := by
        rw [List.getLast?_take, if_neg (by omega)]
        simp [List.getElem?_eq_getElem (by omega : j - 1 < l.length)]
      have e2 : (l.drop j).reverse.head? = some l[l.length - 1] := by
        rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega),
          List.getLast?_eq_some_getLast hne, hlast]
      refine List.isChain_append.2 ⟨?_, List.isChain_singleton _, ?_⟩
      · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.drop _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [e1] at hx
          rw [e2] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hx hz
          exact hadj2.symm
      · intro x hx z hz
        simp at hz
        subst hz
        have e3 : (l.take j ++ (l.drop j).reverse).getLast? = some l[j] := by
          rw [List.getLast?_append, List.getLast?_reverse, List.head?_drop,
            List.getElem?_eq_getElem hj]
          rfl
        rw [e3] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact hadj.symm
lemma dist_two (hconn : G.Connected) {y a b : V} (h1 : G.Adj y a) (h2 : G.Adj a b)
    (h3 : ¬ G.Adj y b) (h4 : b ≠ y) : G.dist y b = 2 := by
  have hle : G.dist y b ≤ 2 := by
    have := SimpleGraph.dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))
    simpa using this
  have h0 : G.dist y b ≠ 0 := fun h => h4 ((hconn.dist_eq_zero_iff.mp h).symm)
  have h1' : G.dist y b ≠ 1 := fun h => h3 (SimpleGraph.dist_eq_one_iff_adj.mp h)
  omega
lemma lemma5c [DecidableRel G.Adj] (hconn : G.Connected) (l : List V)
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (hN : ∀ z, G.Adj y z → z ∈ l) (hdeg : 1 ≤ G.degree y) :
    G.degree y + 2 ≤ distEven G y := by
  classical
  obtain ⟨z0, hz0⟩ : ∃ z, G.Adj y z := by
    have := hdeg
    rw [← card_neighborFinset_eq_degree] at this
    obtain ⟨z, hz⟩ := Finset.card_pos.mp this
    exact ⟨z, (mem_neighborFinset _ _ _).mp hz⟩
  have hne : l ≠ [] := List.ne_nil_of_mem (hN z0 hz0)
  set I := (Finset.range l.length).filter (fun i => G.Adj y (l.getD i y)) with hI
  have hmemI : ∀ i, i ∈ I ↔ i < l.length ∧ G.Adj y (l.getD i y) := by
    intro i
    simp only [hI, Finset.mem_filter, Finset.mem_range]
  have hab : ∀ i ∈ I, 0 < i ∧ i + 1 < l.length ∧ ¬ G.Adj y (l.getD (i + 1) y) ∧
      ¬ G.Adj y (l.getD (i - 1) y) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := (hmemI i).mp hi
    obtain ⟨a, b, c, d, -, -⟩ := lemma5ab hconn l hne hnd hch hmax y hy i hi1 hi2
    exact ⟨a, b, c, d⟩
  have hinj : ∀ i ∈ I, ∀ i' ∈ I, l.getD i y = l.getD i' y → i = i' := by
    intro i hi i' hi' h
    obtain ⟨hi1, -⟩ := (hmemI i).mp hi
    obtain ⟨hi1', -⟩ := (hmemI i').mp hi'
    rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi1'] at h
    exact hnd.getElem_inj_iff.mp h
  have hdegI : G.degree y = I.card := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset y = I.image (fun i => l.getD i y) := by
      ext w
      rw [mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hN w hw)
        exact ⟨k, (hmemI k).mpr ⟨hk, by rw [List.getD_eq_getElem _ _ hk]; exact hw⟩,
          List.getD_eq_getElem _ _ hk⟩
      · rintro ⟨i, hi, rfl⟩
        exact ((hmemI i).mp hi).2
    rw [this, Finset.card_image_of_injOn hinj]
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos, ← hdegI]
    omega
  set i0 := I.min' hIne with hi0
  have hi0I : i0 ∈ I := Finset.min'_mem _ _
  obtain ⟨hi0pos, hi0len, -, hi0pred⟩ := hab i0 hi0I
  have hadjl : ∀ i, i + 1 < l.length → G.Adj (l.getD i y) (l.getD (i + 1) y) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
    exact hch.getElem i hi
  have hnotin : ∀ i, i < l.length → l.getD i y ≠ y := by
    intro i hi h
    apply hy
    rw [← h, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  let T : Finset V := insert (l.getD (i0 - 1) y) (I.image (fun i => l.getD (i + 1) y))
  have hT2 : ∀ w ∈ T, G.dist y w = 2 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · refine dist_two hconn (a := l.getD i0 y) ((hmemI i0).mp hi0I).2 ?_ hi0pred (hnotin _ (by omega))
      have := hadjl (i0 - 1) (by omega)
      rw [show i0 - 1 + 1 = i0 by omega] at this
      exact this.symm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨-, hi2, hi3, -⟩ := hab i hi
      exact dist_two hconn (a := l.getD i y) ((hmemI i).mp hi).2 (hadjl i hi2) hi3
        (hnotin _ hi2)
  have hTcard : T.card = I.card + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn]
    · intro i hi i' hi' h
      obtain ⟨-, h1, -, -⟩ := hab i hi
      obtain ⟨-, h1', -, -⟩ := hab i' hi'
      simp only at h
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h1'] at h
      have := hnd.getElem_inj_iff.mp h
      omega
    · intro hmem
      obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hmem
      obtain ⟨-, h1, -, -⟩ := hab i hi
      rw [List.getD_eq_getElem _ _ (by omega : i0 - 1 < l.length),
        List.getD_eq_getElem _ _ h1] at hieq
      have := hnd.getElem_inj_iff.mp hieq
      have hle := Finset.min'_le I i hi
      omega
  have hsub : insert y T ⊆ Finset.univ.filter (fun w => Even (G.dist y w)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · rw [hT2 w hw]
      exact even_two
  have hyT : y ∉ T := by
    intro hyT
    have := hT2 y hyT
    simp at this
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hyT] at this
  change _ ≤ distEven G y at this
  omega
lemma lemma3a (hconn : G.Connected) (v w : V) (hw : 3 ≤ G.dist v w)
    (u : V) (hu : G.Adj w u) : 2 ≤ G.dist v u := by
  by_contra hlt
  have h1 := hconn.dist_triangle (u := v) (v := u) (w := w)
  have h2 : G.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm
  omega
lemma lemma3b [DecidableRel G.Adj] (hconn : G.Connected) (v : V)
    (hv : distEven G v ≤ 1 + secondSmallestDegree G) :
    (Finset.univ.filter (fun w => 2 ≤ G.dist v w)).card ≤ secondSmallestDegree G +
      (Finset.univ.filter (fun w => 3 ≤ G.dist v w ∧ Odd (G.dist v w))).card := by
  classical
  set E := Finset.univ.filter (fun w => Even (G.dist v w)) with hE
  have hEc : E.card = distEven G v := by
    simp only [hE, distEven]
  have hvE : v ∈ E := by simp [hE]
  have hsub : Finset.univ.filter (fun w => 2 ≤ G.dist v w) ⊆
      E.erase v ∪ Finset.univ.filter (fun w => 3 ≤ G.dist v w ∧ Odd (G.dist v w)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Finset.mem_union]
    rcases Nat.even_or_odd (G.dist v w) with he | ho
    · left
      rw [Finset.mem_erase]
      refine ⟨?_, by simp [hE, he]⟩
      rintro rfl
      simp at hw
    · right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ho⟩
      rcases ho with ⟨k, hk⟩
      omega
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_erase_of_mem hvE
  omega
lemma caseA [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2)
    (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (h1 : l.head hne ≠ x₀) (h2 : l.getLast hne ≠ x₀) : False := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  set n := Fintype.card V with hn
  set σ := secondSmallestDegree G with hσ
  set a := l.head hne with ha
  set b := l.getLast hne with hb
  set m := l.length with hm
  have hm2 : 2 ≤ m := by
    obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial v0
    have hh := hmax [v0, y] (by simp [hy.ne]) (by simpa using hy)
    simpa using hh
  obtain ⟨-, -, hsum, hdisj, hSd, hTd⟩ := lemma4 hconn l hne hnd hch hmax hlt hm2
  simp only [← ha, ← hb] at hsum hdisj hSd hTd
  have hxa : σ ≤ G.degree a := hx0 a h1
  have hxb : σ ≤ G.degree b := hx0 b h2
  have hsum' : G.degree a + G.degree b + 1 ≤ m := hsum
  have hmσ : m = 2 * σ + 1 := by omega
  have hnσ : n = m + 1 := by omega
  set f : ℕ → V := fun i => l.getD i a with hf
  have hf_get : ∀ i (hi : i < m), f i = l[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hf_mem : ∀ i, i < m → f i ∈ l := fun i hi => by rw [hf_get i hi]; exact List.getElem_mem _
  have hf_inj : ∀ i j, i < m → j < m → f i = f j → i = j := by
    intro i j hi hj h
    rw [hf_get i hi, hf_get j hj] at h
    exact hnd.getElem_inj_iff.mp h
  have hf_ex : ∀ w ∈ l, ∃ i, i < m ∧ f i = w := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨k, hk, hf_get k hk⟩
  have hf_adj : ∀ i, i + 1 < m → G.Adj (f i) (f (i + 1)) := by
    intro i hi
    rw [hf_get i (by omega), hf_get (i + 1) hi]
    exact hch.getElem i hi
  have hf0 : f 0 = a := by
    rw [hf_get 0 (by omega)]
    cases l with
    | nil => exact absurd rfl hne
    | cons x t => rfl
  set S := (Finset.range (m - 1)).filter (fun j => G.Adj a (f (j + 1))) with hS
  set T := (Finset.range (m - 1)).filter (fun j => G.Adj (f j) b) with hT
  have hSc : σ ≤ S.card := hxa.trans hSd
  have hTc : σ ≤ T.card := hxb.trans hTd
  have hdisjST : Disjoint S T := by
    refine Finset.disjoint_left.mpr (fun j h1 h2 => ?_)
    simp only [hS, hT, Finset.mem_filter, Finset.mem_range] at h1 h2
    exact hdisj j (by omega) h1.2 h2.2
  have hunion : S ∪ T = Finset.range (m - 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;> exact (Finset.mem_filter.mp hx).1
    · rw [Finset.card_union_of_disjoint hdisjST, Finset.card_range]
      omega
  have hTcard : T.card = σ := by
    have hc := Finset.card_union_of_disjoint hdisjST
    rw [hunion, Finset.card_range] at hc
    omega
  have hpart : ∀ j, j + 1 < m → G.Adj a (f (j + 1)) ∨ G.Adj (f j) b := by
    intro j hj
    have : j ∈ S ∪ T := by rw [hunion]; simp; omega
    rcases Finset.mem_union.mp this with h | h
    · exact Or.inl (Finset.mem_filter.mp h).2
    · exact Or.inr (Finset.mem_filter.mp h).2
  have hexy : ∃ y, y ∉ l := by
    by_contra hcon
    push Not at hcon
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hcon w]
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Finset.card_univ] at h2
    omega
  obtain ⟨y, hy⟩ := hexy
  have hall : ∀ z, z ∈ l ∨ z = y := by
    intro z
    by_contra hcon
    push Not at hcon
    have hnd2 : (y :: z :: l).Nodup := by
      simp [hcon.2, hcon.1, hy, Ne.symm hcon.2, hnd]
    have := List.toFinset_card_of_nodup hnd2
    have h3 := Finset.card_le_univ (y :: z :: l).toFinset
    simp only [List.length_cons] at this
    omega
  have hNy : ∀ z, G.Adj y z → z ∈ l := by
    intro z hz
    rcases hall z with h | h
    · exact h
    · exact absurd (h ▸ hz) (G.loopless.irrefl y)
  have hdegy : 1 ≤ G.degree y := by
    obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial y
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨z, (mem_neighborFinset _ _ _).mpr hz⟩
  have h5c := lemma5c hconn l hnd hch hmax y hy hNy hdegy
  have hyx0 : y = x₀ := by
    by_contra hne0
    have := hx0 y hne0
    have := hH y
    omega
  have hxy : ∀ w, w ≠ y → σ ≤ G.degree w := fun w hw => hx0 w (hyx0 ▸ hw)
  have hyN : ∀ w, G.Adj y w → G.Adj a w ∧ w ≠ a := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := hf_ex w (hNy w hw)
    have hy' : l.getD j y = f j := by
      rw [List.getD_eq_getElem _ _ hj, hf_get j hj]
    obtain ⟨h0, h1, -, -, -, h6⟩ := lemma5ab hconn l hne hnd hch hmax y hy j hj
      (by rw [hy']; exact hw)
    have hy1 : l.getD (j - 1) y = f (j - 1) := by
      rw [List.getD_eq_getElem _ _ (by omega), hf_get (j - 1) (by omega)]
    rw [← hb, hy1] at h6
    have h6' : ¬ G.Adj b (f (j - 1)) := h6
    refine ⟨?_, fun h => ?_⟩
    · rcases hpart (j - 1) (by omega) with h | h
      · rw [show j - 1 + 1 = j by omega] at h
        exact h
      · exact absurd h.symm h6'
    · have := hf_inj j 0 hj (by omega) (h.trans hf0.symm)
      omega
  have hd2 : ∀ u, u ≠ a → ¬ G.Adj a u → 2 ≤ G.dist a u := by
    intro u hu1 hu2
    have h0 : G.dist a u ≠ 0 := fun h => hu1 (hconn.dist_eq_zero_iff.mp h).symm
    have h1 : G.dist a u ≠ 1 := fun h => hu2 (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have hay : G.dist a y = 2 := by
    obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial y
    obtain ⟨hz1, -⟩ := hyN z hz
    refine dist_two hconn hz1 hz.symm ?_ ?_
    · intro h
      exact (hyN a h.symm).2 rfl
    · intro h
      exact hy (by rw [h]; exact List.head_mem hne)
  set Timg := T.image (fun i => f (i + 1)) with hTimg
  have hTi_card : Timg.card = σ := by
    rw [hTimg, Finset.card_image_of_injOn, hTcard]
    intro i hi i' hi' h
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hi1' := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
    have := hf_inj (i + 1) (i' + 1) (by omega) (by omega) h
    omega
  have hTimg_l : ∀ u ∈ Timg, u ∈ l := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact hf_mem _ (by omega)
  have hTimg_d : ∀ u ∈ Timg, 2 ≤ G.dist a u := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    apply hd2
    · intro h
      have := hf_inj (i + 1) 0 (by omega) (by omega) (h.trans hf0.symm)
      omega
    · intro h
      exact Finset.disjoint_left.mp hdisjST
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, h⟩) hi
  set U := Finset.univ.filter (fun w => 2 ≤ G.dist a w) with hU
  have hU_sub : U ⊆ insert y Timg := by
    intro u hu
    have hu2 : 2 ≤ G.dist a u := (Finset.mem_filter.mp hu).2
    rw [Finset.mem_insert]
    rcases hall u with hul | rfl
    · right
      obtain ⟨k, hk, rfl⟩ := hf_ex u hul
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [hf0] at hu2
        simp at hu2
      rcases hpart (k - 1) (by omega) with h | h
      · rw [show k - 1 + 1 = k by omega] at h
        have := SimpleGraph.dist_eq_one_iff_adj.mpr h
        omega
      · exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), h⟩, by rw [show k - 1 + 1 = k by omega]⟩
    · left; rfl
  have hyT : y ∉ Timg := fun h => hy (hTimg_l y h)
  have hU_card : σ + 1 ≤ U.card := by
    have : insert y Timg ⊆ U := by
      intro u hu
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · omega
      · exact hTimg_d u hu
    have := Finset.card_le_card this
    rw [Finset.card_insert_of_notMem hyT] at this
    omega
  have h3b : U.card ≤ σ + (Finset.univ.filter
      (fun w => 3 ≤ G.dist a w ∧ Odd (G.dist a w))).card := lemma3b hconn a (hH a)
  obtain ⟨w, hwF⟩ : (Finset.univ.filter (fun w => 3 ≤ G.dist a w ∧ Odd (G.dist a w))).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨-, hw3, -⟩ := (by simpa using hwF : True ∧ 3 ≤ G.dist a w ∧ Odd (G.dist a w))
  have hwy : w ≠ y := by
    rintro rfl
    omega
  have hwU : w ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hwT : w ∈ Timg := by
    rcases Finset.mem_insert.mp (hU_sub hwU) with h | h
    · exact absurd h hwy
    · exact h
  have hnb : G.neighborFinset w ⊆ Timg.erase w := by
    intro u hu
    rw [mem_neighborFinset] at hu
    have hu2 := lemma3a hconn a w hw3 u hu
    have huU : u ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2⟩
    rw [Finset.mem_erase]
    refine ⟨hu.ne.symm, ?_⟩
    rcases Finset.mem_insert.mp (hU_sub huU) with rfl | h
    · exfalso
      have := SimpleGraph.dist_eq_one_iff_adj.mpr (hyN w hu.symm).1
      omega
    · exact h
  have hdw := Finset.card_le_card hnb
  rw [Finset.card_erase_of_mem hwT, hTi_card, card_neighborFinset_eq_degree] at hdw
  have := hxy w hwy
  have hpos : 0 < Timg.card := Finset.card_pos.mpr ⟨w, hwT⟩
  omega
lemma exists_out_edge (hconn : G.Connected) (l : List V) (hne : l ≠ []) (hnd : l.Nodup)
    (hlt : l.length < Fintype.card V) : ∃ v ∈ l, ∃ y, y ∉ l ∧ G.Adj v y := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, w ∉ l := by
    by_contra hcon
    push Not at hcon
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hcon w]
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Finset.card_univ] at h2
    omega
  obtain ⟨p⟩ := hconn (l.head hne) w
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hne) hw
  exact ⟨d.fst, hd1, d.snd, hd2, d.adj⟩
lemma caseB_aux [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2)
    (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (t : List V) (hnd : (x₀ :: t).Nodup) (hch : (x₀ :: t).IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ (x₀ :: t).length)
    (hlt : (x₀ :: t).length < Fintype.card V)
    (hall : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length = (x₀ :: t).length →
      ∀ h : l' ≠ [], l'.head h = x₀ ∨ l'.getLast h = x₀) : False := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  have hne : (x₀ :: t) ≠ [] := List.cons_ne_nil _ _
  have hm2 : 2 ≤ (x₀ :: t).length := by
    obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial v0
    have hh := hmax [v0, y] (by simp [hy.ne]) (by simpa using hy)
    simpa using hh
  obtain ⟨hext, hextL, hsum⟩ := lemma4 hconn (x₀ :: t) hne hnd hch hmax hlt hm2
  have hext' : ∀ y, G.Adj x₀ y → y ∈ x₀ :: t := hext
  have hdeg1 : 1 ≤ G.degree x₀ := by
    obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial x₀
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨z, (mem_neighborFinset _ _ _).mpr hz⟩
  by_cases hdeg2 : 2 ≤ G.degree x₀
  · exfalso
    obtain ⟨j, hj2, hjm, hadjj⟩ : ∃ j, 2 ≤ j ∧ ∃ hj : j < (x₀ :: t).length,
        G.Adj x₀ (x₀ :: t)[j] := by
      have h1 : 1 < (G.neighborFinset x₀).card := by
        rw [card_neighborFinset_eq_degree]
        omega
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h1
      rw [mem_neighborFinset] at hu hv
      obtain ⟨ku, hku, rfl⟩ := List.getElem_of_mem (hext' u hu)
      obtain ⟨kv, hkv, rfl⟩ := List.getElem_of_mem (hext' v hv)
      have hk0 : ∀ k (hk : k < (x₀ :: t).length), G.Adj x₀ (x₀ :: t)[k] → k ≠ 0 := by
        intro k hk h hk0
        subst hk0
        exact G.loopless.irrefl x₀ (by simpa using h)
      have hne' : ku ≠ kv := fun h => huv (by subst h; rfl)
      have h1 := hk0 ku hku hu
      have h2 := hk0 kv hkv hv
      by_cases hle : ku ≤ kv
      · exact ⟨kv, by omega, hkv, hv⟩
      · exact ⟨ku, by omega, hku, hu⟩
    set L := x₀ :: t with hL
    have e0 : (L.take j).getLast? = some L[j - 1] := by
      rw [List.getLast?_take, if_neg (by omega)]
      simp [List.getElem?_eq_getElem (by omega : j - 1 < L.length)]
    have e1 : (L.take j).head? = some x₀ := by
      rw [List.head?_take, if_neg (by omega)]
      rfl
    have hcperm : ((L.take j).reverse ++ L.drop j).Perm L :=
      ((List.reverse_perm _).append_right _).trans (by rw [List.take_append_drop])
    have hcch : ((L.take j).reverse ++ L.drop j).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨?_, hch.drop _, ?_⟩
      · rw [List.isChain_reverse]
        exact (hch.take _).imp (fun a b h => h.symm)
      · intro x hx z hz
        rw [List.getLast?_reverse, e1] at hx
        rw [List.head?_drop, List.getElem?_eq_getElem hjm] at hz
        simp only [Option.mem_def, Option.some.injEq] at hx hz
        subst hx hz
        exact hadjj
    have hcne : (L.take j).reverse ++ L.drop j ≠ [] := by
      intro h
      have := hcperm.length_eq
      rw [h] at this
      simp at this
    have hcl := hcperm.length_eq
    have hhd : ((L.take j).reverse ++ L.drop j).head? = some L[j - 1] := by
      rw [List.head?_append, List.head?_reverse, e0]
      rfl
    have hlst : ((L.take j).reverse ++ L.drop j).getLast? = some L[L.length - 1] := by
      rw [List.getLast?_append, List.getLast?_drop, if_neg (by omega),
        List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem]
      rfl
    have hidx : ∀ k (hk : k < L.length), L[k] = x₀ → k = 0 := by
      intro k hk h
      have h0 : L[0]'(by omega) = x₀ := rfl
      exact hnd.getElem_inj_iff.mp (h.trans h0.symm)
    rcases hall _ (hcperm.nodup_iff.mpr hnd) hcch hcl hcne with h | h
    · have := (List.head?_eq_some_head hcne).symm.trans hhd
      simp only [Option.some.injEq] at this
      rw [this] at h
      have := hidx _ (by omega) h
      omega
    · have := (List.getLast?_eq_some_getLast hcne).symm.trans hlst
      simp only [Option.some.injEq] at this
      rw [this] at h
      have := hidx _ (by omega) h
      omega
  · have hdeg1' : G.degree x₀ = 1 := by omega
    exfalso
    have hht : t ≠ [] := by
      rintro rfl
      simp at hm2
    have hN1 : ∀ u, G.Adj x₀ u → u = t.head hht := by
      have hcard : (G.neighborFinset x₀).card ≤ 1 := by
        rw [card_neighborFinset_eq_degree]; omega
      intro u hu
      have hc : G.Adj x₀ (t.head hht) := by
        have := (List.isChain_cons.mp hch).1
        exact this _ (by simp [List.head?_eq_some_head hht])
      exact Finset.card_le_one.mp hcard u ((mem_neighborFinset _ _ _).mpr hu) _
        ((mem_neighborFinset _ _ _).mpr hc)
    obtain ⟨v, hv, y, hyl, hvy⟩ := exists_out_edge hconn (x₀ :: t) hne hnd hlt
    have hvx : v ≠ x₀ := by
      rintro rfl
      exact hyl (hext' y hvy)
    have hvt : v ∈ t := by
      rcases List.mem_cons.mp hv with h | h
      · exact absurd h hvx
      · exact h
    have hyt : y ∉ t := fun h => hyl (List.mem_cons_of_mem _ h)
    have hyx : y ≠ x₀ := fun h => hyl (h ▸ List.mem_cons_self)
    have hxt : x₀ ∉ t := (List.nodup_cons.mp hnd).1
    have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
    have hcht : t.IsChain G.Adj := (List.isChain_cons.mp hch).2
    have hm3 : 2 ≤ t.length := by
      by_contra hlt2
      have hl1 : t.length = 1 := by
        have : t.length ≠ 0 := fun h => hht (List.length_eq_zero_iff.mp h)
        omega
      obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hl1
      simp only [List.mem_singleton] at hvt
      subst hvt
      have := hextL y (by simpa using hvy)
      exact hyl this
    have hmaxg : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∉ l' → l'.length ≤ t.length := by
      intro l' h1 h2 h3
      by_contra hcon
      push Not at hcon
      have hle := hmax l' h1 h2
      have hl' : l'.length = (x₀ :: t).length := by
        simp only [List.length_cons] at hle ⊢
        omega
      have hl'ne : l' ≠ [] := by
        rintro rfl
        simp at hcon
      rcases hall l' h1 h2 hl' hl'ne with h | h
      · exact h3 (h ▸ List.head_mem hl'ne)
      · exact h3 (h ▸ List.getLast_mem hl'ne)
    obtain ⟨-, -, s, t', hs, -, ht1, ht2, hst⟩ := lemma4g x₀ t hht hndt hcht hxt hmaxg
      ⟨v, hvt, y, hyt, hvy, hyx⟩ hm3
    have hcx : t.head hht ≠ x₀ := fun h => hxt (h ▸ List.head_mem hht)
    have hzx : t.getLast hht ≠ x₀ := fun h => hxt (h ▸ List.getLast_mem hht)
    have hlast_ne : t.getLast hht ≠ t.head hht := by
      intro heq
      cases t with
      | nil => exact hht rfl
      | cons h0 t2 =>
        have ht2 : t2 ≠ [] := by
          rintro rfl
          simp at hm3
        have hmem : (h0 :: t2).getLast hht ∈ t2 := by
          rw [List.getLast_cons ht2]
          exact List.getLast_mem ht2
        have hnd' := (List.nodup_cons.mp hndt).1
        apply hnd'
        have : (h0 :: t2).getLast hht = h0 := heq
        rw [← this]
        exact hmem
    have hcadj : G.Adj (t.head hht) x₀ := by
      have := (List.isChain_cons.mp hch).1
      exact (this _ (by simp [List.head?_eq_some_head hht])).symm
    have hzna : ¬ G.Adj (t.getLast hht) x₀ := by
      intro h
      exact hlast_ne (hN1 _ h.symm)
    have hdc := hx0 _ hcx
    have hdz := hx0 _ hzx
    have hs' := hs
    have ht2' := ht2 hzna
    have hlen : (x₀ :: t).length = t.length + 1 := rfl
    have hmσ : (x₀ :: t).length = 2 * secondSmallestDegree G + 1 := by omega
    obtain ⟨y', hy'⟩ : ∃ y', y' ∉ x₀ :: t := by
      by_contra hcon
      push Not at hcon
      have h1 : (x₀ :: t).toFinset = Finset.univ :=
        Finset.eq_univ_of_forall (fun w => List.mem_toFinset.mpr (hcon w))
      have h2 := List.toFinset_card_of_nodup hnd
      rw [h1, Finset.card_univ] at h2
      omega
    have hall' : ∀ z, z ∈ x₀ :: t ∨ z = y' := by
      intro z
      by_contra hcon
      push Not at hcon
      have hnd2 : (y' :: z :: (x₀ :: t)).Nodup := by
        simp [hcon.2, hcon.1, hy', Ne.symm hcon.2, hnd]
      have := List.toFinset_card_of_nodup hnd2
      have h3 := Finset.card_le_univ (y' :: z :: (x₀ :: t)).toFinset
      simp only [List.length_cons] at this
      omega
    have hNy : ∀ z, G.Adj y' z → z ∈ x₀ :: t := by
      intro z hz
      rcases hall' z with h | h
      · exact h
      · exact absurd (h ▸ hz) (G.loopless.irrefl y')
    have hdegy : 1 ≤ G.degree y' := by
      obtain ⟨z, hz⟩ := hconn.preconnected.exists_adj_of_nontrivial y'
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨z, (mem_neighborFinset _ _ _).mpr hz⟩
    have h5c := lemma5c hconn (x₀ :: t) hnd hch hmax y' hy' hNy hdegy
    have hy'x : y' ≠ x₀ := fun h => hy' (h ▸ List.mem_cons_self)
    have := hx0 y' hy'x
    have := hH y'
    omega
lemma caseB [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2)
    (x₀ : V) (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (l : List V) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hall : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length = l.length →
      ∀ h : l' ≠ [], l'.head h = x₀ ∨ l'.getLast h = x₀) : False := by
  rcases hall l hnd hch rfl hne with h | h
  · cases l with
    | nil => exact hne rfl
    | cons a t =>
      have : a = x₀ := h
      subst this
      exact caseB_aux hconn hH hn a hx0 t hnd hch hmax hlt hall
  · have hrne : l.reverse ≠ [] := by simpa using hne
    have hrh : l.reverse.head hrne = x₀ := by
      rw [List.head_reverse]
      exact h
    have hrch : l.reverse.IsChain G.Adj := by
      rw [List.isChain_reverse]
      exact hch.imp (fun a b h => h.symm)
    cases hlr : l.reverse with
    | nil => exact hrne hlr
    | cons a t =>
      have ha : a = x₀ := by
        have : (a :: t).head (by simp) = x₀ := by simpa [hlr] using hrh
        exact this
      subst ha
      rw [hlr] at hrch
      have hlen : (a :: t).length = l.length := by rw [← hlr]; simp
      refine caseB_aux hconn hH hn a hx0 t (by rw [← hlr]; exact List.nodup_reverse.mpr hnd) hrch
        (fun l' h1 h2 => hlen ▸ hmax l' h1 h2) (hlen ▸ hlt) ?_
      intro l' h1 h2 h3 h4
      exact hall l' h1 h2 (h3.trans hlen) h4
theorem theorem_C [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : Fintype.card V ≤ 2 * secondSmallestDegree G + 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun v : V => G.degree v)
    Finset.univ_nonempty
  have hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v := by
    intro v hv
    rcases degree_pair (G := G) x₀ v (Ne.symm hv) with h | h
    · exact h.trans (hmin v (Finset.mem_univ v))
    · exact h
  obtain ⟨l, hne, hnd, hch, hmax⟩ := exists_longest (G := G)
  by_cases hlen : l.length = Fintype.card V
  · exact ham_of_list l hne hnd hch hlen
  exfalso
  have hlt : l.length < Fintype.card V := lt_of_le_of_ne hnd.length_le_card hlen
  by_cases hex : ∃ l' : List V, ∃ h : l' ≠ [], l'.Nodup ∧ l'.IsChain G.Adj ∧
      l'.length = l.length ∧ l'.head h ≠ x₀ ∧ l'.getLast h ≠ x₀
  · obtain ⟨l', h', hnd', hch', hlen', h1, h2⟩ := hex
    exact caseA hconn hH hn x₀ hx0 l' h' hnd' hch'
      (fun l'' a b => (hmax l'' a b).trans hlen'.symm.le) (hlen' ▸ hlt) h1 h2
  · push Not at hex
    refine caseB hconn hH hn x₀ hx0 l hne hnd hch hmax hlt ?_
    intro l' hnd' hch' hlen' h'
    by_cases h1 : l'.head h' = x₀
    · exact Or.inl h1
    · exact Or.inr (hex l' h' hnd' hch' hlen' h1)
end Paths
end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2
end

section
section
namespace Graph189CutCore
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable def evenCard (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter fun y => Even (G.dist v y)).card
noncomputable def sortedDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : V => G.degree v).sort (· ≤ ·)
noncomputable def secondDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (sortedDegrees G).getD 1 0
structure Side (G : SimpleGraph V) (c : V) (S : Finset V) : Prop where
  nonempty : S.Nonempty
  outside : c ∉ S
  exit_eq : ∀ {u v}, u ∈ S → G.Adj u v → v ∉ S → v = c
omit [Fintype V] [DecidableEq V] in
theorem Side.contact {c : V} {S : Finset V} (h : Side G c S) (hc : G.Connected) :
    ∃ x ∈ S, G.Adj x c := by
  obtain ⟨w,hw⟩ := h.nonempty
  obtain ⟨P⟩ := hc w c
  obtain ⟨d, _, hin, hout⟩ := P.exists_boundary_dart (S : Set V) hw h.outside
  exact ⟨d.fst,hin,h.exit_eq hin d.adj hout ▸ d.adj⟩
omit [Fintype V] in
theorem Side.dist_add {c x y : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) (hx : x ∈ S) (hy : y ∉ S) :
    G.dist x y = G.dist x c + G.dist c y := by
  obtain ⟨P,hP⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨d, hd, hin, hout⟩ := P.exists_boundary_dart (S : Set V) hx hy
  have hm : c ∈ P.support := h.exit_eq hin d.adj hout ▸ P.dart_snd_mem_support_of_mem_darts hd
  have hsum := congrArg Walk.length (P.take_spec hm)
  rw [Walk.length_append, hP] at hsum
  exact le_antisymm hc.dist_triangle (by
    have := G.dist_le (P.takeUntil c hm)
    have := G.dist_le (P.dropUntil c hm)
    omega)
theorem Side.parity_bound {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1 + k) :
    Sᶜ.card + (S.filter (fun y => Even (G.dist c y))).card + 1 ≤ 2*k+2 := by
  classical
  obtain ⟨x,hx,hxc⟩ := h.contact hc
  let E (v : V) := univ.filter (fun y => Even (G.dist v y))
  let A := S.filter (fun y => Even (G.dist c y))
  have hxA : x ∉ A := by simp [A,dist_eq_one_iff_adj.mpr hxc.symm]
  have hdis : Disjoint (insert x A) Sᶜ := by
    apply Finset.disjoint_left.mpr
    intro y hy hys
    have h' : y ∈ S := by
      rcases mem_insert.mp hy with rfl | hh
      · exact hx
      · exact (mem_filter.mp hh).1
    exact (mem_compl.mp hys) h'
  have hin : insert x A ∪ Sᶜ ⊆ E c ∪ E x := by
    intro y hy
    rcases mem_union.mp hy with hm | hm
    · rcases mem_insert.mp hm with rfl | ha
      · exact mem_union_right _ (by simp [E])
      · exact mem_union_left _ (by simpa [E] using (mem_filter.mp ha).2)
    · have hd := h.dist_add hc hx (mem_compl.mp hm)
      rw [dist_eq_one_iff_adj.mpr hxc] at hd
      simp only [E, mem_union, mem_filter, mem_univ, true_and, Nat.even_iff]
      omega
  have hu := (card_le_card hin).trans (card_union_le (E c) (E x))
  rw [card_union_of_disjoint hdis, card_insert_of_notMem hxA] at hu
  have h1 : (E c).card ≤ 1+k := hσ c
  have h2 : (E x).card ≤ 1+k := hσ x
  change Sᶜ.card + A.card + 1 ≤ 2*k+2
  omega
theorem Side.card_bounds [DecidableRel G.Adj] {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) :
    2 ≤ S.card ∧ k ≤ S.card ∧ Sᶜ.card ≤ 2*k+1 := by
  classical
  have hb := h.parity_bound hc hσ
  have hcs := card_add_card_compl S
  have h2 : 1 < S.card := by omega
  obtain ⟨x,hx,y,hy,hne⟩ := one_lt_card.mp h2
  have deg (v : V) (hv : v ∈ S) : G.degree v ≤ S.card := by
    have hin : G.neighborFinset v ⊆ insert c (S.erase v) := by
      intro w hw
      have he : G.Adj v w := by simpa using hw
      by_cases h' : w ∈ S
      · exact mem_insert_of_mem (mem_erase.mpr ⟨he.ne.symm,h'⟩)
      · exact mem_insert.mpr (Or.inl (h.exit_eq hv he h'))
    have hh := card_le_card hin
    rw [card_neighborFinset_eq_degree, card_insert_of_notMem (by
      exact fun hm => h.outside (mem_of_mem_erase hm)), card_erase_of_mem hv] at hh
    omega
  exact ⟨by omega, (hpair x y hne).elim (·.trans (deg x hx)) (·.trans (deg y hy)), by omega⟩
omit [Fintype V] [DecidableEq V] in
theorem Side.exists_distance_two {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {v : V} (hv : v ∈ S) (hn : ¬ G.Adj c v) :
    ∃ u ∈ S, G.dist c u = 2 := by
  classical
  obtain ⟨P⟩ := hc v c
  let far : Set V := {u | u ∈ S ∧ ¬ G.Adj c u}
  have hnot : c ∉ far := fun hm => h.outside hm.1
  obtain ⟨d,_,hin,hout⟩ := P.exists_boundary_dart far ⟨hv, hn⟩ hnot
  have hnear : G.Adj c d.snd := by
    by_contra hh
    have h' : d.snd ∉ S := fun hs => hout ⟨hs,hh⟩
    have heq := h.exit_eq hin.1 d.adj h'
    exact hin.2 (heq ▸ d.adj.symm)
  let Q : G.Walk c d.fst := .cons hnear (.cons d.adj.symm .nil)
  have hle : G.dist c d.fst ≤ 2 := G.dist_le Q
  have hlt := hc.one_lt_dist_of_ne_of_not_adj
    (show c ≠ d.fst from fun he => h.outside (he ▸ hin.1)) hin.2
  exact ⟨d.fst, hin.1, by omega⟩
theorem Side.full_contact_of_two_other_sides {c : V} {S T U : Finset V}
    (hS : Side G c S) (hT : Side G c T) (hU : Side G c U)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (ht : k ≤ T.card) (hu : k ≤ U.card) :
    ∀ x ∈ S, G.Adj c x := by
  classical
  have hdis : c ∉ T ∪ U := fun hm => (mem_union.mp hm).elim hT.outside hU.outside
  have hin : insert c (T ∪ U) ⊆ Sᶜ := by
    intro v hv
    apply mem_compl.mpr
    rcases mem_insert.mp hv with rfl | hv
    · exact hS.outside
    · rcases mem_union.mp hv with ht | hu
      · exact fun hs => Finset.disjoint_left.mp hST hs ht
      · exact fun hs => Finset.disjoint_left.mp hSU hs hu
  have hcs := card_le_card hin
  rw [card_insert_of_notMem hdis,card_union_of_disjoint hTU] at hcs
  have hb := hS.parity_bound hc hσ
  intro x hx
  by_contra hn
  obtain ⟨y,hy,hy2⟩ := hS.exists_distance_two hc hx hn
  have hp : 0 < (S.filter (fun y => Even (G.dist c y))).card :=
    card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,by simp [hy2]⟩⟩
  omega
theorem no_three_sides [DecidableRel G.Adj] {c : V} {S T U : Finset V}
    (hS : Side G c S) (hT : Side G c T) (hU : Side G c U)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) : False := by
  classical
  obtain ⟨hs,hs',_⟩ := hS.card_bounds hc hσ horder hpair
  obtain ⟨ht,ht',_⟩ := hT.card_bounds hc hσ horder hpair
  obtain ⟨hu,hu',_⟩ := hU.card_bounds hc hσ horder hpair
  obtain ⟨x,hx,hxc⟩ := hS.contact hc
  have hadjT := hT.full_contact_of_two_other_sides hS hU hST.symm hTU hSU hc hσ hs' hu'
  have hadjU := hU.full_contact_of_two_other_sides hS hT hSU.symm hTU.symm hST hc hσ hs' ht'
  have hxa : x ∉ T ∪ U := fun hm => (mem_union.mp hm).elim
    (Finset.disjoint_left.mp hST hx) (Finset.disjoint_left.mp hSU hx)
  have hsub : insert x (T ∪ U) ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp
    · rcases mem_union.mp hy with h | h
      · have hd := hS.dist_add hc hx (fun hs => Finset.disjoint_left.mp hST hs h)
        simp [hd,dist_eq_one_iff_adj.mpr hxc,dist_eq_one_iff_adj.mpr (hadjT y h)]
      · have hd := hS.dist_add hc hx (fun hs => Finset.disjoint_left.mp hSU hs h)
        simp [hd,dist_eq_one_iff_adj.mpr hxc,dist_eq_one_iff_adj.mpr (hadjU y h)]
  have hb : (insert x (T ∪ U)).card ≤ 1+k := (card_le_card hsub).trans (hσ x)
  rw [card_insert_of_notMem hxa,card_union_of_disjoint hTU] at hb
  omega
noncomputable def componentVertices (c : V)
    (C : (G.induce {v | v ≠ c}).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun x => ∃ h : x ≠ c, (G.induce {v | v ≠ c}).connectedComponentMk ⟨x,h⟩ = C)
private theorem mem_componentVertices {c x : V}
    {C : (G.induce {v | v ≠ c}).ConnectedComponent} :
    x ∈ componentVertices c C ↔
      ∃ h : x ≠ c, (G.induce {v | v ≠ c}).connectedComponentMk ⟨x,h⟩ = C := by
  classical
  simp [componentVertices]
private theorem componentVertices_side (c : V) (C : (G.induce {v | v ≠ c}).ConnectedComponent) :
    Side G c (componentVertices c C) := by
  classical
  constructor
  · obtain ⟨x,hx⟩ := (Quot.mk_surjective C)
    exact ⟨x.val, mem_componentVertices.mpr ⟨x.property,hx⟩⟩
  · intro h
    obtain ⟨hn,_⟩ := mem_componentVertices.mp h
    exact hn rfl
  · intro u v hu hadj hv
    by_contra hne
    obtain ⟨huc,hC⟩ := mem_componentVertices.mp hu
    have h' : (G.induce {v | v ≠ c}).Adj ⟨u,huc⟩ ⟨v,hne⟩ := hadj
    exact hv (mem_componentVertices.mpr
      ⟨hne,(ConnectedComponent.connectedComponentMk_eq_of_adj h').symm.trans hC⟩)
private theorem componentVertices_disjoint {c : V}
    {A B : (G.induce {v | v ≠ c}).ConnectedComponent} (hne : A ≠ B) :
    Disjoint (componentVertices c A) (componentVertices c B) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hA hB
  obtain ⟨_,ha⟩ := mem_componentVertices.mp hA
  obtain ⟨_,hb⟩ := mem_componentVertices.mp hB
  exact hne (ha.symm.trans hb)
theorem components_after_deleting_le_two [DecidableRel G.Adj]
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) (c : V) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent ≤ 2 := by
  classical
  let _ := Fintype.ofFinite (G.induce {v | v ≠ c}).ConnectedComponent
  rw [Nat.card_eq_fintype_card]
  by_contra! h
  obtain ⟨A,B,C,hAB,hAC,hBC⟩ := Fintype.two_lt_card_iff.mp h
  exact no_three_sides (componentVertices_side c A) (componentVertices_side c B)
    (componentVertices_side c C) (componentVertices_disjoint hAB)
    (componentVertices_disjoint hAC) (componentVertices_disjoint hBC) hc hσ horder hpair
omit [DecidableEq V] in
private lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondDegree G ≤ G.degree x ∨ secondDegree G ≤ G.degree y := by
  classical
  let ds := sortedDegrees G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, sortedDegrees] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, sortedDegrees]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, sortedDegrees]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq]
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))
theorem components_after_cut_eq_two [DecidableRel G.Adj] [Nontrivial V]
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1 + (secondDegree G))
    (horder : 2 * (secondDegree G) + 3 ≤ Fintype.card V) {c : V}
    (hcut : ¬ (G.induce {v | v ≠ c}).Connected) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2 := by
  classical
  have hub := components_after_deleting_le_two hc hσ horder (degree_pair (G := G)) c
  apply le_antisymm hub
  by_contra! h
  let _ := Fintype.ofFinite (G.induce {v | v ≠ c}).ConnectedComponent
  rw [Nat.card_eq_fintype_card] at h
  have _ : Subsingleton (G.induce {v | v ≠ c}).ConnectedComponent :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨w,hw⟩ := exists_ne c
  exact hcut { preconnected := fun u v => ConnectedComponent.exact (Subsingleton.elim _ _)
               nonempty := ⟨⟨w,hw⟩⟩ }
end Graph189CutCore
end
section
namespace Graph189CutInterface
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
theorem components_after_cut_eq_two (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V) {c : V}
    (hcut : ¬ (G.induce {v | v ≠ c}).Connected) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2 :=
  Graph189CutCore.components_after_cut_eq_two hc hσ horder hcut
end Graph189CutInterface
end
section
namespace Graph189CutExtract
open SimpleGraph Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
theorem componentVertices_connected (c : V)
    (C : (G.induce {v | v ≠ c}).ConnectedComponent) :
    (G.induce (componentVertices c C : Set V)).Connected := by
  classical
  let φ : C.toSimpleGraph →g G.induce (componentVertices c C : Set V) :=
    { toFun := fun z => ⟨z.val.val, mem_componentVertices.mpr ⟨z.val.property,z.property⟩⟩
      map_rel' := fun h => h }
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨hn,hC⟩ := mem_componentVertices.mp z.property
    exact ⟨⟨⟨z.val,hn⟩,hC⟩, Subtype.ext rfl⟩
  exact Connected.map φ hsurj C.connected_toSimpleGraph
theorem two_connected_sides (c : V)
    (htwo : Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2) :
    ∃ A B : Finset V, Side G c A ∧ Side G c B ∧ Disjoint A B ∧
      (∀ x, x = c ∨ x ∈ A ∨ x ∈ B) ∧
      (G.induce (A : Set V)).Connected ∧ (G.induce (B : Set V)).Connected := by
  classical
  let H := G.induce {v | v ≠ c}
  let _ := Fintype.ofFinite H.ConnectedComponent
  have hcard : Fintype.card H.ConnectedComponent = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact htwo
  let e : H.ConnectedComponent ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let C := e.symm 0
  let D := e.symm 1
  have hne : C ≠ D := fun eq => (by decide : (0 : Fin 2) ≠ 1) (e.symm.injective eq)
  refine ⟨componentVertices c C, componentVertices c D,
    componentVertices_side c C, componentVertices_side c D, componentVertices_disjoint hne,
    ?_, componentVertices_connected c C, componentVertices_connected c D⟩
  intro x
  by_cases hx : x = c
  · exact Or.inl hx
  · let t := H.connectedComponentMk ⟨x,hx⟩
    have alt : e t = 0 ∨ e t = 1 := by
      have lim := (e t).isLt
      rcases (by omega : (e t).val = 0 ∨ (e t).val = 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases alt with h | h
    · exact Or.inr (Or.inl (mem_componentVertices.mpr ⟨hx, (e.eq_symm_apply).mpr h⟩))
    · exact Or.inr (Or.inr (mem_componentVertices.mpr ⟨hx, (e.eq_symm_apply).mpr h⟩))
end Graph189CutExtract
end
section
namespace Graph189CutMiddle
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
theorem side_away_from {c d : V} (hcd : c ≠ d)
    (hcut : ¬ (G.induce {x | x ≠ c}).Connected) :
    ∃ A : Finset V, Side G c A ∧ d ∉ A := by
  classical
  let D := G.induce {x | x ≠ c}
  let t : {x : V // x ≠ c} := ⟨d,hcd.symm⟩
  let A := univ.filter (fun x => ∃ hn : x ≠ c, ¬ D.Reachable ⟨x, hn⟩ t)
  have memA {x : V} : x ∈ A ↔ ∃ hn : x ≠ c, ¬ D.Reachable ⟨x,hn⟩ t := by simp [A]
  have hex : ∃ x, ¬ D.Reachable x t := by
    by_contra! hr
    exact hcut {preconnected := fun x y => (hr x).trans (hr y).symm, nonempty := ⟨t⟩}
  obtain ⟨x,hx⟩ := hex
  refine ⟨A, ⟨⟨x.val,memA.mpr ⟨x.property,hx⟩⟩,?_,?_⟩,?_⟩
  · intro h
    obtain ⟨hh,_⟩ := memA.mp h
    exact hh rfl
  · intro u v hu huv hv
    by_contra hvc
    obtain ⟨huc,hut⟩ := memA.mp hu
    have he : D.Adj ⟨u,huc⟩ ⟨v,hvc⟩ := huv
    exact hv (memA.mpr ⟨hvc, fun hr => hut (he.reachable.trans hr)⟩)
  · intro h
    obtain ⟨_, hh⟩ := memA.mp h
    exact hh (Reachable.refl _)
omit [Fintype V] in
theorem separated_sides_disjoint {c d : V} {A B : Finset V}
    (hc : G.Connected) (hcd : c ≠ d) (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have h1 := hA.dist_add hc hxA hdA
  have h2 := hB.dist_add hc hxB hcB
  rw [G.dist_comm (u := d) (v := c)] at h2
  have hpos := hc.pos_dist_of_ne hcd
  omega
private theorem complement_count {A B : Finset V} (hab : Disjoint A B) :
    Aᶜ.card = B.card + (A ∪ B)ᶜ.card := by
  have hd : Disjoint B (A ∪ B)ᶜ := by
    apply Finset.disjoint_left.mpr
    exact fun _ hb h => (mem_compl.mp h) (mem_union_right _ hb)
  have heq : Aᶜ = B ∪ (A ∪ B)ᶜ := by
    ext v
    simp only [mem_compl,mem_union]
    have hh : ¬ (v ∈ A ∧ v ∈ B) := fun hp => Finset.disjoint_left.mp hab hp.1 hp.2
    tauto
  rw [heq,card_union_of_disjoint hd]
omit [Fintype V] [DecidableEq V] in
private theorem all_contacts_of_empty_even {c : V} {S : Finset V}
    (h : Side G c S) (hc : G.Connected)
    (ha : (S.filter (fun x => Even (G.dist c x))).card = 0) :
    ∀ x ∈ S, G.Adj c x := by
  intro x hx
  by_contra hn
  obtain ⟨y,hy,hd⟩ := h.exists_distance_two hc hx hn
  have hh : (S.filter (fun x => Even (G.dist c x))).Nonempty :=
    ⟨y,mem_filter.mpr ⟨hy,by simp [hd]⟩⟩
  have := card_pos.mpr hh
  omega
theorem middle_ball [DecidableRel G.Adj] {c d u : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G d B) (hu : u ∈ (A ∪ B)ᶜ)
    (huc : u ≠ c) (hud : u ≠ d) :
    insert u (G.neighborFinset u) ⊆ (A ∪ B)ᶜ := by
  intro v hv
  rcases mem_insert.mp hv with rfl | hv
  · exact hu
  · have he : G.Adj u v := by simpa using hv
    apply mem_compl.mpr
    intro hvab
    rcases mem_union.mp hvab with ha | hb
    · exact huc (hA.exit_eq ha he.symm (fun hh => (mem_compl.mp hu) (mem_union_left _ hh)))
    · exact hud (hB.exit_eq hb he.symm (fun hh => (mem_compl.mp hu) (mem_union_right _ hh)))
theorem middle_vertices_low [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) {u : V} (hu : u ∈ (A ∪ B)ᶜ)
    (huc : u ≠ c) (hud : u ≠ d) : G.degree u < k := by
  classical
  by_contra! high
  have hAB := separated_sides_disjoint hc hcd hA hB hdA hcB
  obtain ⟨ha2,hak,_⟩ := hA.card_bounds hc hσ horder hpair
  obtain ⟨hb2,hbk,_⟩ := hB.card_bounds hc hσ horder hpair
  have pA := hA.parity_bound hc hσ
  have pB := hB.parity_bound hc hσ
  rw [complement_count hAB] at pA
  rw [complement_count hAB.symm,union_comm B A] at pB
  have sub := middle_ball hA hB hu huc hud
  have hcard := card_le_card sub
  have huN : u ∉ G.neighborFinset u := by simp
  have hball : (insert u (G.neighborFinset u)).card = G.degree u + 1 := by
    rw [card_insert_of_notMem huN,card_neighborFinset_eq_degree]
  rw [hball] at hcard
  have hfill := eq_of_subset_of_card_le sub (by rw [hball]; omega)
  have a := all_contacts_of_empty_even hA hc (by omega)
  have b := all_contacts_of_empty_even hB hc (by omega)
  have touch (w : V) (hw : w ∈ (A ∪ B)ᶜ) (hn : w ≠ u) : G.Adj u w := by
    rw [← hfill] at hw
    simpa using (mem_insert.mp hw).resolve_left hn
  have hcg := touch c (by simp [hA.outside,hcB]) huc.symm
  have hdg := touch d (by simp [hdA,hB.outside]) hud.symm
  have unA : u ∉ A := fun hm => (mem_compl.mp hu) (mem_union_left _ hm)
  have unB : u ∉ B := fun hm => (mem_compl.mp hu) (mem_union_right _ hm)
  have hs : insert u (A ∪ B) ⊆ univ.filter (fun x => Even (G.dist u x)) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simp
    · rcases mem_union.mp hv with ha | hb
      · rw [mem_filter]
        rw [G.dist_comm (u := u) (v := v),hA.dist_add hc ha unA,
          dist_eq_one_iff_adj.mpr (a v ha).symm,dist_eq_one_iff_adj.mpr hcg.symm]
        simp
      · rw [mem_filter]
        rw [G.dist_comm (u := u) (v := v),hB.dist_add hc hb unB,
          dist_eq_one_iff_adj.mpr (b v hb).symm,dist_eq_one_iff_adj.mpr hdg.symm]
        simp
  have cap : (insert u (A ∪ B)).card ≤ 1+k :=
    (card_le_card hs).trans (hσ u)
  rw [card_insert_of_notMem (mem_compl.mp hu),card_union_of_disjoint hAB] at cap
  omega
theorem middle_card_le_three [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) : (A ∪ B)ᶜ.card ≤ 3 := by
  classical
  let Z := (A ∪ B)ᶜ
  have hcZ : c ∈ Z := by simp [Z,hA.outside,hcB]
  have hdZ : d ∈ Z := by simp [Z,hdA,hB.outside]
  have hdZ' : d ∈ Z.erase c := mem_erase.mpr ⟨hcd.symm,hdZ⟩
  have hsmall : ((Z.erase c).erase d).card ≤ 1 := by
    refine card_le_one.mpr ?_
    intro x hx y hy
    obtain ⟨hxd,hx⟩ := mem_erase.mp hx
    obtain ⟨hxc,hx⟩ := mem_erase.mp hx
    obtain ⟨hyd,hy⟩ := mem_erase.mp hy
    obtain ⟨hyc,hy⟩ := mem_erase.mp hy
    have lx := middle_vertices_low hc hσ horder hpair hcd hA hB hdA hcB hx hxc hxd
    have ly := middle_vertices_low hc hσ horder hpair hcd hA hB hdA hcB hy hyc hyd
    by_contra hne
    exact (hpair x y hne).elim (fun hh => (Nat.not_le.mpr lx) hh)
      (fun hh => (Nat.not_le.mpr ly) hh)
  rw [card_erase_of_mem hdZ',card_erase_of_mem hcZ] at hsmall
  change Z.card ≤ 3
  omega
end Graph189CutMiddle
end
section
namespace Graph189CutExtreme
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
theorem alternating_chain (left right : Finset V) (z : V)
    (hcard : left.card = right.card)
    (hdisj : ∀ x ∈ left, x ∉ right)
    (hzl : z ∉ left) (hzr : z ∉ right)
    (hcross : ∀ y ∈ right, ∀ x ∈ left, G.Adj y x)
    (hstart : left.Nonempty → ∃ x ∈ left, G.Adj z x) :
    ∃ L : List V, L.head? = some z ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ b, b ∈ L ↔ b = z ∨ b ∈ left ∨ b ∈ right := by
  by_cases hn : left.Nonempty
  · obtain ⟨x,hxl,hzx⟩ := hstart hn
    have hright : right.Nonempty := Finset.card_pos.mp (hcard ▸ Finset.card_pos.mpr hn)
    obtain ⟨y,hyr⟩ := hright
    have hyl : y ∉ left := fun hy => hdisj y hy hyr
    have hyx : G.Adj y x := hcross y hyr x hxl
    have hc' : (left.erase x).card = (right.erase y).card := by
      rw [Finset.card_erase_of_mem hxl, Finset.card_erase_of_mem hyr, hcard]
    obtain ⟨L,hhead,hnodup,hchain,hcover⟩ :=
      alternating_chain (left.erase x) (right.erase y) y hc'
        (fun b hb hr => hdisj b (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hr))
        (fun he => hyl (Finset.mem_of_mem_erase he)) (Finset.notMem_erase _ _)
        (fun b hb a ha => hcross b (Finset.mem_of_mem_erase hb) a (Finset.mem_of_mem_erase ha))
        (fun hempty => let ⟨a,ha⟩ := hempty
                       ⟨a,ha,hcross y hyr a (Finset.mem_of_mem_erase ha)⟩)
    have hxy : x ≠ y := fun e => hyl (e ▸ hxl)
    have hxright := hdisj x hxl
    have hxnot : x ∉ L := by
      rw [hcover]
      simp [hxy, hxright]
    have hzxne : z ≠ x := fun e => hzl (e.symm ▸ hxl)
    have hzyne : z ≠ y := fun e => hzr (e.symm ▸ hyr)
    have hznot : z ∉ L := by rw [hcover]; simp [hzyne, hzl, hzr]
    have hchain' : (x :: L).IsChain G.Adj := hchain.cons (by simpa [hhead] using hyx.symm)
    refine ⟨z :: x :: L, rfl, ?_, hchain'.cons (by simpa using hzx), ?_⟩
    · simp [hzxne, hznot, hxnot, hnodup]
    · intro b
      simp only [List.mem_cons, hcover, Finset.mem_erase]
      by_cases qx : b = x <;> by_cases qy : b = y <;> simp_all
  · have el : left = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have er : right = ∅ := Finset.card_eq_zero.mp (by simpa [el] using hcard.symm)
    subst left
    subst right
    exact ⟨[z],rfl,by simp,by simp,by simp⟩
termination_by left.card
decreasing_by rw [Finset.card_erase_of_mem hxl]; have hpos := Finset.card_pos.mpr hn; omega
omit [DecidableEq V] in
private theorem dist_two_of_two_edges (hc : G.Connected) {a b x : V}
    (hab : G.Adj a b) (hbx : G.Adj b x) (hne : a ≠ x) (hn : ¬ G.Adj a x) :
    G.dist a x = 2 := by
  have hlt := hc.one_lt_dist_of_ne_of_not_adj hne hn
  have hle : G.dist a x ≤ 2 := G.dist_le (.cons hab (.cons hbx .nil))
  omega
omit [DecidableEq V] in
private theorem contact_universal (hc : G.Connected) {A : Finset V}
    (ha : (G.induce (A : Set V)).Connected) {x : V} (hx : x ∈ A)
    (hn : ∀ y ∈ A, G.dist x y ≠ 2) {v : V} (hv : v ∈ A) (hnv : x ≠ v) :
    G.Adj x v := by
  by_contra hvn
  let F : Set (A : Set V) := {w | x ≠ w.val ∧ ¬ G.Adj x w.val}
  obtain ⟨P⟩ := ha (⟨v,hv⟩ : (A : Set V)) ⟨x,hx⟩
  have notx : (⟨x,hx⟩ : (A : Set V)) ∉ F := fun h => h.1 rfl
  obtain ⟨b,_,hi,ho⟩ := P.exists_boundary_dart F ⟨hnv,hvn⟩ notx
  have he : G.Adj b.fst.val b.snd.val := b.adj
  have hnext : G.Adj x b.snd.val := by
    by_contra h
    by_cases hh : x = b.snd.val
    · exact hi.2 (hh ▸ he.symm)
    · exact ho ⟨hh,h⟩
  exact hn b.fst.val b.fst.property (dist_two_of_two_edges hc hnext he.symm hi.1 hi.2)
variable [Fintype V] [DecidableRel G.Adj]
theorem rooted_at_two_k {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) {c : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G c B) (hAB : Disjoint A B)
    (hconn : (G.induce (A : Set V)).Connected) (hsize : A.card = 2*k)
    (hb : k ≤ B.card) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  classical
  have pb := hB.parity_bound hc hσ
  have hsub : insert c A ⊆ Bᶜ := by
    intro x hx
    apply mem_compl.mpr
    rcases mem_insert.mp hx with rfl | hx
    · exact hB.outside
    · exact Finset.disjoint_left.mp hAB hx
  have hcount := card_le_card hsub
  rw [card_insert_of_notMem hA.outside] at hcount
  have hBcontact : ∀ x ∈ B, G.Adj c x :=
    Graph189CutMiddle.all_contacts_of_empty_even hB hc (by omega)
  have hfull {x : V} (hx : x ∈ A) (hcx : G.Adj c x) {v : V} (hv : v ∈ A)
      (hne : x ≠ v) : G.Adj x v := by
    apply contact_universal hc hconn hx _ hv hne
    intro y hy hdy
    have hxb := Finset.disjoint_left.mp hAB hx
    have hyb := Finset.disjoint_left.mp hAB hy
    have hxy : x ≠ y := by rintro rfl; simp at hdy
    have hs : insert y (insert x B) ⊆ univ.filter (fun z => Even (G.dist x z)) := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · simp [hdy]
      rcases mem_insert.mp hz with rfl | hz
      · simp
      · have hd := hA.dist_add hc hx (fun h => Finset.disjoint_left.mp hAB h hz)
        simp [hd,dist_eq_one_iff_adj.mpr hcx.symm,dist_eq_one_iff_adj.mpr (hBcontact z hz)]
    have cap := (card_le_card hs).trans (hσ x)
    rw [card_insert_of_notMem (by simp [hxy.symm,hyb]),card_insert_of_notMem hxb] at cap
    omega
  let P := A.filter (G.Adj c ·)
  let Q := A \ P
  have hPA : P ⊆ A := filter_subset _ _
  obtain ⟨a,ha,hac⟩ := hA.contact hc
  have hQsub : insert c Q ⊆ univ.filter (fun y => Even (G.dist c y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp
    · obtain ⟨hyA,hyP⟩ := mem_sdiff.mp hy
      have hcy : ¬ G.Adj c y := fun he => hyP (mem_filter.mpr ⟨hyA,he⟩)
      have hay : a ≠ y := fun e => hcy (e ▸ hac.symm)
      have hdy := dist_two_of_two_edges hc hac.symm (hfull ha hac.symm hyA hay)
        (fun e => hA.outside (e ▸ hyA)) hcy
      simp [hdy]
  have hq := (card_le_card hQsub).trans (hσ c)
  rw [card_insert_of_notMem (fun h => hA.outside (mem_sdiff.mp h).1)] at hq
  have hsum : Q.card + P.card = A.card := card_sdiff_add_card_eq_card hPA
  change Q.card + 1 ≤ 1+k at hq
  rw [hsize] at hsum
  obtain ⟨T,hTP,hT⟩ := exists_subset_card_eq (s := P) (n := k) (by omega)
  have hTA := hTP.trans hPA
  have hTR := card_sdiff_add_card_eq_card hTA
  rw [hT,hsize] at hTR
  obtain ⟨L,hl,hn,hch,hcov⟩ := alternating_chain (G:=G) T (A \ T) c
    (by omega) (fun x hx hy => (mem_sdiff.mp hy).2 hx)
    (fun h => hA.outside (hTA h)) (fun h => hA.outside (mem_sdiff.mp h).1)
    (fun y hy x hx => (hfull (hTA hx) (mem_filter.mp (hTP hx)).2 (mem_sdiff.mp hy).1
      (fun e => (mem_sdiff.mp hy).2 (e ▸ hx))).symm)
    (fun ⟨x,hx⟩ => ⟨x,hx,(mem_filter.mp (hTP hx)).2⟩)
  refine ⟨L,hl,hn,hch,?_⟩
  intro z
  rw [hcov]
  simp only [mem_sdiff]
  have hz : z ∈ T → z ∈ A := fun h => hTA h
  tauto
end Graph189CutExtreme
end
section
namespace Graph189CutBounds
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
theorem two_le_degree [DecidableRel G.Adj] [Nontrivial V] (hc : G.Connected)
    {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k) (horder : 2*k+3 ≤ Fintype.card V)
    (v : V) : 2 ≤ G.degree v := by
  classical
  obtain ⟨a,hva⟩ := hc.preconnected.exists_adj_of_nontrivial v
  have hp : 0 < (G.neighborFinset v).card := card_pos.mpr ⟨a,by simpa using hva⟩
  by_contra! hn
  rw [← card_neighborFinset_eq_degree] at hn
  obtain ⟨c,hN⟩ := card_eq_one.mp (show (G.neighborFinset v).card = 1 by omega)
  have hadj (u : V) : G.Adj v u ↔ u = c := by
    rw [← mem_neighborFinset, hN, mem_singleton]
  have hvc := (hadj c).mpr rfl
  have S : Side G c ({v} : Finset V) := by
    refine ⟨singleton_nonempty _,by simpa using hvc.ne.symm,?_⟩
    intro x y hx he _
    have hx' : x = v := mem_singleton.mp hx
    exact (hadj _).mp (hx' ▸ he)
  have hh := S.parity_bound hc hσ
  have hs := card_add_card_compl ({v} : Finset V)
  rw [card_singleton] at hs
  omega
theorem side_card_le_two_k {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) {c : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G c B) (hAB : Disjoint A B) : A.card ≤ 2*k := by
  have hs : insert c A ⊆ Bᶜ := by
    intro y hy
    apply mem_compl.mpr
    rcases mem_insert.mp hy with rfl | hy
    · exact hB.outside
    · exact Finset.disjoint_left.mp hAB hy
  have hh := card_le_card hs
  rw [card_insert_of_notMem hA.outside] at hh
  have := hB.parity_bound hc hσ
  omega
end Graph189CutBounds
end
section
open SimpleGraph
namespace Graph189CutJoin
variable {V : Type*} {G : SimpleGraph V}
private theorem walk_of_chain {a : V} {xs : List V} (h : (a :: xs).IsChain G.Adj) :
    ∃ b, ∃ w : G.Walk a b, w.support = a :: xs := by
  induction xs generalizing a with
  | nil => exact ⟨a, .nil, rfl⟩
  | cons x xs ih =>
    obtain ⟨e, ht⟩ := List.isChain_cons_cons.mp h
    obtain ⟨b, w, hw⟩ := ih ht
    exact ⟨b, .cons e w, by simp [hw]⟩
theorem hamiltonian_of_rooted_sides [DecidableEq V] {c : V} {A B : Finset V}
    (hdis : Disjoint A B) (hcover : ∀ x, x=c ∨ x∈A ∨ x∈B)
    (rootA : ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x∈L ↔ x=c ∨ x∈A)
    (rootB : ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x∈L ↔ x=c ∨ x∈B) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨left, hlhead, hln, hlc, hlm⟩ := rootA
  obtain ⟨right, hrhead, hrn, hrc, hrm⟩ := rootB
  cases left with
  | nil => simp at hlhead
  | cons l ls =>
    simp only [List.head?_cons, Option.some.injEq] at hlhead
    subst l
    cases right with
    | nil => simp at hrhead
    | cons r rs =>
      simp only [List.head?_cons, Option.some.injEq] at hrhead
      subst r
      obtain ⟨a, p, hp⟩ := walk_of_chain hlc
      obtain ⟨b, q, hq⟩ := walk_of_chain hrc
      refine ⟨a, b, p.reverse.append q, ?_⟩
      intro x
      simp only [Walk.support_append, Walk.support_reverse, hp, hq, List.tail_cons,
        List.count_append, List.count_reverse]
      by_cases hx : x ∈ c :: ls
      · have hr : x ∉ rs := by
          intro hxr
          have hne : x ≠ c := fun he => (List.nodup_cons.mp hrn).1 (he ▸ hxr)
          have ha := (hlm x).mp hx
          have hb := (hrm x).mp (List.mem_cons_of_mem _ hxr)
          exact Finset.disjoint_left.mp hdis (ha.resolve_left hne) (hb.resolve_left hne)
        simp [List.count_eq_one_of_mem hln hx, List.count_eq_zero_of_not_mem hr]
      · have hne : x ≠ c := fun he => hx (he ▸ List.mem_cons_self)
        have hb : x∈B := ((hcover x).resolve_left hne).resolve_left
          (fun ha => hx ((hlm x).mpr (.inr ha)))
        have hxr : x ∈ rs := (List.mem_cons.mp ((hrm x).mpr (.inr hb))).resolve_left hne
        simp [List.count_eq_zero_of_not_mem hx, List.count_eq_one_of_mem
          (List.nodup_cons.mp hrn).2 hxr]
end Graph189CutJoin
end
section
namespace Graph189CutH1Assembly
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
theorem h1_of_small_rooted (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    (hcut : ∃ c : V, ¬ (G.induce {v | v ≠ c}).Connected)
    (small : ∀ {c : V} {A : Finset V}, Side G c A →
      A.card ≤ 2 * G.secondSmallestDegree - 1 →
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ A) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨c,cc⟩ := hcut
  have htwo := Graph189CutInterface.components_after_cut_eq_two hc hσ horder cc
  obtain ⟨A,B,hA,hB,hAB,hcover,hconnA,hconnB⟩ := Graph189CutExtract.two_connected_sides c htwo
  have roots {S T : Finset V} (hs : Side G c S) (ht : Side G c T) (hd : Disjoint S T)
      (hconn : (G.induce (S : Set V)).Connected) :
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ S := by
    have hu := Graph189CutBounds.side_card_le_two_k hc hσ hs ht hd
    by_cases heq : S.card = 2 * G.secondSmallestDegree
    · have hlo := (ht.card_bounds hc hσ horder (Graph189CutCore.degree_pair (G := G))).2.1
      exact Graph189CutExtreme.rooted_at_two_k hc hσ hs ht hd hconn heq hlo
    · exact small hs (by omega)
  exact Graph189CutJoin.hamiltonian_of_rooted_sides hAB hcover (roots hA hB hAB hconnA)
    (roots hB hA hAB.symm hconnB)
end Graph189CutH1Assembly
end
section
namespace Graph189InducedSide
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]
abbrev sideVerts (c : V) (A : Finset V) : Set V := ↑(insert c A)
abbrev sideGraph (G : SimpleGraph V) (c : V) (A : Finset V) := G.induce (sideVerts c A)
abbrev sideRoot (c : V) (A : Finset V) : sideVerts c A := ⟨c, Finset.mem_insert_self ..⟩
theorem degree_side [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {A : Finset V} (hA : Graph189CutCore.Side G c A)
    (u : sideVerts c A) (hu : u ≠ sideRoot c A) :
    (sideGraph G c A).degree u = G.degree u.val := by
  have hx : u.val ≠ c := fun e => hu (Subtype.ext e)
  have ha : u.val ∈ A := (Finset.mem_insert.mp u.property).resolve_left hx
  have hsub : G.neighborSet u.val ⊆ sideVerts c A := by
    intro v hv
    by_cases hva : v ∈ A
    · exact Finset.mem_insert_of_mem hva
    · exact Finset.mem_insert.mpr (.inl (hA.exit_eq ha hv hva))
  convert SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := sideVerts c A)
    (v := u) hsub using 1
  congr 1
  exact Subsingleton.elim _ _
theorem card_side [Fintype V] {G : SimpleGraph V} {c : V} {A : Finset V}
    (hA : Graph189CutCore.Side G c A) : Fintype.card (sideVerts c A) = A.card + 1 := by
  change Fintype.card ↥(insert c A) = _
  exact (Fintype.card_coe (insert c A)).trans (Finset.card_insert_of_notMem hA.outside)
theorem lift_rooted_list {G : SimpleGraph V} {c : V} {A : Finset V}
    (rooted : ∃ L : List (sideVerts c A), L.head? = some (sideRoot c A) ∧
      L.Nodup ∧ L.IsChain (sideGraph G c A).Adj ∧ ∀ u, u ∈ L) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  obtain ⟨L, hhead, hn, hchain, hall⟩ := rooted
  refine ⟨L.map Subtype.val, ?_, hn.map Subtype.val_injective, ?_, ?_⟩
  · simp [List.head?_map, hhead]
  · exact (List.isChain_map Subtype.val).mpr hchain
  · intro x
    constructor
    · intro hx
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      exact Finset.mem_insert.mp u.property
    · intro hx
      let u : sideVerts c A := ⟨x, Finset.mem_insert.mpr hx⟩
      exact List.mem_map.mpr ⟨u, hall u, rfl⟩
theorem small_side_of_induced [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {A : Finset V} {k : ℕ} (hA : Graph189CutCore.Side G c A)
    (hconn : G.Connected) (hsize : A.card + 1 ≤ 2*k)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    (htwo : ∀ x : V, 2 ≤ G.degree x)
    (produce :
      Fintype.card (sideVerts c A) ≤ 2*k →
      (∃ u, (sideGraph G c A).Adj (sideRoot c A) u) →
      (∀ u v : sideVerts c A, u ≠ sideRoot c A → v ≠ sideRoot c A → u ≠ v →
        k ≤ (sideGraph G c A).degree u ∨ k ≤ (sideGraph G c A).degree v) →
      (∀ u : sideVerts c A, u ≠ sideRoot c A → 2 ≤ (sideGraph G c A).degree u) →
      ∃ L : List (sideVerts c A), L.head? = some (sideRoot c A) ∧ L.Nodup ∧
        L.IsChain (sideGraph G c A).Adj ∧ ∀ u, u ∈ L) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  apply lift_rooted_list
  apply produce
  · rw [card_side hA]
    exact hsize
  · obtain ⟨x, hx, hxc⟩ := hA.contact hconn
    exact ⟨⟨x, Finset.mem_insert_of_mem hx⟩, hxc.symm⟩
  · intro u v hur hvr huv
    rw [degree_side hA u hur, degree_side hA v hvr]
    exact hpair u.val v.val (fun h => huv (Subtype.ext h))
  · intro u hur
    simpa [degree_side hA u hur] using htwo u.val
end Graph189InducedSide
end
section
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
end Graph189
end
section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*}
def marked (G : SimpleGraph V) (c : V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some y => y = c
    | some x, none => x = c
    | some x, some y => G.Adj x y
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    intro x
    cases x
    · exact id
    · exact G.loopless.irrefl _
end Graph189SmallRoot
end
section
namespace Graph189SmallRoot
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem trace_of_clique_extension {G : SimpleGraph V} [DecidableRel G.Adj]
    (high : V → Prop) (k : ℕ) (horder : Fintype.card V ≤ 2 * k + 1)
    (hdegree : ∀ x, high x → k ≤ G.degree x)
    (finish : ∀ K : SimpleGraph V, G ≤ K →
      (∀ x y, high x → high y → x ≠ y → K.Adj x y) →
      ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let T (K : SimpleGraph V) := ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian
  change T G
  by_contra hn
  obtain ⟨K, hGK, hm⟩ := Finite.exists_le_maximal (p := fun K => ¬ T K) hn
  apply hm.prop
  apply finish K hGK
  intro x y hx hy hne
  have mono (v : V) : G.degree v ≤ K.degree v := by
    apply Finset.card_le_card
    intro u hu
    exact (K.mem_neighborFinset _ _).mpr (hGK ((G.mem_neighborFinset _ _).mp hu))
  have hsum : Fintype.card V ≤ K.degree x + K.degree y + 1 := by
    have := (hdegree x hx).trans (mono x)
    have := (hdegree y hy).trans (mono y)
    omega
  by_contra hxy
  have hnot : ¬ T (K ⊔ edge x y) := fun hp =>
    hm.prop (Graph189.traceable_of_sup_edge hne hxy hsum hp)
  exact hxy (hm.le_of_ge hnot le_sup_left
    (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)))
omit [Fintype V] in
private theorem prefix_marker {G : SimpleGraph V} {c : V} {K : SimpleGraph (Option V)}
    (hGK : marked G c ≤ K) (L : List V) (hhead : L.head? = some c)
    (hnodup : L.Nodup) (hchain : L.IsChain (K.comap some).Adj)
    (hcover : ∀ v : V, v ∈ L) : ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian := by
  let W : List (Option V) := none :: L.map some
  have hWn : W.Nodup := List.nodup_cons.mpr ⟨by simp, hnodup.map (Option.some_injective V)⟩
  have hc : W.IsChain K.Adj := by
    apply List.isChain_cons.mpr
    refine ⟨?_, (List.isChain_map _).mpr hchain⟩
    intro y hy
    have he : some c = y := by simpa [List.head?_map,hhead] using hy
    subst y
    exact hGK (show (marked G c).Adj none (some c) from rfl)
  have hw (v : Option V) : v ∈ W := by
    cases v with
    | none => simp [W]
    | some x => simp [W,hcover x]
  let path := SimpleGraph.Walk.ofSupport W (by simp [W]) hc
  have hs : path.support = W := Walk.support_ofSupport _ hc
  exact ⟨_, _, path, (Walk.IsPath.mk' (hs.symm ▸ hWn)).isHamiltonian_of_mem
    (fun v => hs.symm ▸ hw v)⟩
theorem marked_trace_at_small_root_of_finish
    (finishClique : ∀ {Q : SimpleGraph V} (A : Finset V) {c : V}, c ∉ A →
      (∃ u ∈ A, Q.Adj c u) →
      ((∀ {u v}, u ∈ A → v ∈ A → u ≠ v → Q.Adj u v) ∨
        ∃ z ∈ A, ∀ {u v}, u ∈ A.erase z → v ∈ A.erase z → u ≠ v → Q.Adj u v) →
      (∀ u ∈ A, ∃ x ∈ insert c A, ∃ y ∈ insert c A, x ≠ y ∧ Q.Adj u x ∧ Q.Adj u y) →
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain Q.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ A)
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (k : ℕ)
    (hsize : Fintype.card V ≤ 2*k) (hc : ∃ u, G.Adj c u)
    (hpair : ∀ u v, u ≠ c → v ≠ c → u ≠ v → k ≤ G.degree u ∨ k ≤ G.degree v)
    (htwo : ∀ u, u ≠ c → 2 ≤ G.degree u) :
    ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian := by
  classical
  let H (u : Option V) := ∃ v : V, u = some v ∧ k ≤ G.degree v
  apply trace_of_clique_extension H k
  · rw [Fintype.card_option]
    omega
  · intro u hu
    obtain ⟨v,rfl,hv⟩ := hu
    apply hv.trans
    rw [← G.card_neighborSet_eq_degree v, ← (marked G c).card_neighborSet_eq_degree _]
    let f (y : G.neighborSet v) : (marked G c).neighborSet (some v) :=
      ⟨some y.val, y.property⟩
    apply Fintype.card_le_of_injective f
    intro s t eq
    exact Subtype.ext (Option.some.inj (congrArg Subtype.val eq))
  · intro K hGK hK
    let Q := K.comap (some : V → Option V)
    have hGQ : G ≤ Q := by
      intro x y h
      exact hGK (show (marked G c).Adj (some x) (some y) from h)
    let A : Finset V := univ.erase c
    have hA (u : V) : u ∈ A ↔ u ≠ c := by simp [A]
    have hi (u : V) : u ∈ insert c A := by by_cases h : u = c <;> simp [A,h]
    have hhigh {u v : V} (hu : k ≤ G.degree u) (hv : k ≤ G.degree v) (hne : u ≠ v) :
        Q.Adj u v :=
      hK (some u) (some v) ⟨u,rfl,hu⟩ ⟨v,rfl,hv⟩ (fun e => hne (Option.some.inj e))
    apply Exists.elim (finishClique (Q := Q) A (c := c) (by simp [A]) _ _ _)
    · intro L hL
      exact prefix_marker hGK L hL.1 hL.2.1 hL.2.2.1 (fun x => (hL.2.2.2 x).mpr
        (by by_cases e : x = c; exact Or.inl e; exact Or.inr ((hA x).mpr e)))
    · obtain ⟨u,hu⟩ := hc
      exact ⟨u,(hA u).mpr hu.ne.symm,hGQ hu⟩
    · by_cases hall : ∀ u ∈ A, k ≤ G.degree u
      · exact Or.inl (fun hx hy hxy => hhigh (hall _ hx) (hall _ hy) hxy)
      · push Not at hall
        obtain ⟨z,hz,hlow⟩ := hall
        have high {u : V} (hu : u ∈ A.erase z) : k ≤ G.degree u := by
          obtain ⟨hne,hin⟩ := mem_erase.mp hu
          exact (hpair u z ((hA u).mp hin) ((hA z).mp hz) hne).resolve_right
            (by omega)
        exact Or.inr ⟨z,hz,(fun hu hv hne => hhigh (high hu) (high hv) hne)⟩
    · intro u hu
      have hd : 1 < (G.neighborFinset u).card := by
        rw [G.card_neighborFinset_eq_degree]
        exact htwo u ((hA u).mp hu)
      obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp hd
      exact ⟨x,hi x,y,hi y,ne,hGQ ((G.mem_neighborFinset u x).mp hx),
        hGQ ((G.mem_neighborFinset u y).mp hy)⟩
end Graph189SmallRoot
end
section
namespace Graph189
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
omit [DecidableEq V] in
private theorem chain_of_clique_list {s : V → Prop} {L : List V}
    (hn : L.Nodup) (hm : ∀ x ∈ L, s x)
    (hclique : ∀ {u v}, s u → s v → u ≠ v → G.Adj u v) :
    L.IsChain G.Adj :=
  List.Pairwise.isChain (hn.imp_of_mem (fun {_ _} ha hb hne =>
    hclique (hm _ ha) (hm _ hb) hne))
theorem rootedCliqueList (s : Finset V) {r : V} (hr : r ∈ s)
    (hclique : ∀ {u v}, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x ∈ s := by
  let L := r :: (s.erase r).toList
  have hm (x : V) : x ∈ L ↔ x ∈ s := by
    by_cases hx : x = r <;> simp [L, hx, hr]
  have hn : L.Nodup := List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  exact ⟨L, rfl, hn, chain_of_clique_list hn (fun x hx => (hm x).mp hx) hclique, hm⟩
theorem rootedCliqueBetweenList (s : Finset V) {r t : V}
    (hr : r ∈ s) (ht : t ∈ s) (hrt : r ≠ t)
    (hclique : ∀ {u v}, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) :
    ∃ L : List V, L.head? = some r ∧ L.getLast? = some t ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ ∀ x, x ∈ L ↔ x ∈ s := by
  let L := r :: (((s.erase r).erase t).toList ++ [t])
  have hm (x : V) : x ∈ L ↔ x ∈ s := by
    by_cases hxr : x = r
    · simp [L, hxr, hr]
    by_cases hxt : x = t
    · simp [L, hxt, ht]
    · simp [L, hxr, hxt]
  have hn : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨by simp [hrt], List.nodup_append.mpr ⟨Finset.nodup_toList _, by simp, ?_⟩⟩
    intro x hx y hy hxy
    have hyt : y = t := by simpa using hy
    exact (Finset.mem_erase.mp (Finset.mem_toList.mp hx)).1 (hxy.trans hyt)
  have hlast : L.getLast? = some t := by simp [L, List.getLast?_cons, List.getLast?_append]
  exact ⟨L, rfl, hlast, hn, chain_of_clique_list hn (fun x hx => (hm x).mp hx) hclique, hm⟩
theorem rootedCliqueExceptList (s : Finset V) {r z : V}
    (hr : r ∈ s) (hz : z ∈ s)
    (hclique : ∀ {u v}, u ∈ s.erase z → v ∈ s.erase z → u ≠ v → G.Adj u v)
    (hcontact : ∃ u ∈ s.erase z, G.Adj z u ∧ (r = z ∨ r ≠ u)) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x ∈ s := by
  obtain ⟨u, hu, hzu, hroot⟩ := hcontact
  by_cases hrz : r = z
  · subst r
    obtain ⟨L, hhead, hn, hc, hm⟩ := rootedCliqueList (G := G) (s.erase z) hu hclique
    refine ⟨z :: L, rfl, ?_, ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨fun hmz => (Finset.mem_erase.mp ((hm z).mp hmz)).1 rfl, hn⟩
    · exact hc.cons (by simpa [hhead] using hzu)
    · intro x
      by_cases hx : x = z <;> simp [hx, hz, hm]
  · have hru : r ≠ u := hroot.resolve_left hrz
    obtain ⟨L, hhead, hlast, hn, hc, hm⟩ :=
      rootedCliqueBetweenList (G := G) (s.erase z) (Finset.mem_erase.mpr ⟨hrz,hr⟩) hu hru hclique
    refine ⟨L ++ [z], ?_, ?_, ?_, ?_⟩
    · have hne : L ≠ [] := by intro he; simp [he] at hhead
      rwa [List.head?_append_of_ne_nil _ hne]
    · apply List.nodup_append.mpr
      refine ⟨hn, by simp, ?_⟩
      intro x hx y hy hxy
      have hyz : y = z := by simpa using hy
      exact (Finset.mem_erase.mp ((hm x).mp hx)).1 (hxy.trans hyz)
    · apply hc.append (List.IsChain.singleton z)
      intro x hx y hy
      have hux : u = x := by simpa [hlast] using hx
      have hzy : z = y := by simpa using hy
      exact hux ▸ hzy ▸ hzu.symm
    · intro x
      by_cases hx : x = z <;> simp [hx, hz, hm]
theorem rootedGateCliqueList (A : Finset V) {c : V} (hc : c ∉ A)
    (hcontact : ∃ u ∈ A, G.Adj c u)
    (hshape : (∀ {u v}, u ∈ A → v ∈ A → u ≠ v → G.Adj u v) ∨
      ∃ z ∈ A, ∀ {u v}, u ∈ A.erase z → v ∈ A.erase z → u ≠ v → G.Adj u v)
    (htwo : ∀ u ∈ A, ∃ x ∈ insert c A, ∃ y ∈ insert c A,
      x ≠ y ∧ G.Adj u x ∧ G.Adj u y) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  suffices h : ∃ u, G.Adj c u ∧ ∃ L : List V, L.head? = some u ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ ∀ x, x ∈ L ↔ x ∈ A by
    obtain ⟨u, hcu, L, hhead, hn, hchain, hm⟩ := h
    refine ⟨c :: L, rfl, List.nodup_cons.mpr ⟨fun h => hc ((hm c).mp h), hn⟩, ?_, ?_⟩
    · exact hchain.cons (by simpa [hhead] using hcu)
    · intro x
      simp [hm, eq_comm]
  obtain ⟨u, hu, hcu⟩ := hcontact
  rcases hshape with hclique | ⟨z, hz, hclique⟩
  · exact ⟨u, hcu, rootedCliqueList (G := G) A hu hclique⟩
  obtain ⟨x, hx, y, hy, hxy, hzx, hzy⟩ := htwo z hz
  by_cases hcz : G.Adj c z
  · refine ⟨z, hcz, rootedCliqueExceptList (G := G) A hz hz hclique ?_⟩
    by_cases hxc : x = c
    · have hyc : y ≠ c := fun he => hxy (hxc.trans he.symm)
      exact ⟨y, Finset.mem_erase.mpr ⟨hzy.ne.symm, (Finset.mem_insert.mp hy).resolve_left hyc⟩,
        hzy, Or.inl rfl⟩
    · exact ⟨x, Finset.mem_erase.mpr ⟨hzx.ne.symm, (Finset.mem_insert.mp hx).resolve_left hxc⟩,
        hzx, Or.inl rfl⟩
  · refine ⟨u, hcu, rootedCliqueExceptList (G := G) A hu hz hclique ?_⟩
    have hxc : x ≠ c := fun he => hcz (he ▸ hzx).symm
    have hyc : y ≠ c := fun he => hcz (he ▸ hzy).symm
    by_cases hxu : x = u
    · have huy : u ≠ y := fun he => hxy (hxu.trans he)
      exact ⟨y, Finset.mem_erase.mpr ⟨hzy.ne.symm, (Finset.mem_insert.mp hy).resolve_left hyc⟩,
        hzy, Or.inr huy⟩
    · exact ⟨x, Finset.mem_erase.mpr ⟨hzx.ne.symm, (Finset.mem_insert.mp hx).resolve_left hxc⟩,
        hzx, Or.inr (fun he => hxu he.symm)⟩
end Graph189
end
section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem marked_trace_at_small_root
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (k : ℕ)
    (hsize : Fintype.card V ≤ 2*k) (hc : ∃ u, G.Adj c u)
    (hpair : ∀ u v, u ≠ c → v ≠ c → u ≠ v → k ≤ G.degree u ∨ k ≤ G.degree v)
    (htwo : ∀ u, u ≠ c → 2 ≤ G.degree u) :
    ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian := by
  apply marked_trace_at_small_root_of_finish _ G c k hsize hc hpair htwo
  intro Q A root out contact shape two
  exact Graph189.rootedGateCliqueList A out contact shape two
end Graph189SmallRoot
end
section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {c : V}
private theorem contact_eq {a : Option V} (h : (marked G c).Adj a none) :
    a = some c := by
  cases a with
  | none => exact False.elim h
  | some a => exact congrArg some h
private theorem endpoint : ∀ (l : List (Option V)), l.Nodup →
    l.IsChain (marked G c).Adj → none ∈ l →
    l.head? = some none ∨ l.getLast? = some none
  | [], _, _, hm => by simp at hm
  | [a], _, _, hm => by
    have h : none = a := by simpa using hm
    exact Or.inl (by simp [← h])
  | a :: b :: l, hn, hc, hm => by
    by_cases ha : a = none
    · exact Or.inl (by simp [ha])
    have mem : none ∈ b :: l := (List.mem_cons.mp hm).resolve_left (Ne.symm ha)
    rcases endpoint (b :: l) (List.nodup_cons.mp hn).2
        (List.isChain_cons_cons.mp hc).2 mem with first | last
    · have hb : b = none := by simpa using first
      subst b
      cases l with
      | nil => exact Or.inr (by simp)
      | cons d t =>
        have links := List.isChain_cons_cons.mp hc
        have ad : a = d := (contact_eq links.1).trans
          (contact_eq (List.isChain_cons_cons.mp links.2).1.symm).symm
        exact False.elim ((List.nodup_cons.mp hn).1 (by simp [ad]))
    · exact Or.inr (by simpa using last)
private theorem all_some : ∀ (l : List (Option V)), none ∉ l →
    ∃ s : List V, l = s.map some
  | [], _ => ⟨[], rfl⟩
  | none :: _, hn => False.elim (hn (by simp))
  | some x :: xs, hn => by
    obtain ⟨ys, hy⟩ := all_some xs (fun h => hn (List.mem_cons_of_mem _ h))
    exact ⟨x :: ys, by simp [hy]⟩
theorem rooted_of_marked_traceable [DecidableEq V]
    (h : ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧ ∀ v, v ∈ L := by
  obtain ⟨_, _, p, hp⟩ := h
  have orient : ∃ l : List (Option V), l.head? = some none ∧ l.Nodup ∧
      l.IsChain (marked G c).Adj ∧ ∀ w, w ∈ l := by
    rcases endpoint p.support hp.isPath.support_nodup p.isChain_adj_support
      (hp.mem_support none) with left | right
    · exact ⟨_, left, hp.isPath.support_nodup, p.isChain_adj_support, hp.mem_support⟩
    · refine ⟨p.support.reverse, by simpa using right, by simpa using hp.isPath.support_nodup,
        List.isChain_reverse.mpr (p.isChain_adj_support.imp fun _ _ e => e.symm), ?_⟩
      simpa using hp.mem_support
  obtain ⟨l, first, nodup, chain, full⟩ := orient
  cases l with
  | nil => simp at first
  | cons m r =>
    have hm : m = none := by simpa using first
    subst m
    obtain ⟨s, rfl⟩ := all_some r (List.nodup_cons.mp nodup).1
    have all (v : V) : v ∈ s := by simpa using full (some v)
    have sc : s.IsChain G.Adj :=
      (List.isChain_map some).mp chain.tail
    refine ⟨s, ?_, List.Nodup.of_map some (List.nodup_cons.mp nodup).2, sc, all⟩
    cases s with
    | nil => exact False.elim (by simpa using all c)
    | cons x xs =>
      have hxc : x = c := (List.isChain_cons_cons.mp chain).1
      simp [hxc]
end Graph189SmallRoot
end
section
namespace Graph189CutH1
open SimpleGraph Graph189CutCore Graph189InducedSide Graph189SmallRoot
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
theorem cut_vertex_case (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    (hcut : ∃ c : V, ¬ (G.induce {v | v ≠ c}).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  apply Graph189CutH1Assembly.h1_of_small_rooted hc hσ horder hcut
  intro c A hA hsize
  have hp := Finset.card_pos.mpr hA.nonempty
  apply small_side_of_induced (k := G.secondSmallestDegree) hA hc (by omega)
    (Graph189CutCore.degree_pair (G := G)) (Graph189CutBounds.two_le_degree hc hσ horder)
  intro hsz hcontact hpair htwo
  apply rooted_of_marked_traceable
  exact marked_trace_at_small_root (sideGraph G c A) (sideRoot c A)
    G.secondSmallestDegree hsz hcontact hpair htwo
end Graph189CutH1
end
end

section
section
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2
section Aux
open SimpleGraph OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma h11 [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V) : ∀ v, 2 ≤ G.degree v := by
  classical
  intro v
  by_contra hlt
  push Not at hlt
  have hpos : 0 < G.degree v := by
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := hconn.preconnected v w
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ =>
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨_, (mem_neighborFinset _ _ _).mpr h⟩
  have h1 : G.degree v = 1 := by omega
  obtain ⟨c', hc', huniq⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp h1
  have hdist : ∀ w, w ≠ v → G.dist v w = 1 + G.dist c' w := by
    intro w hw
    apply le_antisymm
    · have := hconn.dist_triangle (u := v) (v := c') (w := w)
      have h2 : G.dist v c' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hc'
      omega
    · obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v w
      cases p with
      | nil => exact absurd rfl hw
      | @cons _ z _ h q =>
        have hz : z = c' := huniq z h
        subst hz
        have := SimpleGraph.dist_le q
        simp only [Walk.length_cons] at hp
        omega
  have key : ∀ w, Even (G.dist c' w) ↔ ¬ Even (G.dist v w) := by
    intro w
    by_cases hw : w = v
    · subst hw
      have : G.dist c' w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hc'.symm
      simp [this]
    · rw [hdist w hw, Nat.even_iff, Nat.even_iff]
      omega
  have hsum : distEven G v + distEven G c' = Fintype.card V := by
    unfold distEven
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun w => Even (G.dist v w))
    simp only [key] at *
    rw [Finset.card_univ] at this
    simpa [key] using this
  have := hH v
  have := hH c'
  omega
lemma sigma_ge [Nontrivial V] [DecidableRel G.Adj] (h : ∀ v, 2 ≤ G.degree v) :
    2 ≤ secondSmallestDegree G := by
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hmem : secondSmallestDegree G ∈ degreeSequence G := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  simp only [degreeSequence, Multiset.mem_sort, Multiset.mem_map] at hmem
  obtain ⟨v, -, hv⟩ := hmem
  rw [← hv]; exact h v
lemma lemma4x [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
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
      (fun v hv => List.mem_cons_of_mem _ hv)
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
    have := hmax _ hnd hch (fun v hv => List.mem_append_left _ hv)
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
      have := hmax _ hnd' hch' (fun v hv => List.mem_cons_of_mem _
        ((hc'p.trans hperm).mem_iff.mpr hv))
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
lemma longer_of_perm_x (l : List V) (hnd : l.Nodup)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) {c : List V} (hc : c.Perm (y :: l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : c.Nodup := hc.nodup_iff.mpr (List.nodup_cons.2 ⟨hy, hnd⟩)
  have := hmax c hnd' hch (fun v hv => hc.mem_iff.mpr (List.mem_cons_of_mem _ hv))
  rw [hc.length_eq] at this
  simp only [List.length_cons] at this
  omega
lemma no_insert_x (l : List V) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (k : ℕ) (hk0 : 0 < k) (hk : k < l.length)
    (h1 : G.Adj (l[k - 1]'(by omega)) y) (h2 : G.Adj y (l[k]'hk)) : False := by
  refine longer_of_perm_x l hnd hmax y hy (c := l.take k ++ y :: l.drop k)
    (List.perm_middle.trans ?_) ?_
  · rw [List.take_append_drop]
  · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
    · refine List.isChain_cons.2 ⟨?_, hch.drop _⟩
      intro z hz
      rw [List.head?_drop, List.getElem?_eq_getElem hk] at hz
      simp only [Option.mem_def, Option.some.injEq] at hz
      subst hz
      exact h2
    · intro x hx z hz
      rw [List.getLast?_take, if_neg (by omega)] at hx
      simp only [List.getElem?_eq_getElem (by omega : k - 1 < l.length), Option.some_or,
        Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hx hz
      exact h1
lemma lemma5abx [DecidableRel G.Adj] (hconn : G.Connected) (l : List V) (hne : l ≠ [])
    (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) (j : ℕ) (hj : j < l.length) (hadj : G.Adj y (l.getD j y)) :
    0 < j ∧ j + 1 < l.length ∧ ¬ G.Adj y (l.getD (j + 1) y) ∧ ¬ G.Adj y (l.getD (j - 1) y) ∧
      ¬ G.Adj (l.head hne) (l.getD (j + 1) y) ∧ ¬ G.Adj (l.getLast hne) (l.getD (j - 1) y) := by
  have hjd : l.getD j y = l[j] := List.getD_eq_getElem _ _ hj
  rw [hjd] at hadj
  have hlast : l.getLast hne = l[l.length - 1]'(by omega) := List.getLast_eq_getElem _
  have hhead : l.head hne = l[0]'(by omega) := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have h0 : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    subst hj0
    refine longer_of_perm_x l hnd hmax y hy (c := y :: l) (List.Perm.refl _) ?_
    refine List.IsChain.cons_of_ne_nil hne hch ?_
    rw [hhead]
    exact hadj
  have h1 : j + 1 < l.length := by
    by_contra h
    have hjl : j = l.length - 1 := by omega
    subst hjl
    refine longer_of_perm_x l hnd hmax y hy (c := l ++ [y]) (List.perm_append_comm.trans (List.Perm.refl _)) ?_
    refine List.isChain_append.2 ⟨hch, List.isChain_singleton _, ?_⟩
    intro x hx y' hy'
    rw [List.getLast?_eq_some_getLast hne] at hx
    simp at hx hy'
    subst hx hy'
    rw [hlast]
    exact hadj.symm
  refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ h1]
    intro hadj2
    exact no_insert_x l hnd hch hmax y hy (j + 1) (by omega) h1 (by simpa using hadj.symm) hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length)]
    intro hadj2
    exact no_insert_x l hnd hch hmax y hy j h0 hj hadj2.symm hadj
  · rw [List.getD_eq_getElem _ _ h1, hhead]
    intro hadj2
    refine longer_of_perm_x l hnd hmax y hy
      (c := y :: ((l.take (j + 1)).reverse ++ l.drop (j + 1))) ?_ ?_
    · refine List.Perm.cons _ ?_
      exact ((List.reverse_perm _).append_right _).trans (by rw [List.take_append_drop])
    · refine List.isChain_cons.2 ⟨?_, ?_⟩
      · intro z hz
        rw [List.head?_append, List.head?_reverse] at hz
        have e : (l.take (j + 1)).getLast? = some l[j] := by
          rw [List.getLast?_take]
          simp [List.getElem?_eq_getElem hj]
        rw [e] at hz
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hz
        subst hz
        exact hadj.symm.symm
      · refine List.isChain_append.2 ⟨?_, hch.drop _, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.take _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [List.getLast?_reverse] at hx
          rw [List.head?_drop, List.getElem?_eq_getElem h1] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hz
          have : (l.take (j + 1)).head? = some l[0] := by
            rw [List.head?_take, if_neg (by omega), List.head?_eq_some_head hne, hhead]
          rw [this] at hx
          simp only [Option.some.injEq] at hx
          subst hx
          exact hadj2
  · rw [List.getD_eq_getElem _ _ (by omega : j - 1 < l.length), hlast]
    intro hadj2
    refine longer_of_perm_x l hnd hmax y hy
      (c := (l.take j ++ (l.drop j).reverse) ++ [y]) ?_ ?_
    · refine List.perm_append_singleton _ _ |>.trans (List.Perm.cons _ ?_)
      exact (List.Perm.append_left _ (List.reverse_perm _)).trans (by rw [List.take_append_drop])
    · have e1 : (l.take j).getLast? = some l[j - 1] := by
        rw [List.getLast?_take, if_neg (by omega)]
        simp [List.getElem?_eq_getElem (by omega : j - 1 < l.length)]
      have e2 : (l.drop j).reverse.head? = some l[l.length - 1] := by
        rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega),
          List.getLast?_eq_some_getLast hne, hlast]
      refine List.isChain_append.2 ⟨?_, List.isChain_singleton _, ?_⟩
      · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
        · rw [List.isChain_reverse]
          exact (hch.drop _).imp (fun a b h => h.symm)
        · intro x hx z hz
          rw [e1] at hx
          rw [e2] at hz
          simp only [Option.mem_def, Option.some.injEq] at hx hz
          subst hx hz
          exact hadj2.symm
      · intro x hx z hz
        simp at hz
        subst hz
        have e3 : (l.take j ++ (l.drop j).reverse).getLast? = some l[j] := by
          rw [List.getLast?_append, List.getLast?_reverse, List.head?_drop,
            List.getElem?_eq_getElem hj]
          rfl
        rw [e3] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact hadj.symm
lemma exists_longest_x0 [DecidableRel G.Adj] (x₀ : V) :
    ∃ l : List V, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
      ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length := by
  classical
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l) ∧ l.length = k
  have h1 : PP 1 := ⟨[x₀], ⟨by simp, List.isChain_singleton _, by simp⟩, rfl⟩
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x₀⟩
  obtain ⟨l, ⟨hlnd, hlch, hlx⟩, hlM⟩ := Nat.findGreatest_spec (P := PP) hpos h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' →
      l'.length ≤ Nat.findGreatest PP (Fintype.card V) :=
    fun l' a b c => Nat.le_findGreatest a.length_le_card ⟨l', ⟨a, b, c⟩, rfl⟩
  exact ⟨l, List.ne_nil_of_mem hlx, hlnd, hlch, hlx, fun l' a b c => hlM ▸ hmax l' a b c⟩
lemma chain_rev {l : List V} (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj := by
  rw [List.isChain_reverse]
  exact h.imp (fun a b h => h.symm)
lemma rot_head [DecidableRel G.Adj] (x₀ : V) (hδ : ∀ v, 2 ≤ G.degree v) (l : List V)
    (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj) (hx : x₀ ∈ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hh : l.head hne = x₀) :
    ∃ l' : List V, ∃ h : l' ≠ [], l'.Nodup ∧ l'.IsChain G.Adj ∧ x₀ ∈ l' ∧
      l'.length = l.length ∧ l'.head h ≠ x₀ ∧ l'.getLast h ≠ x₀ := by
  classical
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    have hax : a = x₀ := hh
    subst hax
    have hxt : a ∉ t := (List.nodup_cons.mp hnd).1
    have hnt : t.Nodup := (List.nodup_cons.mp hnd).2
    have hnbr : ∀ y, G.Adj a y → y ∈ t := by
      intro y hy
      by_contra hyt
      have hyl : y ∉ a :: t := by
        simp only [List.mem_cons, not_or]
        exact ⟨hy.ne.symm, hyt⟩
      have := hmax (y :: a :: t) (List.nodup_cons.2 ⟨hyl, hnd⟩)
        (List.IsChain.cons_of_ne_nil hne hch hy.symm) (by simp)
      simp only [List.length_cons] at this
      omega
    have hcard : 1 < (G.neighborFinset a).card := by
      rw [card_neighborFinset_eq_degree]; have := hδ a; omega
    cases t with
    | nil =>
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset a).card)
      simpa using hnbr y ((mem_neighborFinset _ _ _).mp hy)
    | cons u t' =>
      obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_ne hcard u
      have hwadj : G.Adj a w := (mem_neighborFinset _ _ _).mp hw
      have hwt : w ∈ u :: t' := hnbr w hwadj
      obtain ⟨A, B, hAB⟩ := List.append_of_mem hwt
      have hA : A ≠ [] := by
        rintro rfl
        simp only [List.nil_append, List.cons.injEq] at hAB
        exact hwu hAB.1.symm
      have hch' : (A ++ w :: B).IsChain G.Adj := by
        rw [← hAB]; exact (List.isChain_cons.mp hch).2
      rw [List.isChain_append] at hch'
      have hlink : ∀ y ∈ A.head?, G.Adj a y := by
        intro y hy
        have hAh : (u :: t').head? = A.head? := by
          rw [hAB]
          cases A with
          | nil => exact absurd rfl hA
          | cons a1 A' => rfl
        exact (List.isChain_cons.mp hch).1 y (by rw [hAh]; exact hy)
      have hperm : (A.reverse ++ a :: w :: B).Perm (a :: u :: t') := by
        rw [List.perm_iff_count]
        intro z
        have h2 : (u :: t') = A ++ w :: B := hAB
        rw [h2]
        simp [List.count_cons, List.count_append]
        omega
      have hnd' : (A.reverse ++ a :: w :: B).Nodup := hperm.nodup_iff.mpr hnd
      refine ⟨A.reverse ++ a :: w :: B, by simp, hnd', ?_, by simp, hperm.length_eq, ?_, ?_⟩
      · rw [List.isChain_append]
        refine ⟨chain_rev hch'.1, ?_, ?_⟩
        · exact List.isChain_cons.mpr ⟨fun y hy => by
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            subst hy; exact hwadj, hch'.2.1⟩
        · intro x hx y hy
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          rw [List.getLast?_reverse] at hx
          exact (hlink x hx).symm
      · have hxA : a ∉ A := fun h => hxt (by rw [hAB]; exact List.mem_append_left _ h)
        intro hh2
        have hmem : (A.reverse ++ a :: w :: B).head (by simp) ∈ A.reverse := by
          rw [List.head_append_of_ne_nil (by simpa using hA)]
          exact List.head_mem _
        rw [hh2] at hmem
        exact hxA (List.mem_reverse.mp hmem)
      · intro hh2
        have hg := List.getLast_eq_getElem (l := A.reverse ++ a :: w :: B) (by simp)
        have hi : (A.reverse ++ a :: w :: B)[A.reverse.length]'(by simp) = a := by
          rw [List.getElem_append_right (by omega)]; simp
        have hinj := (List.Nodup.getElem_inj_iff hnd').mp (hi.trans (hh2.symm.trans hg))
        simp at hinj
lemma h18 [DecidableRel G.Adj] (hconn : G.Connected) (x₀ : V) (hδ : ∀ v, 2 ≤ G.degree v)
    (hlt : ∀ l : List V, l.Nodup → l.IsChain G.Adj → x₀ ∈ l → l.length < Fintype.card V) :
    ∃ l : List V, ∃ h : l ≠ [], l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
      l.head h ≠ x₀ ∧ l.getLast h ≠ x₀ ∧
      (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length) := by
  obtain ⟨l, hne, hnd, hch, hx, hmax⟩ := exists_longest_x0 (G := G) x₀
  by_cases h1 : l.head hne = x₀
  · obtain ⟨l', h', hnd', hch', hx', hlen, h2, h3⟩ :=
      rot_head x₀ hδ l hne hnd hch hx hmax h1
    exact ⟨l', h', hnd', hch', hx', h2, h3, fun l'' a b c => (hmax l'' a b c).trans hlen.ge⟩
  by_cases h2 : l.getLast hne = x₀
  · have hrne : l.reverse ≠ [] := by simpa using hne
    have hhead : l.reverse.head hrne = x₀ := by
      rw [List.head_reverse]; exact h2
    have hmaxr : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' →
        l'.length ≤ l.reverse.length := by
      intro l' a b c; rw [List.length_reverse]; exact hmax l' a b c
    obtain ⟨l', h', hnd', hch', hx', hlen, h3, h4⟩ :=
      rot_head x₀ hδ l.reverse hrne (List.nodup_reverse.mpr hnd) (chain_rev hch)
        (List.mem_reverse.mpr hx) hmaxr hhead
    exact ⟨l', h', hnd', hch', hx', h3, h4, fun l'' a b c => (hmaxr l'' a b c).trans hlen.ge⟩
  · exact ⟨l, hne, hnd, hch, hx, h1, h2, hmax⟩
lemma Cadre.hmax_sup [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → (∀ v ∈ l, v ∈ l') → l'.length ≤ l.length := by
  intro l' h1 h2 h3
  exact hmax l' h1 h2 (h3 x₀ hmem)
lemma Cadre.reverse [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∃ hne' : l.reverse ≠ [], l.reverse.Nodup ∧ l.reverse.IsChain G.Adj ∧ x₀ ∈ l.reverse ∧
      l.reverse.head hne' ≠ x₀ ∧ l.reverse.getLast hne' ≠ x₀ ∧
      (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.reverse.length) ∧
      l.reverse.length < Fintype.card V := by
  have hne' : l.reverse ≠ [] := by simpa using hne
  refine ⟨hne', List.nodup_reverse.mpr hnd, chain_rev hch, List.mem_reverse.mpr hmem, ?_, ?_, ?_, ?_⟩
  · rw [List.head_reverse]; exact hlast
  · rw [List.getLast_reverse]; exact hhd
  · intro l' a b c; rw [List.length_reverse]; exact hmax l' a b c
  · rw [List.length_reverse]; exact hlt
lemma Cadre.getD_reverse (l : List V) (d : V) {i : ℕ} (hi : i < l.length) :
    l.reverse.getD i d = l.getD (l.length - 1 - i) d := by
  have h1 : l.length - 1 - i < l.length := by omega
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ h1,
    List.getElem_reverse]
lemma Cadre.exists_cadre [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V) {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) :
    (∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) ∨
      ∃ l : List V, ∃ hne : l ≠ [], l.Nodup ∧ l.IsChain G.Adj ∧ x₀ ∈ l ∧
        l.head hne ≠ x₀ ∧ l.getLast hne ≠ x₀ ∧
        (∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length) ∧
        l.length < Fintype.card V := by
  classical
  have hδ := h11 hconn hH hn
  by_cases hall : ∀ l : List V, l.Nodup → l.IsChain G.Adj → x₀ ∈ l → l.length < Fintype.card V
  · right
    obtain ⟨l, hne, hnd, hch, hx, h1h, hlast, hmax⟩ := h18 hconn x₀ hδ hall
    exact ⟨l, hne, hnd, hch, hx, h1h, hlast, hmax, hall l hnd hch hx⟩
  · left
    push Not at hall
    obtain ⟨l, hnd, hch, hx, hlen⟩ := hall
    have hne : l ≠ [] := List.ne_nil_of_mem hx
    exact ham_of_list l hne hnd hch (le_antisymm hnd.length_le_card hlen)
lemma deg_x0_le [Nontrivial V] [DecidableRel G.Adj] {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) : G.degree x₀ ≤ secondSmallestDegree G := by
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hmem : secondSmallestDegree G ∈ degreeSequence G := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  simp only [degreeSequence, Multiset.mem_sort, Multiset.mem_map] at hmem
  obtain ⟨v, -, hv⟩ := hmem
  rw [← hv]; exact hmin v
lemma card_le_gamma [DecidableRel G.Adj] (hconn : G.Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) (v : V) (S : Finset V)
    (hS : ∀ w ∈ S, G.dist v w = 2) : S.card ≤ secondSmallestDegree G := by
  classical
  have hsub : S ⊆ (Finset.univ.filter fun w => Even (G.dist v w)).erase v := by
    intro w hw
    have h2 := hS w hw
    have hwv : w ≠ v := by
      rintro rfl
      simp at h2
    simp [hwv, h2]
  have hvm : v ∈ Finset.univ.filter fun w => Even (G.dist v w) := by simp
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hvm] at this
  have h3 := hH v
  unfold distEven at h3
  omega
lemma cut_closed (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected) (c : V) (S : Finset V)
    (hc : c ∉ S) (hS : S.Nonempty) (hcl : ∀ v ∈ S, ∀ w, G.Adj v w → w ≠ c → w ∈ S)
    (hout : ∃ w, w ≠ c ∧ w ∉ S) : False := by
  classical
  obtain ⟨s, hs⟩ := hS
  obtain ⟨w, hwc, hwS⟩ := hout
  have hsc : s ≠ c := fun h => hc (h ▸ hs)
  obtain ⟨p⟩ := (hb c) ⟨s, hsc⟩ ⟨w, hwc⟩
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x.1 ∈ S} hs hwS
  exact hd2 (hcl _ hd1 _ d.adj d.snd.2)
lemma Cadre.no_longer [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (l' : List V) (h1 : l'.Nodup) (h2 : l'.IsChain G.Adj) (h3 : x₀ ∈ l')
    (h4 : l.length < l'.length) : False := by
  have := hmax l' h1 h2 h3
  omega
lemma b5_chain3 {A B C : List V} (hB : B ≠ []) (hA : A.IsChain G.Adj) (hb : B.IsChain G.Adj)
    (hc : C.IsChain G.Adj) (hAB : ∀ x ∈ A.getLast?, ∀ y ∈ B.head?, G.Adj x y)
    (hBC : ∀ x ∈ B.getLast?, ∀ y ∈ C.head?, G.Adj x y) : (A ++ B ++ C).IsChain G.Adj := by
  rw [List.isChain_append]
  refine ⟨List.isChain_append.2 ⟨hA, hb, hAB⟩, hc, ?_⟩
  intro x hx y hy
  rw [List.getLast?_append_of_ne_nil _ hB] at hx
  exact hBC x hx y hy
lemma b5_idx {l : List V} {x : V} (h : x ∈ l) : ∃ i, i < l.length ∧ l.getD i x = x := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩
lemma b5_mem_td {l : List V} {x : V} {A B i : ℕ} (hi : i < l.length) (h : l.getD i x = x)
    (hc : i < A ∨ B ≤ i) : x ∈ l.take A ∨ x ∈ l.drop B := by
  rw [List.getD_eq_getElem _ _ hi] at h
  rcases hc with hc | hc
  · left
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simpa using h⟩
  · right
    refine List.mem_iff_getElem.mpr ⟨i - B, by simp; omega, ?_⟩
    rw [List.getElem_drop]
    have : B + (i - B) = i := by omega
    simpa [this] using h
lemma b5_head_drop {l : List V} {b : ℕ} (d : V) (hb : b < l.length) :
    (l.drop b).head? = some (l.getD b d) := by
  rw [List.head?_drop, List.getD_eq_getElem _ _ hb, List.getElem?_eq_getElem hb]
lemma b5_last_take {l : List V} {a : ℕ} (d : V) (ha : a < l.length) :
    (l.take (a + 1)).getLast? = some (l.getD a d) := by
  rw [List.getLast?_take, List.getD_eq_getElem _ _ ha]
  simp [List.getElem?_eq_getElem ha]
lemma b5_nodup_td {l : List V} (hnd : l.Nodup) {A B : ℕ} (hAB : A ≤ B) :
    (l.take A ++ l.drop B).Nodup := by
  have hsub : (l.take A ++ l.drop B).Sublist l := by
    have h1 : l.drop B = (l.drop A).drop (B - A) := by
      rw [List.drop_drop]; congr 1; omega
    have h2 : (l.take A ++ (l.drop A).drop (B - A)).Sublist (l.take A ++ l.drop A) :=
      List.Sublist.append (List.Sublist.refl _) (List.drop_sublist _ _)
    rw [h1]
    simpa using h2
  exact hsub.nodup hnd
lemma Cadre.no_mid [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a b : ℕ) (hab : a < b) (hb' : b < l.length)
    (h1 : G.Adj (l.getD a x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD b x₀))
    (hx : ∀ i, a < i → i < b → l.getD i x₀ ≠ x₀) (hlen : b - a - 1 < s.length) : False := by
  have hT : (l.take (a + 1)).length = a + 1 := by simp; omega
  have hD : (l.drop b).length = l.length - b := by simp
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (l.take (a + 1) ++ s ++ l.drop b) ?_ ?_ ?_ ?_
  · have hTD := b5_nodup_td hnd (A := a + 1) (B := b) (by omega)
    rw [List.nodup_append]
    refine ⟨List.nodup_append.2 ⟨hnd.sublist (List.take_sublist _ _), snd, ?_⟩,
      hnd.sublist (List.drop_sublist _ _), ?_⟩
    · intro x hx y hy hxy
      exact sl y hy (hxy ▸ List.take_subset _ _ hx)
    · intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact (List.nodup_append.1 hTD).2.2 x hx y hy
      · rintro rfl
        exact sl x hx (List.drop_subset _ _ hy)
  · refine b5_chain3 hs (hch.take _) sch (hch.drop _) ?_ ?_
    · intro x hx y hy
      rw [b5_last_take x₀ (by omega)] at hx
      rw [List.head?_eq_head hs] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h1
    · intro x hx y hy
      rw [b5_head_drop x₀ hb'] at hy
      rw [List.getLast?_eq_getLast hs] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h2
  · obtain ⟨i, hi, hxi⟩ := b5_idx hmem
    have hc : i < a + 1 ∨ b ≤ i := by
      by_contra hcon
      push Not at hcon
      exact hx i (by omega) hcon.2 (by rw [hxi])
    rcases b5_mem_td hi hxi hc with h | h
    · simp [h]
    · simp [h]
  · simp only [List.length_append, hT, hD]
    omega
lemma Cadre.no_pre [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a : ℕ) (ha : a < l.length) (h : G.Adj (s.getLast hs) (l.getD a x₀))
    (hx : ∀ i, i < a → l.getD i x₀ ≠ x₀) (hlen : a < s.length) : False := by
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (s ++ l.drop a) ?_ ?_ ?_ ?_
  · refine List.nodup_append.2 ⟨snd, hnd.sublist (List.drop_sublist _ _), ?_⟩
    intro x hx y hy hxy
    exact sl x hx (hxy ▸ List.drop_subset _ _ hy)
  · refine List.isChain_append.2 ⟨sch, hch.drop _, ?_⟩
    intro x hx y hy
    rw [b5_head_drop x₀ ha] at hy
    rw [List.getLast?_eq_getLast hs] at hx
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx; subst hy; exact h
  · obtain ⟨i, hi, hxi⟩ := b5_idx hmem
    have hc : i < 0 ∨ a ≤ i := by
      by_contra hcon
      push Not at hcon
      exact hx i (by omega) (by rw [hxi])
    rcases b5_mem_td (A := 0) (B := a) hi hxi hc with h | h
    · simp at h
    · simp [h]
  · simp only [List.length_append, List.length_drop]
    omega
lemma Cadre.no_suf [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (b : ℕ) (hb' : b < l.length) (h : G.Adj (l.getD b x₀) (s.head hs))
    (hx : ∀ i, b < i → i < l.length → l.getD i x₀ ≠ x₀) (hlen : l.length - 1 - b < s.length) :
    False := by
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (l.take (b + 1) ++ s) ?_ ?_ ?_ ?_
  · refine List.nodup_append.2 ⟨hnd.sublist (List.take_sublist _ _), snd, ?_⟩
    intro x hx y hy hxy
    exact sl y hy (hxy ▸ List.take_subset _ _ hx)
  · refine List.isChain_append.2 ⟨hch.take _, sch, ?_⟩
    intro x hx y hy
    rw [b5_last_take x₀ hb'] at hx
    rw [List.head?_eq_head hs] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx; subst hy; exact h
  · obtain ⟨i, hi, hxi⟩ := b5_idx hmem
    have hc : i < b + 1 ∨ l.length ≤ i := by
      by_contra hcon
      push Not at hcon
      exact hx i (by omega) hi (by rw [hxi])
    rcases b5_mem_td (A := b + 1) (B := l.length) hi hxi hc with h | h
    · simp [h]
    · simp at h
  · simp only [List.length_append, List.length_take]
    omega
lemma Cadre.endE [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a j : ℕ) (haj : a < j) (hj : j < l.length)
    (h1 : G.Adj (l.getD 0 x₀) (l.getD j x₀)) (h2 : G.Adj (s.getLast hs) (l.getD a x₀))
    (hx : ∃ i, (i ≤ a ∨ j ≤ i) ∧ i < l.length ∧ l.getD i x₀ = x₀) (hlen : j - a ≤ s.length) :
    False := by
  have hT : (l.take (a + 1)).length = a + 1 := by simp; omega
  have hhead : (l.take (a + 1)).head? = some (l.getD 0 x₀) := by
    rw [List.head?_take, if_neg (by omega), List.head?_eq_getElem?,
      List.getD_eq_getElem _ _ (by omega), List.getElem?_eq_getElem (by omega)]
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (s ++ (l.take (a + 1)).reverse ++ l.drop j) ?_ ?_ ?_ ?_
  · have hTD := b5_nodup_td hnd (A := a + 1) (B := j) (by omega)
    have hTn : (l.take (a + 1)).reverse.Nodup :=
      List.nodup_reverse.mpr (hnd.sublist (List.take_sublist _ _))
    rw [List.nodup_append]
    refine ⟨List.nodup_append.2 ⟨snd, hTn, ?_⟩, hnd.sublist (List.drop_sublist _ _), ?_⟩
    · intro x hx y hy hxy
      exact sl x hx (hxy ▸ List.take_subset _ _ (List.mem_reverse.mp hy))
    · intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · rintro rfl
        exact sl x hx (List.drop_subset _ _ hy)
      · exact (List.nodup_append.1 hTD).2.2 x (List.mem_reverse.mp hx) y hy
  · refine b5_chain3 (by rw [← List.length_pos_iff, List.length_reverse, hT]; omega) sch (chain_rev (hch.take _)) (hch.drop _) ?_ ?_
    · intro x hx y hy
      rw [List.head?_reverse, b5_last_take x₀ (by omega)] at hy
      rw [List.getLast?_eq_getLast hs] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h2
    · intro x hx y hy
      rw [List.getLast?_reverse, hhead] at hx
      rw [b5_head_drop x₀ hj] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h1
  · obtain ⟨i, hi, hxi, hc⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ ∧ (i < a + 1 ∨ j ≤ i) := by
      obtain ⟨i, hc, hi, he⟩ := hx
      exact ⟨i, hi, he, by omega⟩
    rcases b5_mem_td hi hxi hc with h | h
    · simp [h]
    · simp [h]
  · simp only [List.length_append, List.length_reverse, hT, List.length_drop]
    omega
lemma Cadre.endE_last [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l) (a j : ℕ) (hja : j < a) (ha : a < l.length)
    (h1 : G.Adj (l.getD (l.length - 1) x₀) (l.getD j x₀)) (h2 : G.Adj (s.head hs) (l.getD a x₀))
    (hx : ∃ i, (a ≤ i ∨ i ≤ j) ∧ i < l.length ∧ l.getD i x₀ = x₀) (hlen : a - j ≤ s.length) :
    False := by
  have hT : (l.drop a).length = l.length - a := by simp
  have hlast' : (l.drop a).getLast? = some (l.getD (l.length - 1) x₀) := by
    rw [List.getLast?_drop, if_neg (by omega), getD_last l hne, List.getLast?_eq_getLast hne]
  refine Cadre.no_longer hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    (l.take (j + 1) ++ (l.drop a).reverse ++ s) ?_ ?_ ?_ ?_
  · have hTD := b5_nodup_td hnd (A := j + 1) (B := a) (by omega)
    have hTn : (l.drop a).reverse.Nodup :=
      List.nodup_reverse.mpr (hnd.sublist (List.drop_sublist _ _))
    rw [List.nodup_append]
    refine ⟨List.nodup_append.2 ⟨hnd.sublist (List.take_sublist _ _), hTn, ?_⟩, snd, ?_⟩
    · intro x hx y hy
      exact (List.nodup_append.1 hTD).2.2 x hx y (List.mem_reverse.mp hy)
    · intro x hx y hy hxy
      rcases List.mem_append.mp hx with hx | hx
      · exact sl y hy (hxy ▸ List.take_subset _ _ hx)
      · exact sl y hy (hxy ▸ List.drop_subset _ _ (List.mem_reverse.mp hx))
  · refine b5_chain3 (by rw [← List.length_pos_iff, List.length_reverse, hT]; omega) (hch.take _) (chain_rev (hch.drop _)) sch ?_ ?_
    · intro x hx y hy
      rw [b5_last_take x₀ (by omega)] at hx
      rw [List.head?_reverse, hlast'] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h1.symm
    · intro x hx y hy
      rw [List.getLast?_reverse, b5_head_drop x₀ ha] at hx
      rw [List.head?_eq_head hs] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy; exact h2.symm
  · obtain ⟨i, hi, hxi, hc⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ ∧ (i < j + 1 ∨ a ≤ i) := by
      obtain ⟨i, hc, hi, he⟩ := hx
      exact ⟨i, hi, he, by omega⟩
    rcases b5_mem_td hi hxi hc with h | h
    · simp [h]
    · simp [List.mem_reverse, h]
  · simp only [List.length_append, List.length_reverse, hT, List.length_take]
    omega
lemma ring_card (J : Finset ℕ) (h0 : 0 ∉ J) :
    (J.image (· + 1) ∪ J.image (· - 1)).card + (J.filter (fun j => j + 2 ∈ J)).card =
      2 * J.card := by
  have h1 : (J.image (· + 1)).card = J.card :=
    Finset.card_image_of_injective _ (add_left_injective 1)
  have h2 : (J.image (· - 1)).card = J.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
    have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
    simp only at hab
    omega
  have h3 : J.image (· + 1) ∩ J.image (· - 1) = (J.filter (fun j => j + 2 ∈ J)).image (· + 1) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hbx⟩⟩
      have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      have : b = a + 2 := by omega
      rw [← this]; exact hb
    · rintro ⟨a, ⟨ha, ha2⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨a + 2, ha2, by simp⟩⟩
  have h4 : ((J.filter (fun j => j + 2 ∈ J)).image (· + 1)).card = (J.filter (fun j => j + 2 ∈ J)).card :=
    Finset.card_image_of_injective _ (add_left_injective 1)
  have h5 := Finset.card_union_add_card_inter (J.image (· + 1)) (J.image (· - 1))
  rw [h3, h4, h1, h2] at h5
  omega
lemma T_lt (J : Finset ℕ) (hJ : J.Nonempty) :
    (J.filter (fun j => j + 2 ∈ J)).card + 1 ≤ J.card := by
  have hsub : J.filter (fun j => j + 2 ∈ J) ⊆ J.erase (J.max' hJ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, hj.1⟩
    have := Finset.le_max' J _ hj.2
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.max'_mem J hJ)] at this
  have := Finset.card_pos.mpr hJ
  omega
lemma prog (J : Finset ℕ) (hJ : J.Nonempty)
    (ht : (J.filter (fun j => j + 2 ∈ J)).card + 1 = J.card) :
    (∀ j ∈ J, j ≠ J.max' hJ → j + 2 ∈ J) ∧ (∀ j ∈ J, j ≠ J.min' hJ → 2 ≤ j ∧ j - 2 ∈ J) := by
  have hsub : J.filter (fun j => j + 2 ∈ J) ⊆ J.erase (J.max' hJ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    refine ⟨?_, hj.1⟩
    have := Finset.le_max' J _ hj.2
    omega
  have hc := Finset.card_erase_of_mem (Finset.max'_mem J hJ)
  have hpos := Finset.card_pos.mpr hJ
  have heq : J.filter (fun j => j + 2 ∈ J) = J.erase (J.max' hJ) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨?_, ?_⟩
  · intro j hj hne
    have : j ∈ J.erase (J.max' hJ) := Finset.mem_erase.mpr ⟨hne, hj⟩
    rw [← heq] at this
    exact (Finset.mem_filter.mp this).2
  · have hsub2 : (J.filter (fun j => j + 2 ∈ J)).image (· + 2) ⊆ J.erase (J.min' hJ) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨hj, hj2⟩, rfl⟩ := hx
      rw [Finset.mem_erase]
      refine ⟨?_, hj2⟩
      have := Finset.min'_le J _ hj
      omega
    have hc2 := Finset.card_erase_of_mem (Finset.min'_mem J hJ)
    have hci : ((J.filter (fun j => j + 2 ∈ J)).image (· + 2)).card = (J.filter (fun j => j + 2 ∈ J)).card :=
      Finset.card_image_of_injective _ (add_left_injective 2)
    have heq2 := Finset.eq_of_subset_of_card_le hsub2 (by omega)
    intro j hj hne
    have : j ∈ J.erase (J.min' hJ) := Finset.mem_erase.mpr ⟨hne, hj⟩
    rw [← heq2] at this
    simp only [Finset.mem_image, Finset.mem_filter] at this
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := this
    exact ⟨by omega, by simpa using hi⟩
lemma Cadre.J_bounds [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) {j : ℕ} (hj : j ∈ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)))) : 0 < j ∧ j + 1 < l.length := by
  rw [Finset.mem_filter, Finset.mem_range] at hj
  obtain ⟨hjl, hadj⟩ := hj
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hgd : l.getD j y = l.getD j x₀ := by
    rw [List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ hjl]
  have := lemma5abx hconn l hne hnd hch hhs y hy j hjl (by rw [hgd]; exact hadj)
  exact ⟨this.1, this.2.1⟩
lemma Cadre.dset_dist [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) {i : ℕ} (hi : i ∈ (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1))) :
    i < l.length ∧ G.dist y (l.getD i x₀) = 2 := by
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hi
  have key : ∀ j, j < l.length → G.Adj y (l.getD j x₀) →
      (j + 1 < l.length ∧ G.dist y (l.getD (j + 1) x₀) = 2) ∧
        (0 < j ∧ G.dist y (l.getD (j - 1) x₀) = 2) := by
    intro j hjl hadj
    have hgd : ∀ k, k < l.length → l.getD k y = l.getD k x₀ := by
      intro k hk; rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
    have h5 := lemma5abx hconn l hne hnd hch hhs y hy j hjl (by rw [hgd j hjl]; exact hadj)
    obtain ⟨h0, h1, h2, h3, -, -⟩ := h5
    have hk1 : j + 1 < l.length := h1
    have hk2 : j - 1 < l.length := by omega
    rw [hgd _ hk1] at h2
    rw [hgd _ hk2] at h3
    have hch' : ∀ k, k + 1 < l.length → G.Adj (l.getD k x₀) (l.getD (k + 1) x₀) := by
      intro k hk
      have := List.isChain_iff_getElem.mp hch k hk
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]
      exact this
    have hne1 : l.getD (j + 1) x₀ ≠ y := by
      intro h; apply hy; rw [← h, List.getD_eq_getElem _ _ hk1]; exact List.getElem_mem _
    have hne2 : l.getD (j - 1) x₀ ≠ y := by
      intro h; apply hy; rw [← h, List.getD_eq_getElem _ _ hk2]; exact List.getElem_mem _
    refine ⟨⟨hk1, dist_two hconn hadj (hch' j hk1) h2 hne1⟩, ⟨h0, ?_⟩⟩
    have hj1 : j - 1 + 1 = j := by omega
    have hc2 : G.Adj (l.getD j x₀) (l.getD (j - 1) x₀) := by
      have := hch' (j - 1) (by omega)
      rw [hj1] at this
      exact this.symm
    exact dist_two hconn hadj hc2 h3 hne2
  rcases hi with ⟨j, ⟨hjl, hadj⟩, rfl⟩ | ⟨j, ⟨hjl, hadj⟩, rfl⟩
  · exact ⟨(key j hjl hadj).1.1, (key j hjl hadj).1.2⟩
  · have := (key j hjl hadj).2
    exact ⟨by omega, this.2⟩
lemma Cadre.degree_split [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    {y : V} (hy : y ∉ l) :
    G.degree y = (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)))).card + ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hdisj : Disjoint (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image
      (fun i => l.getD i x₀)) ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hw1 hw2
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hw1
    apply hw2.1
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hN : G.neighborFinset y = ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image
      (fun i => l.getD i x₀) ∪ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · intro hw
      by_cases hwl : w ∈ l
      · left
        obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwl
        refine ⟨i, ⟨hi, ?_⟩, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hiw]; exact hw
        · rw [List.getD_eq_getElem _ _ hi, hiw]
      · right; exact ⟨hwl, hw⟩
    · rintro (⟨i, ⟨hi, hadj⟩, rfl⟩ | ⟨_, hw⟩)
      · exact hadj
      · exact hw
  rw [hN, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn]
  intro i hi j hj hij
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
  simp only at hij
  rw [List.getD_eq_getElem _ _ hi.1, List.getD_eq_getElem _ _ hj.1] at hij
  exact (List.Nodup.getElem_inj_iff hnd).mp hij
lemma Cadre.count_Q2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) (Bp K2 : Finset V)
    (hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj y w ∧ ∃ z, z ∉ l ∧ G.Adj y z ∧ G.Adj z w)
    (hK : ∀ w ∈ K2, w ∉ l ∧ w ≠ y ∧ ¬ G.Adj y w ∧ ∃ z, G.Adj y z ∧ G.Adj z w) :
    ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1))).card + Bp.card + K2.card ≤ secondSmallestDegree G := by
  classical
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hDd : ∀ i ∈ (((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)),
      i < l.length ∧ G.dist y (l.getD i x₀) = 2 := fun i hi =>
    Cadre.dset_dist hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hi
  have hdisjDB : Disjoint ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀)) Bp := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp hw1
    obtain ⟨-, -, z, hz, hyz, hzw⟩ := hB _ hw2
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hiD
    rcases hiD with ⟨j, ⟨hjl, hadj⟩, rfl⟩ | ⟨j, ⟨hjl, hadj⟩, rfl⟩
    · have hjb := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
        (j := j) (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hjl, hadj⟩)
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, z] (by simp) (by simp; exact G.ne_of_adj hyz) (by simp [hyz]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) j (j + 1) (by omega) hjb.2 (by simpa using hadj.symm) (by simpa using hzw) (by intro i h1 h2; omega) (by simp)
    · have hjb := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
        (j := j) (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hjl, hadj⟩)
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z, y] (by simp) (by simp; exact (G.ne_of_adj hyz).symm) (by simp [hyz.symm]) (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) (j - 1) j (by omega) (by omega) (by simpa using hzw.symm) (by simpa using hadj) (by intro i h1 h2; omega) (by simp only [List.length_cons, List.length_nil]; omega)
  have hdisjK : Disjoint ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀) ∪ Bp) K2 := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have hwl : w ∈ l := by
      rcases Finset.mem_union.mp hw1 with h | h
      · obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp h
        rw [List.getD_eq_getElem _ _ (hDd i hiD).1]; exact List.getElem_mem _
      · exact (hB w h).1
    exact (hK w hw2).1 hwl
  have hinj : Set.InjOn (fun i => l.getD i x₀) (((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)) : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    have hi' := (hDd i hi).1
    have hj' := (hDd j hj).1
    simp only at hij
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at hij
    exact (List.Nodup.getElem_inj_iff hnd).mp hij
  have hcard := card_le_gamma hconn hH y
    ((((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· + 1) ∪ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).image (· - 1)).image (fun i => l.getD i x₀) ∪ Bp) ∪ K2)) (by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · rcases Finset.mem_union.mp h with h | h
        · obtain ⟨i, hiD, rfl⟩ := Finset.mem_image.mp h
          exact (hDd i hiD).2
        · obtain ⟨hwl, hnadj, z, -, hyz, hzw⟩ := hB w h
          exact dist_two hconn hyz hzw hnadj (fun h => hy (h ▸ hwl))
      · obtain ⟨-, hwy, hnadj, z, hyz, hzw⟩ := hK w h
        exact dist_two hconn hyz hzw hnadj hwy)
  rw [Finset.card_union_of_disjoint hdisjK, Finset.card_union_of_disjoint hdisjDB,
    Finset.card_image_of_injOn hinj] at hcard
  exact hcard
lemma b15_adj {l : List V} (d : V) (hch : l.IsChain G.Adj) {i : ℕ} (hi : i + 1 < l.length) :
    G.Adj (l.getD i d) (l.getD (i + 1) d) := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact List.isChain_iff_getElem.1 hch i hi
lemma b15_inj {l : List V} (d : V) (hnd : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i d = l.getD j d) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h
lemma b15_mem {l : List V} (d : V) {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _
lemma b15_head {l : List V} (hne : l ≠ []) (d : V) : l.head hne = l.getD 0 d := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl
lemma b15_last {l : List V} (hne : l ≠ []) (d : V) : l.getLast hne = l.getD (l.length - 1) d := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by have := List.length_pos_of_ne_nil hne; omega)]
lemma b15_dflt {l : List V} {i : ℕ} (hi : i < l.length) (d d' : V) : l.getD i d = l.getD i d' := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
lemma b15_len2 {l : List V} {x₀ : V} (hne : l ≠ []) (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) :
    2 ≤ l.length := by
  by_contra hlt
  have h1 : l.length = 1 := by have := List.length_pos_of_ne_nil hne; omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h1
  simp only [List.mem_singleton] at hmem
  exact hhd (by simp [hmem])
lemma b17_decomp (l : List V) (d : V) {i : ℕ} (hi : i + 1 < l.length) :
    l = l.take i ++ l.getD i d :: l.getD (i + 1) d :: l.drop (i + 2) := by
  have h := List.take_append_drop i l
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)] at h
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact h.symm
lemma b17_long {x₀ : V} {l s c : List V} (hnd : l.Nodup) (sl : ∀ v ∈ s, v ∉ l)
    (snd : s.Nodup) (hs : s ≠ []) (hmem : x₀ ∈ l)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hc : c.Perm (s ++ l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : (s ++ l).Nodup :=
    List.nodup_append.2 ⟨snd, hnd, (fun a ha b hb h => sl a ha (h ▸ hb))⟩
  have h := hmax c (hc.nodup_iff.2 hnd') hch (hc.mem_iff.2 (List.mem_append_right _ hmem))
  rw [hc.length_eq, List.length_append] at h
  have := List.length_pos_of_ne_nil hs
  omega
lemma b17_perm1 (t d s : List V) (u x : V) :
    (t ++ x :: u :: (s ++ d)).Perm (s ++ (t ++ u :: x :: d)) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_cons]
  split_ifs <;> omega
lemma b17_perm2 (t d s : List V) (w x : V) :
    (t ++ (s ++ w :: x :: d)).Perm (s ++ (t ++ x :: w :: d)) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_cons]
  split_ifs <;> omega
lemma b17_head_app {s : List V} (hs : s ≠ []) (d : List V) : (s ++ d).head? = some (s.head hs) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons a t => rfl
lemma b17_last_take {l : List V} (d : V) {p : ℕ} (hp : 1 ≤ p) (hpl : p ≤ l.length) :
    (l.take p).getLast? = some (l.getD (p - 1) d) := by
  rw [List.getLast?_take, if_neg (by omega), List.getD_eq_getElem _ _ (by omega)]
  simp [List.getElem?_eq_getElem (by omega : p - 1 < l.length)]
lemma b17_head_drop {l : List V} (d : V) {n : ℕ} (hn : n < l.length) :
    (l.drop n).head? = some (l.getD n d) := by
  rw [List.head?_drop, List.getD_eq_getElem _ _ hn, List.getElem?_eq_getElem hn]
lemma Cadre.hole_x0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (S : Finset V) (hS : ∀ y ∈ S, y ∉ l) (p : ℕ) (hp : 1 ≤ p) (hp3 : p + 3 < l.length)
    (hx : l.getD (p + 1) x₀ = x₀)
    (hSA : ∀ y ∈ S, G.Adj y (l.getD p x₀) ∨ G.Adj y (l.getD (p + 2) x₀))
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l)
    (h1 : G.Adj (l.getD p x₀) (s.head hs)) (h2 : G.Adj (s.getLast hs) (l.getD (p + 2) x₀)) :
    S.card + 2 ≤ secondSmallestDegree G := by
  have hp2 : p + 2 < l.length := by omega
  have hA : G.Adj (l.getD p x₀) x₀ := by
    have := b15_adj (G := G) x₀ hch (i := p) (by omega)
    rwa [hx] at this
  have hB : G.Adj x₀ (l.getD (p + 2) x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p + 1) (by omega)
    rwa [hx] at this
  have hAa : G.Adj (l.getD (p - 1) x₀) (l.getD p x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp] at this
  have hBb : G.Adj (l.getD (p + 2) x₀) (l.getD (p + 3) x₀) :=
    b15_adj (G := G) x₀ hch (i := p + 2) (by omega)
  have hsl := List.getLast?_eq_getLast hs
  have hna : ¬ G.Adj (l.getD (p - 1) x₀) x₀ := by
    intro hadj
    refine b17_long (l := l) (s := s) (c := l.take p ++ x₀ :: l.getD p x₀ :: (s ++ l.drop (p + 2)))
      hnd sl snd hs hmem hmax ?_ ?_
    · have hd := b17_decomp l x₀ (i := p) (by omega)
      rw [hx] at hd
      have := b17_perm1 (l.take p) (l.drop (p + 2)) s (l.getD p x₀) x₀
      rwa [← hd] at this
    · refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, List.isChain_append.2 ⟨sch, hch.drop _, ?_⟩⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hA.symm
        · intro z hz
          rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact h1
        · intro z hz w hw
          rw [hsl, Option.mem_def, Option.some.injEq] at hz
          rw [b17_head_drop x₀ hp2, Option.mem_def, Option.some.injEq] at hw
          subst hz hw; exact h2
      · intro z hz w hw
        rw [b17_last_take x₀ hp (by omega), Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact hadj
  have hnb : ¬ G.Adj x₀ (l.getD (p + 3) x₀) := by
    intro hadj
    refine b17_long (l := l) (s := s) (c := l.take (p + 1) ++ (s ++ l.getD (p + 2) x₀ :: x₀ :: l.drop (p + 3)))
      hnd sl snd hs hmem hmax ?_ ?_
    · have hd := b17_decomp l x₀ (i := p + 1) (by omega)
      rw [hx] at hd
      have := b17_perm2 (l.take (p + 1)) (l.drop (p + 1 + 2)) s (l.getD (p + 1 + 1) x₀) x₀
      rwa [← hd] at this
    · refine List.isChain_append.2 ⟨hch.take _, List.isChain_append.2 ⟨sch, ?_, ?_⟩, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, hch.drop _⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hB.symm
        · intro z hz
          rw [b17_head_drop x₀ (by omega), Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hadj
      · intro z hz w hw
        rw [hsl, Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact h2
      · intro z hz w hw
        rw [List.getLast?_take, if_neg (by omega)] at hz
        have hw' := hw
        rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hw'
        subst hw'
        simp only [List.getElem?_eq_getElem (by omega : p + 1 - 1 < l.length), Option.some_or,
          Option.mem_def, Option.some.injEq] at hz
        subst hz
        have e1 : l[p + 1 - 1]'(by omega) = l.getD p x₀ := by
          rw [List.getD_eq_getElem _ _ (by omega)]; simp
        rw [e1]; exact h1
  have hne_a : l.getD (p - 1) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hne_b : l.getD (p + 3) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hab : l.getD (p - 1) x₀ ≠ l.getD (p + 3) x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) h
    omega
  have hSd : ∀ y ∈ S, G.dist x₀ y = 2 := by
    intro y hy
    have hyl := hS y hy
    have hyx : y ≠ x₀ := fun h => hyl (h ▸ hmem)
    have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have key : ¬ G.Adj y x₀ := by
      intro hadj
      have hadj' : G.Adj y (l.getD (p + 1) y) := by
        rw [b15_dflt (l := l) (i := p + 1) (by omega) y x₀, hx]; exact hadj
      obtain ⟨-, -, h5, h6, -, -⟩ := lemma5abx hconn l hne hnd hch hmx y hyl (p + 1) (by omega) hadj'
      rw [Nat.add_sub_cancel] at h6
      rcases hSA y hy with h | h
      · exact h6 (by rwa [b15_dflt (l := l) (i := p) (by omega) y x₀])
      · exact h5 (by rwa [b15_dflt (l := l) (i := p + 1 + 1) (by omega) y x₀])
    rcases hSA y hy with h | h
    · exact dist_two hconn hA.symm h.symm (fun h' => key h'.symm) hyx
    · exact dist_two hconn hB h.symm (fun h' => key h'.symm) hyx
  have hall : ∀ w ∈ insert (l.getD (p - 1) x₀) (insert (l.getD (p + 3) x₀) S), G.dist x₀ w = 2 := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hA.symm hAa.symm (fun h' => hna h'.symm) hne_a
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hB hBb hnb hne_b
    · exact hSd w hw
  have hc := card_le_gamma hconn hH x₀ _ hall
  have hAS : l.getD (p - 1) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  have hBS : l.getD (p + 3) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  rw [Finset.card_insert_of_notMem (by rw [Finset.mem_insert]; rintro (h | h); exacts [hab h, hAS h]),
    Finset.card_insert_of_notMem hBS] at hc
  omega
lemma b10_side [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y z : V) (hy : y ∉ l) (hz : z ∉ l) (hyz : G.Adj y z)
    (hNy : ∀ w, w ∉ l → G.Adj y w → w = z) :
    (∀ i, i < l.length → G.Adj z (l.getD i x₀) → G.Adj y (l.getD i x₀)) ∧
    secondSmallestDegree G = ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).card + 1 ∧
    ((((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).filter (fun j => j + 2 ∈ ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))))).card + 1 =
      ((Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀))).card) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  rw [← hJ]
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have h0 : 0 ∉ J := fun h => (Nat.lt_irrefl 0) (hjb 0 h).1
  have hdeg := Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
  rw [← hJ] at hdeg
  have hR : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) = {z} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, hadj⟩; exact hNy w hw hadj
    · rintro rfl; exact ⟨hz, hyz⟩
  rw [hR, Finset.card_singleton] at hdeg
  have hy0 : y ≠ x₀ := fun h => hy (h ▸ hmem)
  have hdy := hx0 y hy0
  have hσ2 := sigma_ge hδ
  obtain ⟨Bp, hBp⟩ : ∃ Bp : Finset V, Bp = Finset.univ.filter (fun w => w ∈ l ∧ ¬ G.Adj y w ∧ G.Adj z w) := ⟨_, rfl⟩
  have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy Bp ∅
    (by
      intro w hw
      rw [hBp] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨hw.1, hw.2.1, z, hz, hyz, hw.2.2⟩)
    (by intro w hw; simp at hw)
  rw [← hJ] at hQ
  simp only [Finset.card_empty] at hQ
  have hring := ring_card J h0
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hT := T_lt J hJne
  have hBp0 : Bp.card = 0 := by omega
  refine ⟨?_, by omega, by omega⟩
  intro i hi hadj
  by_contra hn
  have hmemBp : l.getD i x₀ ∈ Bp := by
    rw [hBp]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hn, hadj⟩
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  rw [Finset.card_eq_zero.mp hBp0] at hmemBp
  simp at hmemBp
lemma Cadre.no_edge_comp [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y z : V) (hy : y ∉ l) (hz : z ∉ l) (hyz : G.Adj y z)
    (hNy : ∀ w, w ∉ l → G.Adj y w → w = z) (hNz : ∀ w, w ∉ l → G.Adj z w → w = y) : False := by
  classical
  obtain ⟨hs1, hσ1, ht1⟩ := b10_side hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y z hy hz hyz hNy
  obtain ⟨hs2, -, -⟩ := b10_side hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt z y hz hy hyz.symm hNz
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  rw [← hJ] at hσ1 ht1
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have hJmem : ∀ j, j ∈ J ↔ j < l.length ∧ G.Adj y (l.getD j x₀) := by
    intro j; rw [hJ]; simp only [Finset.mem_filter, Finset.mem_range]
  have hσ2 := sigma_ge hδ
  have hxj : ∀ j ∈ J.filter (fun j => j + 2 ∈ J), l.getD (j + 1) x₀ = x₀ := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjJ, hj2⟩ := hj
    by_contra hne1
    obtain ⟨hjl, hjadj⟩ := (hJmem j).mp hjJ
    obtain ⟨hj2l, hj2adj⟩ := (hJmem (j + 2)).mp hj2
    exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, z] (by simp)
      (by simp; exact G.ne_of_adj hyz) (by simp [hyz])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption) j (j + 2) (by omega) hj2l
      (by simpa using hjadj.symm) (by simpa using hs2 (j + 2) hj2l hj2adj)
      (by intro i h1 h2; have : i = j + 1 := by omega
          subst this; exact hne1) (by simp)
  have hT1 : (J.filter (fun j => j + 2 ∈ J)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb'
    have ha' := hxj a ha
    have hb'' := hxj b hb'
    have haJ := (Finset.mem_filter.mp ha)
    have hbJ := (Finset.mem_filter.mp hb')
    have hal := (hjb a haJ.1).2
    have hbl := (hjb b hbJ.1).2
    have e1 := ha'
    have e2 := hb''
    rw [List.getD_eq_getElem _ _ hal] at e1
    rw [List.getD_eq_getElem _ _ hbl] at e2
    have := (List.Nodup.getElem_inj_iff hnd).mp (e1.trans e2.symm)
    omega
  have hcpos : 0 < J.card := by omega
  have hc : J.card = 1 ∨ J.card = 2 := by omega
  rcases hc with hc | hc
  ·
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hpJ : p ∈ J := by rw [hp]; exact Finset.mem_singleton_self p
    obtain ⟨hpl, hpadj⟩ := (hJmem p).mp hpJ
    obtain ⟨hp0, hp1⟩ := hjb p hpJ
    have hxp : l.getD p x₀ ∈ l := by rw [List.getD_eq_getElem _ _ hpl]; exact List.getElem_mem _
    have hidx : ∀ i, i < l.length → G.Adj y (l.getD i x₀) → i = p := by
      intro i hi hadj
      have : i ∈ J := (hJmem i).mpr ⟨hi, hadj⟩
      rw [hp] at this; exact Finset.mem_singleton.mp this
    refine cut_closed hb (l.getD p x₀) {y, z} ?_ ⟨y, by simp⟩ ?_ ?_
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hy (h ▸ hxp)
      · exact hz (h ▸ hxp)
    · intro v hv w hvw hwc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      by_cases hwl : w ∈ l
      · exfalso
        obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hwl
        have hgi : l.getD i x₀ = w := by rw [List.getD_eq_getElem _ _ hi, hiw]
        rcases hv with rfl | rfl
        · have := hidx i hi (by rw [hgi]; exact hvw)
          apply hwc; rw [← hgi, this]
        · have := hidx i hi (hs1 i hi (by rw [hgi]; exact hvw))
          apply hwc; rw [← hgi, this]
      · rcases hv with rfl | rfl
        · exact Or.inr (hNy w hwl hvw)
        · exact Or.inl (hNz w hwl hvw)
    · refine ⟨l.getD 0 x₀, ?_, ?_⟩
      · intro h
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hpl] at h
        have h' := (List.Nodup.getElem_inj_iff hnd).mp h
        omega
      · have h0l : l.getD 0 x₀ ∈ l := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        intro h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact hy (h ▸ h0l)
        · exact hz (h ▸ h0l)
  ·
    have htc : (J.filter (fun j => j + 2 ∈ J)).card = 1 := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (J.filter (fun j => j + 2 ∈ J)).card)
    have hxj' := hxj j hj
    obtain ⟨hjJ, hj2⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjl, hjadj⟩ := (hJmem j).mp hjJ
    obtain ⟨hj2l, hj2adj⟩ := (hJmem (j + 2)).mp hj2
    obtain ⟨hj0, -⟩ := hjb j hjJ
    obtain ⟨-, hj3⟩ := hjb (j + 2) hj2
    have hres := Cadre.hole_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {y, z}
      (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> assumption) j hj0 (by omega) hxj'
      (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact Or.inl hjadj
          · exact Or.inl (hs2 j hjl hjadj))
      [y, z] (by simp) (by simp; exact G.ne_of_adj hyz) (by simp [hyz])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
      (by simpa using hjadj.symm) (by simpa using hs2 (j + 2) hj2l hj2adj)
    rw [Finset.card_pair (G.ne_of_adj hyz)] at hres
    omega
lemma Cadre.Rdeg2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) : 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card := by
  classical
  by_contra hlt2
  push Not at hlt2
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, rfl⟩
  have hjb : ∀ j ∈ J, 0 < j ∧ j + 1 < l.length := by
    intro j hj
    rw [hJ] at hj
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy hj
  have h0 : 0 ∉ J := fun h => (Nat.lt_irrefl 0) (hjb 0 h).1
  have hdeg := Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
  rw [← hJ] at hdeg
  have hy0 : y ≠ x₀ := fun h => hy (h ▸ hmem)
  have hdy := hx0 y hy0
  have hσ2 := sigma_ge hδ
  have hring := ring_card J h0
  have hk : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card = 0 ∨
      ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card = 1 := by omega
  rcases hk with hk | hk
  · have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy ∅ ∅
      (by intro w hw; simp at hw) (by intro w hw; simp at hw)
    rw [← hJ] at hQ
    simp only [Finset.card_empty] at hQ
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    have hT := T_lt J hJne
    omega
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hk
    have hzmem : z ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) := by rw [hz]; exact Finset.mem_singleton_self z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzmem
    have hNy : ∀ w, w ∉ l → G.Adj y w → w = z := by
      intro w hw hadj
      have : w ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hw, hadj⟩
      rw [hz] at this; exact Finset.mem_singleton.mp this
    by_cases hex : ∃ w, w ∉ l ∧ G.Adj z w ∧ w ≠ y
    · obtain ⟨w, hwl, hzw, hwy⟩ := hex
      have hnadj : ¬ G.Adj y w := by
        intro h
        have := hNy w hwl h
        subst this
        exact G.loopless.irrefl _ hzw
      have hQ := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy ∅ {w}
        (by intro w hw; simp at hw)
        (by intro w' hw'; rw [Finset.mem_singleton] at hw'; subst hw'; exact ⟨hwl, hwy, hnadj, z, hzmem.2, hzw⟩)
      rw [← hJ] at hQ
      simp only [Finset.card_empty, Finset.card_singleton] at hQ
      have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
      have hT := T_lt J hJne
      omega
    · push Not at hex
      exact Cadre.no_edge_comp hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y z hy hzmem.1 hzmem.2 hNy
        hex
lemma Cadre.m_ge [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    2 * secondSmallestDegree G + 2 ≤ l.length := by
  classical
  by_contra hcon
  push Not at hcon
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  set σ := secondSmallestDegree G with hσ
  set a := l.head hne with ha
  set b := l.getLast hne with hbd
  set m := l.length with hm
  have hm2 : 2 ≤ m := by
    by_contra h2
    have h1 : m = 1 := by have := List.length_pos_of_ne_nil hne; omega
    obtain ⟨e, he⟩ := List.length_eq_one_iff.mp h1
    subst he
    simp at hmem hhd
    exact hhd hmem.symm
  obtain ⟨hNa, hNb, hsum, hdisj, hSd, hTd⟩ := lemma4x hconn l hne hnd hch hhs hlt hm2
  simp only [← ha, ← hbd] at hNa hNb hsum hdisj hSd hTd
  have hxa : σ ≤ G.degree a := hx0 a hhd
  have hxb : σ ≤ G.degree b := hx0 b hlast
  have hsum' : G.degree a + G.degree b + 1 ≤ m := hsum
  have hmσ : m = 2 * σ + 1 := by omega
  set f : ℕ → V := fun i => l.getD i a with hf
  have hf_get : ∀ i (hi : i < m), f i = l[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hf_mem : ∀ i, i < m → f i ∈ l := fun i hi => by rw [hf_get i hi]; exact List.getElem_mem _
  have hf_inj : ∀ i j, i < m → j < m → f i = f j → i = j := by
    intro i j hi hj h
    rw [hf_get i hi, hf_get j hj] at h
    exact hnd.getElem_inj_iff.mp h
  have hf_ex : ∀ w ∈ l, ∃ i, i < m ∧ f i = w := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨k, hk, hf_get k hk⟩
  have hf0 : f 0 = a := by
    rw [hf_get 0 (by omega)]
    cases l with
    | nil => exact absurd rfl hne
    | cons x t => rfl
  set S := (Finset.range (m - 1)).filter (fun j => G.Adj a (f (j + 1))) with hS
  set T := (Finset.range (m - 1)).filter (fun j => G.Adj (f j) b) with hT
  have hSc : σ ≤ S.card := hxa.trans hSd
  have hTc : σ ≤ T.card := hxb.trans hTd
  have hdisjST : Disjoint S T := by
    refine Finset.disjoint_left.mpr (fun j h1 h2 => ?_)
    simp only [hS, hT, Finset.mem_filter, Finset.mem_range] at h1 h2
    exact hdisj j (by omega) h1.2 h2.2
  have hunion : S ∪ T = Finset.range (m - 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;> exact (Finset.mem_filter.mp hx).1
    · rw [Finset.card_union_of_disjoint hdisjST, Finset.card_range]
      omega
  have hTcard : T.card = σ := by
    have hc := Finset.card_union_of_disjoint hdisjST
    rw [hunion, Finset.card_range] at hc
    omega
  have hpart : ∀ j, j + 1 < m → G.Adj a (f (j + 1)) ∨ G.Adj (f j) b := by
    intro j hj
    have : j ∈ S ∪ T := by rw [hunion]; simp; omega
    rcases Finset.mem_union.mp this with h | h
    · exact Or.inl (Finset.mem_filter.mp h).2
    · exact Or.inr (Finset.mem_filter.mp h).2
  have hNa' : ∀ y, y ∉ l → ¬ G.Adj a y := fun y hy h => hy (hNa y h)
  have hyN : ∀ y, y ∉ l → ∀ j, (hj : j < m) → G.Adj y (f j) → G.Adj a (f j) ∧ f j ≠ a := by
    intro y hy j hj hw
    have hy' : l.getD j y = f j := by
      rw [List.getD_eq_getElem _ _ hj, hf_get j hj]
    obtain ⟨h0, h1, -, -, -, h6⟩ := lemma5abx hconn l hne hnd hch hhs y hy j hj
      (by rw [hy']; exact hw)
    have hy1 : l.getD (j - 1) y = f (j - 1) := by
      rw [List.getD_eq_getElem _ _ (by omega), hf_get (j - 1) (by omega)]
    rw [← hbd, hy1] at h6
    have h6' : ¬ G.Adj b (f (j - 1)) := h6
    refine ⟨?_, fun h => ?_⟩
    · rcases hpart (j - 1) (by omega) with h | h
      · rw [show j - 1 + 1 = j by omega] at h
        exact h
      · exact absurd h.symm h6'
    · have := hf_inj j 0 hj (by omega) (h.trans hf0.symm)
      omega
  have hd2 : ∀ u, u ≠ a → ¬ G.Adj a u → 2 ≤ G.dist a u := by
    intro u hu1 hu2
    have h0 : G.dist a u ≠ 0 := fun h => hu1 (hconn.dist_eq_zero_iff.mp h).symm
    have h1 : G.dist a u ≠ 1 := fun h => hu2 (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have hdist2 : ∀ y, y ∉ l → ∀ j, (hj : j < m) → G.Adj y (f j) → G.dist a y = 2 := by
    intro y hy j hj hadj
    obtain ⟨h1, -⟩ := hyN y hy j hj hadj
    refine dist_two hconn h1 hadj.symm (hNa' y hy) ?_
    intro h
    exact hy (by rw [h]; exact List.head_mem hne)
  set Timg := T.image (fun i => f (i + 1)) with hTimg
  have hTi_card : Timg.card = σ := by
    rw [hTimg, Finset.card_image_of_injOn, hTcard]
    intro i hi i' hi' h
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hi1' := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
    have := hf_inj (i + 1) (i' + 1) (by omega) (by omega) h
    omega
  have hTimg_l : ∀ u ∈ Timg, u ∈ l := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact hf_mem _ (by omega)
  have hTimg_d : ∀ u ∈ Timg, 2 ≤ G.dist a u := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hi1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    apply hd2
    · intro h
      have := hf_inj (i + 1) 0 (by omega) (by omega) (h.trans hf0.symm)
      omega
    · intro h
      exact Finset.disjoint_left.mp hdisjST
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi1, h⟩) hi
  have hTim : ∀ k, k < m → k ≠ 0 → ¬ G.Adj a (f k) → f k ∈ Timg := by
    intro k hk hk0 hna
    rcases hpart (k - 1) (by omega) with h | h
    · rw [show k - 1 + 1 = k by omega] at h; exact absurd h hna
    · exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), h⟩, by rw [show k - 1 + 1 = k by omega]⟩
  set U := Finset.univ.filter (fun w => 2 ≤ G.dist a w) with hU
  set Rs := Finset.univ.filter (fun t => t ∉ l) with hRs
  have hRU : Rs ∪ Timg ⊆ U := by
    intro u hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hu with h | h
    · have hul : u ∉ l := by simpa [hRs] using h
      apply hd2
      · intro h'; exact hul (by rw [h']; exact List.head_mem hne)
      · exact hNa' u hul
    · exact hTimg_d u h
  have hdisjRT : Disjoint Rs Timg :=
    Finset.disjoint_left.mpr (fun u h1 h2 => by simp [hRs] at h1; exact h1 (hTimg_l u h2))
  have hUcard : Rs.card + σ ≤ U.card := by
    have := Finset.card_le_card hRU
    rw [Finset.card_union_of_disjoint hdisjRT, hTi_card] at this
    exact this
  set F := Finset.univ.filter (fun w => 3 ≤ G.dist a w ∧ Odd (G.dist a w)) with hF
  set R₀ := Rs.filter (fun y => ∀ j, j < m → ¬ G.Adj y (f j)) with hR₀
  have hFsub : F ⊆ insert x₀ R₀ := by
    intro w hwF
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hwF
    obtain ⟨hw3, -⟩ := hwF
    rw [Finset.mem_insert]
    by_cases hwl : w ∈ l
    · left
      obtain ⟨k, hk, rfl⟩ := hf_ex w hwl
      have hk0 : k ≠ 0 := by rintro rfl; rw [hf0] at hw3; simp at hw3
      have hna : ¬ G.Adj a (f k) := fun h => by
        have := SimpleGraph.dist_eq_one_iff_adj.mpr h; omega
      have hwT : f k ∈ Timg := hTim k hk hk0 hna
      by_contra hwx
      have hdeg := hx0 (f k) hwx
      have hnb : G.neighborFinset (f k) ⊆ Timg.erase (f k) := by
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        have hu2 := lemma3a hconn a (f k) hw3 u hu
        rw [Finset.mem_erase]
        refine ⟨hu.ne.symm, ?_⟩
        by_cases hul : u ∈ l
        · obtain ⟨k', hk', rfl⟩ := hf_ex u hul
          have hk0' : k' ≠ 0 := by rintro rfl; rw [hf0] at hu2; simp at hu2
          apply hTim k' hk' hk0'
          intro h
          have := SimpleGraph.dist_eq_one_iff_adj.mpr h; omega
        · exfalso
          exact hna (hyN u hul k hk hu.symm).1
      have hdw := Finset.card_le_card hnb
      rw [Finset.card_erase_of_mem hwT, hTi_card, SimpleGraph.card_neighborFinset_eq_degree] at hdw
      have hpos : 0 < Timg.card := Finset.card_pos.mpr ⟨_, hwT⟩
      omega
    · right
      simp only [hR₀, hRs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hwl, fun j hj hadj => ?_⟩
      have := hdist2 w hwl j hj hadj
      omega
  have h3b : U.card ≤ σ + F.card := lemma3b hconn a (hH a)
  have hFc : F.card ≤ R₀.card + 1 := by
    have h1 := Finset.card_le_card hFsub
    have h2 := Finset.card_insert_le x₀ R₀
    omega
  obtain ⟨v, hv, y, hy, hvy⟩ := exists_out_edge hconn l hne hnd hlt
  have hyRs : y ∈ Rs := by simp [hRs, hy]
  have h2y := Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy
  have hR3 : 3 ≤ Rs.card := by
    have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆ Rs.erase y := by
      intro w hw
      rw [Finset.mem_erase]
      refine ⟨?_, (Finset.mem_filter.mp hw).1⟩
      rintro rfl
      exact G.loopless.irrefl _ (Finset.mem_filter.mp hw).2
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hyRs] at this
    omega
  set R₁ := Rs.filter (fun y => ¬ ∀ j, j < m → ¬ G.Adj y (f j)) with hR₁
  have hsplit : R₀.card + R₁.card = Rs.card := Finset.card_filter_add_card_filter_not _
  have hR1le : R₁.card ≤ 1 := by omega
  have hyR1 : y ∈ R₁ := by
    obtain ⟨j, hj, rfl⟩ := hf_ex v hv
    simp only [hR₁, Finset.mem_filter]
    exact ⟨hyRs, fun h => h j hj hvy.symm⟩
  have hR1eq : ∀ w ∈ R₁, w = y := fun w hw =>
    Finset.card_le_one.mp hR1le w hw y hyR1
  have hy0 : y ∉ R₀ := by
    intro h
    simp only [hR₀, Finset.mem_filter] at h
    simp only [hR₁, Finset.mem_filter] at hyR1
    exact hyR1.2 h.2
  have hR0pos : R₀.Nonempty := Finset.card_pos.mp (by omega)
  refine cut_closed hb y R₀ hy0 hR0pos ?_ ⟨a, ?_, ?_⟩
  · intro w hw w' hww' hw'y
    simp only [hR₀, Finset.mem_filter] at hw
    by_cases hwl : w' ∈ l
    · obtain ⟨j, hj, rfl⟩ := hf_ex w' hwl
      exact absurd hww' (hw.2 j hj)
    · by_contra hn
      have hw'R : w' ∈ R₁ := by
        simp only [hR₁, hR₀, Finset.mem_filter] at hn ⊢
        have hw'Rs : w' ∈ Rs := by simp [hRs, hwl]
        exact ⟨hw'Rs, fun h => hn ⟨hw'Rs, h⟩⟩
      exact hw'y (hR1eq w' hw'R)
  · intro h
    exact hy (by rw [← h]; exact List.head_mem hne)
  · intro h
    simp only [hR₀, hRs, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.1 (List.head_mem hne)
lemma Cadre.two_attach [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ∃ a b, a < b ∧ b < l.length ∧ (∃ y ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y (l.getD a x₀)) ∧
      (∃ y ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y (l.getD b x₀)) := by
  classical
  have hhs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  obtain ⟨v, hv, y, hy, hvy⟩ := exists_out_edge hconn l hne hnd hlt
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hv
  have hga : ∀ i (h : i < l.length), l.getD i x₀ = l[i] := fun i h => List.getD_eq_getElem _ _ h
  have hyR : y ∈ Finset.univ.filter (fun t => t ∉ l) := by simp [hy]
  by_cases hother : ∃ b y', b < l.length ∧ b ≠ a ∧ y' ∉ l ∧ G.Adj y' (l.getD b x₀)
  · obtain ⟨b, y', hb', hba, hy', hadj'⟩ := hother
    have hy'R : y' ∈ Finset.univ.filter (fun t => t ∉ l) := by simp [hy']
    rcases lt_or_gt_of_ne hba with h | h
    · exact ⟨b, a, h, ha, ⟨y', hy'R, hadj'⟩, ⟨y, hyR, by rw [hga a ha]; exact hvy.symm⟩⟩
    · exact ⟨a, b, h, hb', ⟨y, hyR, by rw [hga a ha]; exact hvy.symm⟩, ⟨y', hy'R, hadj'⟩⟩
  · exfalso
    push Not at hother
    have ha0 : 0 < a := (lemma5abx hconn l hne hnd hch hhs y hy a ha
      (by rw [List.getD_eq_getElem _ _ ha]; exact hvy.symm)).1
    refine cut_closed hb l[a] (Finset.univ.filter (fun t => t ∉ l)) (by simp) ⟨y, hyR⟩ ?_ ?_
    · intro v' hv' w hvw hwc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
      intro hwl
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hwl
      have hia : i ≠ a := by
        rintro rfl; exact hwc rfl
      exact hother i v' hi hia hv' (by rw [hga i hi]; exact hvw)
    · refine ⟨l.getD 0 x₀, ?_, ?_⟩
      · rw [hga 0 (by omega)]
        intro h
        have := (List.Nodup.getElem_inj_iff hnd).mp h
        omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        rw [hga 0 (by omega)]; exact List.getElem_mem _
lemma b14_rcard {l : List V} (hnd : l.Nodup) (hlt : l.length < Fintype.card V) :
    ((Finset.univ.filter (fun t => t ∉ l))).card + l.length = Fintype.card V := by
  have h : Finset.univ.filter (fun t => t ∉ l) = (l.toFinset)ᶜ := by
    ext t; simp
  rw [h, Finset.card_compl, List.toFinset_card_of_nodup hnd]
  omega
lemma Cadre.R_ge3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    3 ≤ ((Finset.univ.filter (fun t => t ∉ l))).card := by
  classical
  have hc := b14_rcard hnd hlt
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.filter (fun t => t ∉ l))).card)
  have hyl : y ∉ l := by simpa using hy
  have h2 := Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hyl
  have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆ (Finset.univ.filter (fun t => t ∉ l)).erase y := by
    intro w hw
    rw [Finset.mem_erase]
    refine ⟨?_, (Finset.mem_filter.mp hw).1⟩
    rintro rfl
    exact G.loopless.irrefl _ (Finset.mem_filter.mp hw).2
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hy] at this
  omega
lemma Cadre.R_card [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) :
    ((Finset.univ.filter (fun t => t ∉ l))).card + l.length = Fintype.card V := by
  exact b14_rcard hnd hlt
lemma b14_two [DecidableRel G.Adj] {l : List V} {x c d : V}
    (hx : 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x)).card)
    (hE : ∀ w, w ∉ l → G.Adj x w → w = c ∨ w = d) (hcd : c ≠ d) : G.Adj x c ∧ G.Adj x d := by
  have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x) ⊆ {c, d} := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simpa using hE w hw.1 hw.2
  have hcard : ({c, d} : Finset V).card = 2 := Finset.card_pair hcd
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hc : c ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x) := by rw [heq]; simp
  have hd : d ∈ (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj x) := by rw [heq]; simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
  exact ⟨hc.2, hd.2⟩
lemma Cadre.R3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (h : ((Finset.univ.filter (fun t => t ∉ l))).card = 3) :
    ∃ u v w : V, (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w} ∧ u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
      G.Adj u v ∧ G.Adj v w ∧ G.Adj u w := by
  have hR2 : ∀ y, y ∉ l → 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card :=
    fun y hy => Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy
  obtain ⟨u, v, w, huv, huw, hvw, hR⟩ := Finset.card_eq_three.mp h
  have hmemR : ∀ t, t ∈ (Finset.univ.filter (fun t => t ∉ l)) ↔ t ∉ l := by intro t; simp
  have hu : u ∉ l := (hmemR u).mp (by rw [hR]; simp)
  have hv : v ∉ l := (hmemR v).mp (by rw [hR]; simp)
  have hw : w ∉ l := (hmemR w).mp (by rw [hR]; simp)
  have hE : ∀ x, ∀ t, t ∉ l → G.Adj x t → t ∈ ({u, v, w} : Finset V) := by
    intro x t ht _
    rw [← hR]; exact (hmemR t).mpr ht
  have hu' := b14_two (hR2 u hu) (c := v) (d := w) (fun t ht hadj => by
    have := hE u t ht hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | h | h
    · exact absurd hadj (G.loopless.irrefl _)
    · exact Or.inl h
    · exact Or.inr h) hvw
  have hv' := b14_two (hR2 v hv) (c := u) (d := w) (fun t ht hadj => by
    have := hE v t ht hadj
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | rfl | h
    · exact Or.inl h
    · exact absurd hadj (G.loopless.irrefl _)
    · exact Or.inr h) huw
  exact ⟨u, v, w, hR, huv, hvw, huw, hu'.1, hv'.2, hu'.2⟩
lemma b14_right [DecidableRel G.Adj] {l : List V}
    (hR2 : ∀ y, y ∉ l → 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card)
    (p p' a b : V) (hset : Finset.univ.filter (fun t => t ∉ l) = {p, p', a, b})
    (h1 : p ≠ p') (h2 : p ≠ a) (h3 : p ≠ b) (h4 : p' ≠ a) (h5 : p' ≠ b) (h6 : a ≠ b)
    (hn : ¬ G.Adj p p') :
    ∃ z z' a b : V, (Finset.univ.filter (fun t => t ∉ l)) = {z, z', a, b} ∧ z ≠ z' ∧ z ≠ a ∧ z ≠ b ∧ z' ≠ a ∧ z' ≠ b ∧ a ≠ b ∧
      ¬ G.Adj z z' ∧ G.Adj z a ∧ G.Adj z b ∧ G.Adj z' a ∧ G.Adj z' b := by
  have hmemR : ∀ t, t ∈ Finset.univ.filter (fun t => t ∉ l) ↔ t ∉ l := by intro t; simp
  have hp : p ∉ l := (hmemR p).mp (by rw [hset]; simp)
  have hp' : p' ∉ l := (hmemR p').mp (by rw [hset]; simp)
  have hE : ∀ t, t ∉ l → t = p ∨ t = p' ∨ t = a ∨ t = b := by
    intro t ht
    have : t ∈ ({p, p', a, b} : Finset V) := by rw [← hset]; exact (hmemR t).mpr ht
    simpa using this
  have e1 := b14_two (hR2 p hp) (c := a) (d := b) (fun t ht hadj => by
    rcases hE t ht with h | h | h | h
    · rw [h] at hadj; exact absurd hadj (G.loopless.irrefl _)
    · rw [h] at hadj; exact absurd hadj hn
    · exact Or.inl h
    · exact Or.inr h) h6
  have e2 := b14_two (hR2 p' hp') (c := a) (d := b) (fun t ht hadj => by
    rcases hE t ht with h | h | h | h
    · rw [h] at hadj; exact absurd hadj.symm hn
    · rw [h] at hadj; exact absurd hadj (G.loopless.irrefl _)
    · exact Or.inl h
    · exact Or.inr h) h6
  exact ⟨p, p', a, b, hset, h1, h2, h3, h4, h5, h6, hn, e1.1, e1.2, e2.1, e2.2⟩
lemma Cadre.R4 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (h : ((Finset.univ.filter (fun t => t ∉ l))).card = 4) :
    (∃ a b c d : V, (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d) ∨
    (∃ z z' a b : V, (Finset.univ.filter (fun t => t ∉ l)) = {z, z', a, b} ∧ z ≠ z' ∧ z ≠ a ∧ z ≠ b ∧ z' ≠ a ∧ z' ≠ b ∧ a ≠ b ∧
      ¬ G.Adj z z' ∧ G.Adj z a ∧ G.Adj z b ∧ G.Adj z' a ∧ G.Adj z' b) := by
  have hR2 : ∀ y, y ∉ l → 2 ≤ ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card :=
    fun y hy => Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hy
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hR⟩ := Finset.card_eq_four.mp h
  by_cases hall : G.Adj x y ∧ G.Adj x z ∧ G.Adj x w ∧ G.Adj y z ∧ G.Adj y w ∧ G.Adj z w
  · left
    exact ⟨x, y, z, w, hR, hxy, hxz, hxw, hyz, hyw, hzw, hall.1, hall.2.1, hall.2.2.1,
      hall.2.2.2.1, hall.2.2.2.2.1, hall.2.2.2.2.2⟩
  · right
    have hn : ¬G.Adj x y ∨ ¬G.Adj x z ∨ ¬G.Adj x w ∨ ¬G.Adj y z ∨ ¬G.Adj y w ∨ ¬G.Adj z w := by
      tauto
    rcases hn with hn | hn | hn | hn | hn | hn
    · exact b14_right hR2 x y z w hR hxy hxz hxw hyz hyw hzw hn
    · exact b14_right hR2 x z y w (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hxz hxy hxw hyz.symm hzw hyw hn
    · exact b14_right hR2 x w y z (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hxw hxy hxz hyw.symm hzw.symm hyz hn
    · exact b14_right hR2 y z x w (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hyz hxy.symm hyw hxz.symm hzw hxw hn
    · exact b14_right hR2 y w x z (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hyw hxy.symm hyz hxw.symm hzw.symm hxz hn
    · exact b14_right hR2 z w x y (by rw [hR]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hh <;> rcases hh with hh | hh | hh | hh <;> simp [hh]) hzw hxz.symm hyz.symm hxw.symm hyw.symm hxy hn
lemma Cadre.small_sigma [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hham : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∃ s : List V, s.Nodup ∧ s.IsChain G.Adj ∧ s.toFinset = (Finset.univ.filter (fun t => t ∉ l)) ∧
      s.getLast? = some y)
    (hd2 : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∀ y' ∈ (Finset.univ.filter (fun t => t ∉ l)), y ≠ y' →
      G.Adj y y' ∨ ∃ w ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y w ∧ G.Adj w y') :
    ((Finset.univ.filter (fun t => t ∉ l))).card + 5 ≤ l.length := by
  classical
  obtain ⟨a, b, hab, hbl, ⟨y, hy, hya⟩, ⟨y', hy', hyb⟩⟩ :=
    Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hyl : y ∉ l := (Finset.mem_filter.1 hy).2
  have hyl' : y' ∉ l := (Finset.mem_filter.1 hy').2
  obtain ⟨i₀, hi₀, hxi⟩ := List.mem_iff_getElem.1 hmem
  have hxi' : l.getD i₀ x₀ = x₀ := by rw [List.getD_eq_getElem _ _ hi₀]; exact hxi
  have hi0pos : i₀ ≠ 0 := by
    intro h; subst h; apply hhd; rw [b15_head hne x₀]; exact hxi'
  have hi0last : i₀ ≠ l.length - 1 := by
    intro h; apply hlast; rw [b15_last hne x₀, ← h]; exact hxi'
  have hnx : ∀ i, i < l.length → i ≠ i₀ → l.getD i x₀ ≠ x₀ :=
    fun i hi hne' h => hne' (b15_inj x₀ hnd hi hi₀ (h.trans hxi'.symm))
  have hr3 : 3 ≤ (Finset.univ.filter (fun t => t ∉ l)).card := by
    have h2 := Cadre.Rdeg2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y hyl
    have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆
        (Finset.univ.filter (fun t => t ∉ l)).erase y := by
      intro v hv
      rw [Finset.mem_filter] at hv
      exact Finset.mem_erase.2 ⟨fun h => G.loopless.irrefl y (h ▸ hv.2), hv.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy] at this
    omega
  have hpath : ∀ z ∈ Finset.univ.filter (fun t => t ∉ l), ∃ s : List V, ∃ hs : s ≠ [], s.Nodup ∧
      s.IsChain G.Adj ∧ (∀ v ∈ s, v ∉ l) ∧ s.getLast hs = z ∧
      s.length = (Finset.univ.filter (fun t => t ∉ l)).card := by
    intro z hz
    obtain ⟨s, snd, sch, hsR, hsl⟩ := hham z hz
    have hs : s ≠ [] := by intro h; rw [h] at hsl; simp at hsl
    refine ⟨s, hs, snd, sch, ?_, ?_, ?_⟩
    · intro v hv
      have : v ∈ s.toFinset := List.mem_toFinset.2 hv
      rw [hsR] at this
      exact (Finset.mem_filter.1 this).2
    · have := List.getLast?_eq_getLast hs
      rw [hsl] at this
      exact (Option.some.inj this).symm
    · rw [← hsR]; exact (List.toFinset_card_of_nodup snd).symm
  have hL : i₀ < a ∨ (Finset.univ.filter (fun t => t ∉ l)).card ≤ a := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs, snd, sch, sl, hlast_eq, hslen⟩ := hpath y hy
    exact Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch sl a
      (by omega) (by rw [hlast_eq]; exact hya) (fun i hi => hnx i (by omega) (by omega)) (by omega)
  have hRr : b < i₀ ∨ (Finset.univ.filter (fun t => t ∉ l)).card ≤ l.length - 1 - b := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs, snd, sch, sl, hlast_eq, hslen⟩ := hpath y' hy'
    have hs' : s.reverse ≠ [] := by simpa using hs
    have hhead : s.reverse.head hs' = y' := by rw [List.head_reverse]; exact hlast_eq
    exact Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s.reverse hs'
      (List.nodup_reverse.2 snd) (chain_rev sch) (fun v hv => sl v (List.mem_reverse.1 hv)) b hbl
      (by rw [hhead]; exact hyb.symm) (fun i h1 h2 => hnx i h2 (by omega))
      (by rw [List.length_reverse]; omega)
  have hM : a + 2 ≤ b := by
    by_contra hcon
    have hb1 : b = a + 1 := by omega
    by_cases hyy : y = y'
    · subst hyy
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y]
        (by simp) (by simp) (by simp) (by simpa using hyl) a b hab hbl (by simpa using hya.symm)
        (by simpa using hyb) (fun i h1 h2 => absurd h2 (by omega)) (by simp; omega)
    · by_cases hadj : G.Adj y y'
      · exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, y']
          (by simp) (by simp [hyy]) (by simp [hadj]) (by simp [hyl, hyl']) a b hab hbl
          (by simpa using hya.symm) (by simpa using hyb) (fun i h1 h2 => absurd h2 (by omega))
          (by simp; omega)
      · obtain ⟨w, hw, hyw, hwy'⟩ := (hd2 y hy y' hy' hyy).resolve_left hadj
        have hwl : w ∉ l := (Finset.mem_filter.1 hw).2
        exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y, w, y']
          (by simp)
          (by simp [hyy, hyw.ne, hwy'.ne])
          (by simp [hyw, hwy'])
          (by simp [hyl, hwl, hyl']) a b hab hbl
          (by simpa using hya.symm) (by simpa using hyb) (fun i h1 h2 => absurd h2 (by omega))
          (by simp; omega)
  omega
lemma b16_inv (E : Finset ℕ) (K i₀ : ℕ) (s : Finset ℕ) :
    (∀ x ∈ s, 1 ≤ x) → ((∀ x ∈ s, K + 1 ≤ x) ∨ (∀ x ∈ s, i₀ < x)) →
    (∀ a ∈ s, ∀ b ∈ s, a < b → (∀ c ∈ s, ¬ (a < c ∧ c < b)) →
      a + 2 ≤ b ∧ (a ∉ E → a + (K + 1) + 1 ≤ b ∨ (a < i₀ ∧ i₀ < b))) →
    ∀ a ∈ s, (∀ x ∈ s, x ≤ a) →
      (K + 2) * s.card ≤ a + 1 + K * (((s.erase a).filter (· ∈ E)).card + if i₀ < a then 1 else 0) := by
  induction s using Finset.induction_on_max with
  | empty => intro _ _ _ a ha; simp at ha
  | insert a s hlt ih =>
    intro h1 hL hM a' ha' hmax'
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ea : a = a' := by
      have h3 := hmax' a (Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.1 ha' with h | h
      · exact h.symm
      · have := hlt a' h; omega
    subst ea
    rw [Finset.card_insert_of_notMem has, Finset.erase_insert has]
    rcases s.eq_empty_or_nonempty with rfl | hne
    · have h0 := h1 a (Finset.mem_insert_self _ _)
      simp only [Finset.card_empty, Finset.filter_empty, zero_add]
      rcases hL with hL | hL
      · have := hL a (Finset.mem_insert_self _ _)
        split_ifs <;> simp <;> nlinarith
      · have := hL a (Finset.mem_insert_self _ _)
        rw [if_pos this]
        simp only [Finset.card_empty, mul_one]
        nlinarith
    · obtain ⟨m0, hm0, hm0max⟩ := Finset.exists_max_image s id hne
      have ih' := ih (fun x hx => h1 x (Finset.mem_insert_of_mem hx))
        (hL.imp (fun h x hx => h x (Finset.mem_insert_of_mem hx))
          (fun h x hx => h x (Finset.mem_insert_of_mem hx)))
        (by
          intro a1 ha1 b1 hb1 hab hno
          refine hM a1 (Finset.mem_insert_of_mem ha1) b1 (Finset.mem_insert_of_mem hb1) hab ?_
          intro c hc
          rcases Finset.mem_insert.1 hc with rfl | hc
          · have := hlt b1 hb1; omega
          · exact hno c hc)
        m0 hm0 (fun x hx => hm0max x hx)
      have hMa := hM m0 (Finset.mem_insert_of_mem hm0) a (Finset.mem_insert_self _ _) (hlt m0 hm0)
        (by
          intro c hc
          rcases Finset.mem_insert.1 hc with rfl | hc
          · omega
          · have := hm0max c hc; simp only [id] at this; omega)
      have hf : (s.filter (· ∈ E)).card = ((s.erase m0).filter (· ∈ E)).card + if m0 ∈ E then 1 else 0 := by
        rw [Finset.filter_erase]
        by_cases hE : m0 ∈ E
        · have hmf : m0 ∈ s.filter (· ∈ E) := Finset.mem_filter.2 ⟨hm0, hE⟩
          rw [Finset.card_erase_of_mem hmf, if_pos hE]
          have := Finset.card_pos.2 ⟨m0, hmf⟩
          omega
        · rw [Finset.erase_eq_of_notMem (fun h => hE (Finset.mem_filter.1 h).2), if_neg hE]; rfl
      rw [hf]
      by_cases hE : m0 ∈ E
      · have h5 := hMa.1
        rw [if_pos hE]
        split_ifs at ih' ⊢ <;> simp only [mul_add, mul_one] at ih' ⊢ <;> omega
      · have h5 := hMa.1
        have h6 := hMa.2 hE
        rw [if_neg hE]
        split_ifs at ih' ⊢ <;> simp only [mul_add, mul_one, add_zero, mul_zero] at ih' ⊢ <;> omega
lemma pack (A E : Finset ℕ) (m k i₀ : ℕ) (hk : 1 ≤ k) (hA : A.Nonempty) (hE : E ⊆ A)
    (hAm : ∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ m) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ m)
    (hL : k ≤ A.min' hA ∨ i₀ < A.min' hA)
    (hR : A.max' hA + k + 1 ≤ m ∨ A.max' hA < i₀)
    (hM : ∀ a ∈ A, ∀ b ∈ A, a < b → (∀ c ∈ A, ¬ (a < c ∧ c < b)) →
        a + 2 ≤ b ∧ (a ∉ E → a + k + 1 ≤ b ∨ (a < i₀ ∧ i₀ < b))) :
    (k + 1) * A.card + 1 ≤ m + (k - 1) * E.card := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  have hLs : (∀ x ∈ A, K + 1 ≤ x) ∨ (∀ x ∈ A, i₀ < x) :=
    hL.imp (fun h x hx => h.trans (A.min'_le x hx)) (fun h x hx => h.trans_le (A.min'_le x hx))
  have hinv := b16_inv E K i₀ A (fun x hx => (hAm x hx).1) hLs hM (A.max' hA) (A.max'_mem hA)
    (fun x hx => A.le_max' x hx)
  have hfe : ((A.erase (A.max' hA)).filter (· ∈ E)).card ≤ E.card :=
    Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2)
  have hKE := Nat.mul_le_mul_left K hfe
  have hmx := (hAm _ (A.max'_mem hA)).2
  simp only [Nat.add_sub_cancel]
  rcases hR with hR | hR
  · split_ifs at hinv <;> simp only [mul_add, mul_one, add_zero, mul_zero] at hinv ⊢ <;> nlinarith
  · rw [if_neg (by omega)] at hinv
    simp only [mul_add, mul_zero, add_zero] at hinv ⊢
    nlinarith
lemma Cadre.x0_attach [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (S : Finset V) (hS : ∀ y ∈ S, y ∉ l) (p : ℕ) (hp : 1 ≤ p) (hp1 : p + 1 < l.length)
    (hx : l.getD p x₀ = x₀) (hSA : ∀ y ∈ S, G.Adj y x₀) :
    S.card + 2 ≤ secondSmallestDegree G := by
  have hmx := deg_x0_le hmin
  have hpl : p < l.length := by omega
  have hA : G.Adj (l.getD (p - 1) x₀) x₀ := by
    have := b15_adj (G := G) x₀ hch (i := p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp, hx] at this
  have hB : G.Adj x₀ (l.getD (p + 1) x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p) (by omega)
    rwa [hx] at this
  have hne1 : l.getD (p - 1) x₀ ≠ l.getD (p + 1) x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) h
    omega
  have hAS : l.getD (p - 1) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  have hBS : l.getD (p + 1) x₀ ∉ S := fun h => hS _ h (b15_mem x₀ (by omega))
  have hsub : insert (l.getD (p - 1) x₀) (insert (l.getD (p + 1) x₀) S) ⊆ G.neighborFinset x₀ := by
    intro v hv
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact hA.symm
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact hB
    · exact (hSA v hv).symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by rw [Finset.mem_insert]; rintro (h | h); exacts [hne1 h, hAS h]), Finset.card_insert_of_notMem hBS,
    SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega
lemma b19_perm4 (t seg s d : List V) :
    (t ++ (s ++ (seg.reverse ++ d))).Perm (s ++ (t ++ (seg ++ d))) := by
  refine List.perm_iff_count.2 (fun a => ?_)
  simp only [List.count_append, List.count_reverse]
  omega
lemma b19_split (l : List V) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ l.length) :
    l = l.take i ++ ((l.drop i).take (j - i) ++ l.drop j) := by
  have e : (l.drop i).drop (j - i) = l.drop j := by
    rw [List.drop_drop]; congr 1; omega
  conv_lhs => rw [← List.take_append_drop i l, ← List.take_append_drop (j - i) (l.drop i), e]
lemma b19_seglast (l : List V) (d : V) {p q : ℕ} (hpq : p + 3 ≤ q) (hq : q < l.length) :
    ((l.drop (p + 1)).take (q - p)).getLast? = some (l.getD q d) := by
  rw [List.getLast?_take, if_neg (by omega), List.getElem?_drop,
    show p + 1 + (q - p - 1) = q by omega, List.getElem?_eq_getElem hq,
    List.getD_eq_getElem _ _ hq]
  rfl
lemma b19_seghead (l : List V) (d : V) {p q : ℕ} (hpq : p + 3 ≤ q) (hq : q < l.length) :
    ((l.drop (p + 1)).take (q - p)).head? = some (l.getD (p + 1) d) := by
  rw [List.head?_take, if_neg (by omega), List.head?_drop, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem _ _ (by omega)]
lemma Cadre.walk_x0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (s : List V) (hs : s ≠ []) (snd : s.Nodup) (sch : s.IsChain G.Adj) (sl : ∀ v ∈ s, v ∉ l)
    (p q : ℕ) (hp : 1 ≤ p) (hpq : p + 3 ≤ q) (hq : q + 1 < l.length) (hx : l.getD (p + 1) x₀ = x₀)
    (hsp : ∀ y ∈ s, G.Adj y (l.getD p x₀)) (hsq : ∀ y ∈ s, G.Adj y (l.getD q x₀))
    (hσ : secondSmallestDegree G ≤ s.length + 1) (hg : q - p - 1 ≤ s.length) : False := by
  have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hp2 : p + 2 < l.length := by omega
  have hA : G.Adj (l.getD p x₀) x₀ := by
    have := b15_adj (G := G) x₀ hch (i := p) (by omega)
    rwa [hx] at this
  have hB : G.Adj x₀ (l.getD (p + 2) x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p + 1) (by omega)
    rwa [hx] at this
  have hAa : G.Adj (l.getD (p - 1) x₀) (l.getD p x₀) := by
    have := b15_adj (G := G) x₀ hch (i := p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp] at this
  have hsl := List.getLast?_eq_getLast hs
  have hhs : G.Adj (l.getD p x₀) (s.head hs) := (hsp _ (List.head_mem hs)).symm
  have hls : G.Adj (s.getLast hs) (l.getD q x₀) := hsq _ (List.getLast_mem hs)
  have hne_a : l.getD (p - 1) x₀ ≠ x₀ := by
    intro h
    have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
    omega
  have hna : ¬ G.Adj (l.getD (p - 1) x₀) x₀ := by
    intro hadj
    have hd := b17_decomp l x₀ (i := p) (by omega)
    rw [hx] at hd
    have hsub : (l.take p ++ l.getD p x₀ :: x₀ :: l.drop q).Sublist
        (l.take p ++ l.getD p x₀ :: x₀ :: l.drop (p + 2)) :=
      List.Sublist.append (List.Sublist.refl _)
        (List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.drop_sublist_drop_left l (by omega))))
    rw [← hd] at hsub
    have hl''nd := hnd.sublist hsub
    have hperm := b17_perm1 (l.take p) (l.drop q) s (l.getD p x₀) x₀
    have hcnd : (l.take p ++ x₀ :: l.getD p x₀ :: (s ++ l.drop q)).Nodup :=
      hperm.nodup_iff.2 (List.nodup_append.2 ⟨snd, hl''nd, fun a ha b hb h =>
        sl a ha (h ▸ hsub.subset hb)⟩)
    have hchain : (l.take p ++ x₀ :: l.getD p x₀ :: (s ++ l.drop q)).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hch.take _, ?_, ?_⟩
      · refine List.isChain_cons.2 ⟨?_, List.isChain_cons.2 ⟨?_, List.isChain_append.2 ⟨sch, hch.drop _, ?_⟩⟩⟩
        · intro z hz
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hA.symm
        · intro z hz
          rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hz
          subst hz; exact hhs
        · intro z hz w hw
          rw [hsl, Option.mem_def, Option.some.injEq] at hz
          rw [b17_head_drop x₀ (by omega), Option.mem_def, Option.some.injEq] at hw
          subst hz hw; exact hls
      · intro z hz w hw
        rw [b17_last_take x₀ hp (by omega), Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        subst hz hw; exact hadj
    have := hmax _ hcnd hchain (List.mem_append_right _ (List.mem_cons_self ..))
    simp only [List.length_append, List.length_cons, List.length_take, List.length_drop] at this
    omega
  have hSd : ∀ y ∈ s, G.dist x₀ y = 2 := by
    intro y hy
    have hyl := sl y hy
    have hyx : y ≠ x₀ := fun h => hyl (h ▸ hmem)
    have hadj' : G.Adj y (l.getD p y) := by
      rw [b15_dflt (l := l) (i := p) (by omega) y x₀]; exact hsp y hy
    obtain ⟨-, -, h5, -, -, -⟩ := lemma5abx hconn l hne hnd hch hmx y hyl p (by omega) hadj'
    exact dist_two hconn hA.symm (hsp y hy).symm
      (fun h' => h5 (by rw [b15_dflt (l := l) (i := p + 1) (by omega) y x₀, hx]; exact h'.symm)) hyx
  have hAS : l.getD (p - 1) x₀ ∉ s.toFinset := fun h =>
    sl _ (List.mem_toFinset.1 h) (b15_mem x₀ (by omega))
  have hS0 : ∀ w ∈ insert (l.getD (p - 1) x₀) s.toFinset, G.dist x₀ w = 2 := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact dist_two hconn hA.symm hAa.symm (fun h' => hna h'.symm) hne_a
    · exact hSd w (List.mem_toFinset.1 hw)
  have hS0c : (insert (l.getD (p - 1) x₀) s.toFinset).card = s.length + 1 := by
    rw [Finset.card_insert_of_notMem hAS, List.toFinset_card_of_nodup snd]
  have hadjall : ∀ i, p + 2 ≤ i → i ≤ q + 1 → G.Adj x₀ (l.getD i x₀) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _; exact hB
    | succ i hi ih =>
      intro hiq
      have ih := ih (by omega)
      by_contra hn
      have hnl : l.getD (i + 1) x₀ ∉ insert (l.getD (p - 1) x₀) s.toFinset := by
        rw [Finset.mem_insert, not_or]
        refine ⟨fun h => ?_, fun h => sl _ (List.mem_toFinset.1 h) (b15_mem x₀ (by omega))⟩
        have := b15_inj x₀ hnd (by omega) (by omega) h
        omega
      have hne' : l.getD (i + 1) x₀ ≠ x₀ := by
        intro h
        have := b15_inj x₀ hnd (by omega) (by omega) (h.trans hx.symm)
        omega
      have hd2' := dist_two hconn ih (b15_adj (G := G) x₀ hch (i := i) (by omega)) hn hne'
      have hc := card_le_gamma hconn hH x₀ (insert (l.getD (i + 1) x₀) (insert (l.getD (p - 1) x₀) s.toFinset))
        (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hd2'
          · exact hS0 w hw)
      rw [Finset.card_insert_of_notMem hnl, hS0c] at hc
      omega
  have hlast_adj := hadjall (q + 1) (by omega) le_rfl
  have hc4 : ((l.take (p + 1) ++ (s ++ (((l.drop (p + 1)).take (q - p)).reverse ++ l.drop (q + 1))))).IsChain G.Adj := by
    refine List.isChain_append.2 ⟨hch.take _, List.isChain_append.2 ⟨sch,
      List.isChain_append.2 ⟨chain_rev ((hch.drop _).take _), hch.drop _, ?_⟩, ?_⟩, ?_⟩
    · intro z hz w hw
      rw [List.getLast?_reverse, b19_seghead l x₀ (by omega) (by omega), Option.mem_def,
        Option.some.injEq] at hz
      rw [b17_head_drop x₀ (by omega), Option.mem_def, Option.some.injEq] at hw
      subst hz hw
      rw [hx]; exact hlast_adj
    · intro z hz w hw
      rw [hsl, Option.mem_def, Option.some.injEq] at hz
      have hrev : (((l.drop (p + 1)).take (q - p)).reverse ++ l.drop (q + 1)).head? =
          some (l.getD q x₀) := by
        rw [List.head?_append, List.head?_reverse, b19_seglast l x₀ (by omega) (by omega)]
        rfl
      rw [hrev, Option.mem_def, Option.some.injEq] at hw
      subst hz hw; exact hls
    · intro z hz w hw
      have hz' := b17_last_take (l := l) x₀ (p := p + 1) (by omega) (by omega)
      rw [hz', Option.mem_def, Option.some.injEq] at hz
      rw [b17_head_app hs, Option.mem_def, Option.some.injEq] at hw
      subst hz hw
      simpa using hhs
  have hperm := b19_perm4 (l.take (p + 1)) ((l.drop (p + 1)).take (q - p)) s (l.drop (q + 1))
  have hsplit := b19_split l (i := p + 1) (j := q + 1) (by omega) (by omega)
  have e1 : q + 1 - (p + 1) = q - p := by omega
  rw [e1] at hsplit
  rw [← hsplit] at hperm
  exact b17_long hnd sl snd hs hmem hmax hperm hc4
lemma Cadre.head_deg_le [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (C : Finset ℕ)
    (hex : ∀ j, 0 < j → j < l.length → j ∉ C → ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀)) :
    G.degree (l.getD 0 x₀) ≤ C.card := by
  have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have h2 := b15_len2 hne hmem hhd
  obtain ⟨-, -, -, -, h5, -⟩ := lemma4x hconn l hne hnd hch hmx hlt h2
  have e := b15_head hne x₀
  rw [← e]
  refine h5.trans (Finset.card_le_card_of_injOn (fun j => j + 1) ?_ ?_)
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    show j + 1 ∈ C
    by_contra hC'
    apply hex (j + 1) (by omega) (by omega) hC'
    have := hj.2
    rwa [e, b15_dflt (l := l) (i := j + 1) (by omega) (l.getD 0 x₀) x₀] at this
  · intro a _ b _ h
    simpa using h
lemma Cadre.head_forced [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (C : Finset ℕ) (hCr : ∀ j ∈ C, 0 < j ∧ j < l.length)
    (hex : ∀ j, 0 < j → j < l.length → j ∉ C → ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀))
    (hdeg : C.card ≤ G.degree (l.getD 0 x₀)) :
    ∀ j ∈ C, G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
  intro j hj
  by_contra hadj
  have h := Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (C.erase j)
    (by
      intro j' h0 h1 hj'
      by_cases e : j' = j
      · subst e; exact hadj
      · exact hex j' h0 h1 (fun h => hj' (Finset.mem_erase.2 ⟨e, h⟩)))
  rw [Finset.card_erase_of_mem hj] at h
  have := Finset.card_pos.2 ⟨j, hj⟩
  omega
lemma Cadre.last_deg_le [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (C : Finset ℕ)
    (hex : ∀ j, j + 1 < l.length → j ∉ C →
      ¬ G.Adj (l.getD j x₀) (l.getD (l.length - 1) x₀)) :
    G.degree (l.getD (l.length - 1) x₀) ≤ C.card := by
  have hmx := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have h2 := b15_len2 hne hmem hhd
  obtain ⟨-, -, -, -, -, h5⟩ := lemma4x hconn l hne hnd hch hmx hlt h2
  have e := b15_last hne x₀
  rw [← e]
  refine h5.trans (Finset.card_le_card ?_)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  by_contra hC'
  apply hex j (by omega) hC'
  have := hj.2
  rwa [e, b15_dflt (l := l) (i := j) (by omega) (l.head hne) x₀] at this
lemma b22_E [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w)
    (huw : u ≠ w) (h1 : G.Adj u v) (h2 : G.Adj v w)
    (a j : ℕ) (hA : G.Adj w (l.getD a x₀)) (haj : a < j) (hj : j < l.length) (hja : j ≤ a + 3)
    (hx : ∃ i, (i ≤ a ∨ j ≤ i) ∧ i < l.length ∧ l.getD i x₀ = x₀) :
    ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
  intro h
  have hs : [u, v, w] ≠ [] := by simp
  have snd : [u, v, w].Nodup := by simp [huv, hvw, huw]
  have sch : [u, v, w].IsChain G.Adj := by simp [List.isChain_cons_cons, h1, h2]
  have sl : ∀ x ∈ [u, v, w], x ∉ l := by
    intro x hx'
    have : x ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simpa using hx'
    simpa using this
  exact Cadre.endE hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [u, v, w] hs snd sch sl a j haj hj h (by simpa using hA) hx
    (by simp; omega)
lemma b22_gam [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (y : V) (hy : y ∉ l) (P : Finset ℕ)
    (hP : ∀ a ∈ P, 2 ≤ a ∧ a + 1 < l.length ∧ G.Adj y (l.getD a x₀)) :
    ∀ a ∈ P, secondSmallestDegree G < (P.image (· + 1) ∪ P.image (· - 1)).card + 1 →
      ¬ G.Adj (l.getD 0 x₀) (l.getD a x₀) := by
  intro a ha hcard h
  have hl0 : 0 < l.length := List.length_pos_iff.mpr hne
  have hn0 : ¬ G.Adj y (l.getD 0 x₀) := by
    intro hh
    have := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy (j := 0)
      (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hl0, hh⟩)
    omega
  set I : Finset ℕ := insert 0 (P.image (· + 1) ∪ P.image (· - 1)) with hI
  have hmemD : ∀ i ∈ P.image (· + 1) ∪ P.image (· - 1), i < l.length ∧ G.dist y (l.getD i x₀) = 2 := by
    intro i hi
    refine Cadre.dset_dist hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy ?_
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a',
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hP a' ha'; omega), (hP a' ha').2.2⟩, rfl⟩)
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a',
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hP a' ha'; omega), (hP a' ha').2.2⟩, rfl⟩)
  have hmemI : ∀ i ∈ I, i < l.length ∧ G.dist y (l.getD i x₀) = 2 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · refine ⟨hl0, dist_two hconn (a := l.getD a x₀) (hP a ha).2.2 h.symm hn0 ?_⟩
      intro e
      exact hy (by rw [← e]; exact List.getD_eq_getElem _ _ hl0 ▸ List.getElem_mem _)
    · exact hmemD i hi
  have h0 : (0 : ℕ) ∉ P.image (· + 1) ∪ P.image (· - 1) := by
    intro h0
    rcases Finset.mem_union.mp h0 with h0 | h0
    · obtain ⟨a', ha', e⟩ := Finset.mem_image.mp h0; omega
    · obtain ⟨a', ha', e⟩ := Finset.mem_image.mp h0
      have := (hP a' ha').1; omega
  have hcardI : I.card = (P.image (· + 1) ∪ P.image (· - 1)).card + 1 := by
    rw [hI, Finset.card_insert_of_notMem h0]
  have hinj : Set.InjOn (fun i => l.getD i x₀) (I : Set ℕ) := by
    intro i hi i' hi' he
    have e1 := (hmemI i hi).1
    have e2 := (hmemI i' hi').1
    simp only at he
    rw [List.getD_eq_getElem _ _ e1, List.getD_eq_getElem _ _ e2] at he
    exact (List.Nodup.getElem_inj_iff hnd).mp he
  have hle := card_le_gamma hconn hH y (I.image (fun i => l.getD i x₀)) (by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact (hmemI i hi).2)
  rw [Finset.card_image_of_injOn hinj, hcardI] at hle
  omega
lemma b22_h0 {l : List V} {x₀ : V} (hne : l ≠ []) (hhd : l.head hne ≠ x₀) : l.getD 0 x₀ ≠ x₀ := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => simpa using hhd
lemma Cadre.C1 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 10)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 6 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {2, 6} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 1 ∧ l.getD i0 x₀ = x₀ := ⟨1, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 10 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact hGa 2 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 3 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 6 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 7 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1} : Finset ℕ).card < 4 := by decide
  omega
lemma Cadre.C3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 6 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {2, 6} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 1 ∧ l.getD i0 x₀ = x₀ := ⟨1, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 10} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 10} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact hGa 2 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 3 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 6 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 7 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 6 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact absurd (by simp) hjC
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 10} : Finset ℕ).card < 4 := by decide
  omega
lemma Cadre.C4 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {2, 7} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 1 ∧ l.getD i0 x₀ = x₀ := ⟨1, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 6} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 6} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact hGa 2 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 3 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 2 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact absurd (by simp) hjC
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 10 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 6} : Finset ℕ).card < 4 := by decide
  omega
lemma Cadre.C5 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 1 x₀ = x₀ ∨ l.getD 2 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {3, 7} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, (1 ≤ i0 ∧ i0 ≤ 2) ∧ l.getD i0 x₀ = x₀ := by rcases hx with h | h; exact ⟨1, by omega, h⟩; exact ⟨2, by omega, h⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 2} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 2} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact absurd (by simp) hjC
    · exact hGa 3 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 6 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 10 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 2} : Finset ℕ).card < 4 := by decide
  omega
lemma Cadre.C9 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 4) (hm : l.length = 11)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 5 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {3, 7} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 5 ∧ l.getD i0 x₀ = x₀ := ⟨5, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 2, 6} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 2, 6} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 11 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact absurd (by simp) hjC
    · exact hGa 3 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact absurd (by simp) hjC
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 9 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 10 (hA w (by simp)).2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 2, 6} : Finset ℕ).card < 4 := by decide
  omega
lemma Cadre.C10 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 5) (hm : l.length = 13)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 7 x₀) ∧ G.Adj y (l.getD 9 x₀))
    (hx : l.getD 8 x₀ = x₀) : False := by
  have hu : u ∉ l := by
    have : u ∈ Finset.univ.filter (fun t => t ∉ l) := by rw [hR]; simp
    simpa using this
  have hGa := b22_gam hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u hu {3, 7, 9} (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2.1)⟩
    · exact ⟨by norm_num, by omega, ((hA u (by simp)).2.2)⟩)
  obtain ⟨i0, hi0, hx'⟩ : ∃ i0, i0 = 8 ∧ l.getD i0 x₀ = x₀ := ⟨8, rfl, hx⟩
  have hdeg : G.degree (l.getD 0 x₀) ≤ ({1, 2} : Finset ℕ).card := by
    refine Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt {1, 2} ?_
    intro j hj0 hjm hjC
    have hjm' : j < 13 := by omega
    interval_cases j
    · exact absurd (by simp) hjC
    · exact absurd (by simp) hjC
    · exact hGa 3 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 4 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 5 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 3 6 (hA w (by simp)).1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 7 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 7 8 (hA w (by simp)).2.1 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact hGa 9 (by simp) (by rw [hσ]; decide)
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 9 10 (hA w (by simp)).2.2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 9 11 (hA w (by simp)).2.2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
    · exact b22_E hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 9 12 (hA w (by simp)).2.2 (by omega) (by omega) (by omega) ⟨i0, by omega, by omega, hx'⟩
  have h4 := hx0 _ (b22_h0 hne hhd)
  have hc : ({1, 2} : Finset ℕ).card < 5 := by decide
  omega
lemma b21_clq {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) :
    ∀ a ∈ ({u, v, w} : Finset V), ∀ b ∈ ({u, v, w} : Finset V), a ≠ b → G.Adj a b := by
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | assumption | exact (G.adj_comm _ _).1 (by assumption)
lemma b21_path {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) {y1 y2 : V}
    (hy1 : y1 ∈ ({u, v, w} : Finset V)) (hy2 : y2 ∈ ({u, v, w} : Finset V)) (hne : y1 ≠ y2) :
    ∃ s : List V, ∃ hs : s ≠ [], s.Nodup ∧ s.IsChain G.Adj ∧ (∀ x ∈ s, x ∈ ({u, v, w} : Finset V)) ∧
      s.length = 3 ∧ s.head hs = y1 ∧ s.getLast hs = y2 := by
  have hc := b21_clq huv hvw huw h1 h2 h3
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  have hlt : ({y1, y2} : Finset V).card < ({u, v, w} : Finset V).card := by
    rw [hcard, Finset.card_pair hne]; omega
  obtain ⟨z, hz, hz'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
  refine ⟨[y1, z, y2], by simp, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [hne, Ne.symm hz'.1, hz'.2]
  · simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
    exact ⟨hc y1 hy1 z hz (Ne.symm hz'.1), hc z hz y2 hy2 hz'.2⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
lemma b21_rdeg [DecidableRel G.Adj] {l : List V} {u v w : V} (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w})
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) {y : V} (hy : y ∈ ({u, v, w} : Finset V)) :
    (((Finset.univ.filter (fun t => t ∉ l))).filter (G.Adj y)).card = 2 := by
  have hc := b21_clq huv hvw huw h1 h2 h3
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  rw [hR]
  have : ({u, v, w} : Finset V).filter (G.Adj y) = ({u, v, w} : Finset V).erase y := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨(G.ne_of_adj h).symm, hz⟩
    · rintro ⟨hne, hz⟩; exact ⟨hz, hc y hy z hz (Ne.symm hne)⟩
  rw [this, Finset.card_erase_of_mem hy, hcard]
lemma b21_mem {l : List V} {u v w : V} (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) {y : V} :
    y ∈ ({u, v, w} : Finset V) ↔ y ∉ l := by
  rw [← hR]; simp
lemma b21_getD_mem {l : List V} {d : V} {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
lemma b21_inj {l : List V} (hnd : l.Nodup) {d : V} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : l.getD i d = l.getD j d) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (hnd.getElem_inj_iff).mp h
lemma b21_Dcard (J : Finset ℕ) (hJ : J.Nonempty) (hb : ∀ j ∈ J, 0 < j) :
    J.card + 1 ≤ (J.image (· + 1) ∪ J.image (· - 1)).card := by
  have hm0 := Finset.min'_mem J hJ
  have hpos := hb _ hm0
  have hnot : J.min' hJ - 1 ∉ J.image (· + 1) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro j hj hjm
    have := Finset.min'_le J j hj
    omega
  have hsub : insert (J.min' hJ - 1) (J.image (· + 1)) ⊆ J.image (· + 1) ∪ J.image (· - 1) := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hm0, rfl⟩)
    · exact Finset.mem_union_left _ hx
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ (add_left_injective 1)] at this
  exact this
lemma b21_a [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (A : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ i < l.length ∧ ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀)) :
    (∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ l.length) ∧ 2 ≤ A.card ∧ A.card + 1 ≤ secondSmallestDegree G ∧
    secondSmallestDegree G ≤ A.card + 2 ∧
    (∀ y ∈ ({u, v, w} : Finset V), ∃ a ∈ A, G.Adj y (l.getD a x₀)) ∧
    (∀ y ∈ ({u, v, w} : Finset V), secondSmallestDegree G = A.card + 2 → ∀ a ∈ A, G.Adj y (l.getD a x₀)) ∧
    (∀ y ∈ ({u, v, w} : Finset V), (A.filter (fun i => ¬ G.Adj y (l.getD i x₀))).card ≤ 1) := by
  have hc := b21_clq huv hvw huw h1 h2 h3
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  have hJ : ∀ y ∈ ({u, v, w} : Finset V), A.filter (fun i => G.Adj y (l.getD i x₀)) =
      (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := by
    intro y hy
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, hA]
    constructor
    · rintro ⟨⟨hi, _⟩, h⟩; exact ⟨hi, h⟩
    · rintro ⟨hi, h⟩; exact ⟨⟨hi, y, hy, h⟩, h⟩
  have hdeg : ∀ y ∈ ({u, v, w} : Finset V), G.degree y = (A.filter (fun i => G.Adj y (l.getD i x₀))).card + 2 := by
    intro y hy
    rw [hJ y hy, Cadre.degree_split hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (hRl y hy), b21_rdeg hR huv hvw huw h1 h2 h3 hy]
  have hxl : ∀ y ∈ ({u, v, w} : Finset V), y ≠ x₀ := fun y hy h => hRl y hy (h ▸ hmem)
  have hS1 : ∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ l.length := by
    intro a ha
    obtain ⟨hal, z, hz, hza⟩ := (hA a).1 ha
    have := Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (hRl z hz) (j := a) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hal, hza⟩)
    omega
  have hS2 : 2 ≤ A.card := by
    obtain ⟨a, b, hab, hbl, ⟨y1, hy1, hy1a⟩, ⟨y2, hy2, hy2b⟩⟩ := Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    rw [hR] at hy1 hy2
    have ha : a ∈ A := (hA a).2 ⟨by omega, y1, hy1, hy1a⟩
    have hb' : b ∈ A := (hA b).2 ⟨hbl, y2, hy2, hy2b⟩
    exact Finset.one_lt_card.mpr ⟨a, ha, b, hb', by omega⟩
  have hS3 : A.card + 1 ≤ secondSmallestDegree G := by
    obtain ⟨a, b, hab, hbl, ⟨y1, hy1, hy1a⟩, _⟩ := Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    rw [hR] at hy1
    have hnonempty : ((Finset.range l.length).filter (fun i => G.Adj y1 (l.getD i x₀))).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hy1a⟩⟩
    have hbp := Cadre.count_Q2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt y1 (hRl y1 hy1)
      ((A.filter (fun i => ¬ G.Adj y1 (l.getD i x₀))).image (fun i => l.getD i x₀)) ∅
      (by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter] at hx
        obtain ⟨i, ⟨hiA, hni⟩, rfl⟩ := hx
        obtain ⟨hil, z, hz, hza⟩ := (hA i).1 hiA
        have hzy : z ≠ y1 := fun h => hni (h ▸ hza)
        exact ⟨b21_getD_mem hil, hni, z, hRl z hz, hc y1 hy1 z hz (Ne.symm hzy), hza⟩)
      (by simp)
    have hDc := b21_Dcard _ hnonempty (fun j hj => (Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt (hRl y1 hy1) hj).1)
    have himg : ((A.filter (fun i => ¬ G.Adj y1 (l.getD i x₀))).image (fun i => l.getD i x₀)).card =
        (A.filter (fun i => ¬ G.Adj y1 (l.getD i x₀))).card := by
      apply Finset.card_image_of_injOn
      intro i hi j hj hij
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hj
      exact b21_inj hnd ((hA i).1 hi.1).1 ((hA j).1 hj.1).1 hij
    have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun i => G.Adj y1 (l.getD i x₀))
    rw [hJ y1 hy1] at hsplit
    simp only [Finset.card_empty] at hbp
    omega
  have hS4 : secondSmallestDegree G ≤ A.card + 2 := by
    have := hx0 u (hxl u (by simp))
    rw [hdeg u (by simp)] at this
    have := Finset.card_filter_le A (fun i => G.Adj u (l.getD i x₀))
    omega
  have hS5 : ∀ y ∈ ({u, v, w} : Finset V), ∃ a ∈ A, G.Adj y (l.getD a x₀) := by
    intro y hy
    have h := hx0 y (hxl y hy)
    rw [hdeg y hy] at h
    have : 0 < (A.filter (fun i => G.Adj y (l.getD i x₀))).card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp this
    rw [Finset.mem_filter] at ha
    exact ⟨a, ha.1, ha.2⟩
  have hS6 : ∀ y ∈ ({u, v, w} : Finset V), secondSmallestDegree G = A.card + 2 → ∀ a ∈ A, G.Adj y (l.getD a x₀) := by
    intro y hy hσ a ha
    have h := hx0 y (hxl y hy)
    rw [hdeg y hy] at h
    have := Finset.eq_of_subset_of_card_le (Finset.filter_subset (fun i => G.Adj y (l.getD i x₀)) A) (by omega)
    rw [← this] at ha
    exact (Finset.mem_filter.mp ha).2
  have hS7 : ∀ y ∈ ({u, v, w} : Finset V), (A.filter (fun i => ¬ G.Adj y (l.getD i x₀))).card ≤ 1 := by
    intro y hy
    have h := hx0 y (hxl y hy)
    rw [hdeg y hy] at h
    have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun i => G.Adj y (l.getD i x₀))
    omega
  exact ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7⟩
lemma b21_other {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) (y : V) :
    ∃ y' ∈ ({u, v, w} : Finset V), y' ≠ y := by
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  exact Finset.exists_mem_ne (by omega) y
lemma b21_c [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (A : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ i < l.length ∧ ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀))
    (i₀ : ℕ) (hi₀ : i₀ < l.length ∧ l.getD i₀ x₀ = x₀)
    (hS2 : 2 ≤ A.card)
    (hS7 : ∀ y ∈ ({u, v, w} : Finset V), (A.filter (fun i => ¬ G.Adj y (l.getD i x₀))).card ≤ 1) :
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD a x₀) ∧ G.Adj y2 (l.getD b x₀)) ∧
    (∀ a ∈ A, 3 ≤ a ∨ i₀ < a) ∧ (∀ a ∈ A, a + 4 ≤ l.length ∨ a < i₀) ∧
    (∀ a ∈ A, ∀ b ∈ A, a < b → a + 2 ≤ b ∧ (a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b))) := by
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  have huniq : ∀ i, i < l.length → l.getD i x₀ = x₀ → i = i₀ :=
    fun i hi h => b21_inj hnd hi hi₀.1 (h.trans hi₀.2.symm)
  have hcross : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD a x₀) ∧ G.Adj y2 (l.getD b x₀) := by
    intro a ha b hb hab
    by_contra hno
    push Not at hno
    obtain ⟨_, y1, hy1, hy1a⟩ := (hA a).1 ha
    obtain ⟨_, y2, hy2, hy2b⟩ := (hA b).1 hb
    have hyy : y1 = y2 := by
      by_contra hne'
      exact hno y1 hy1 y2 hy2 hne' hy1a hy2b
    subst hyy
    obtain ⟨v', hv', hvy⟩ := b21_other huv hvw huw y1
    have hva : ¬ G.Adj v' (l.getD a x₀) := fun h => hno v' hv' y1 hy1 hvy h hy2b
    have hvb : ¬ G.Adj v' (l.getD b x₀) := fun h => hno y1 hy1 v' hv' (Ne.symm hvy) hy1a h
    have hsub : ({a, b} : Finset ℕ) ⊆ A.filter (fun i => ¬ G.Adj v' (l.getD i x₀)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨ha, hva⟩
      · exact Finset.mem_filter.mpr ⟨hb, hvb⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hab] at this
    have := hS7 v' hv'
    omega
  have hL : ∀ a ∈ A, 3 ≤ a ∨ i₀ < a := by
    intro a ha
    by_contra hcon
    push Not at hcon
    obtain ⟨hal, z, hz, hza⟩ := (hA a).1 ha
    obtain ⟨y', hy', hyz⟩ := b21_other huv hvw huw z
    obtain ⟨s, hs, snd, sch, hsR, hlen, -, hlast'⟩ := b21_path huv hvw huw h1 h2 h3 hy' hz hyz
    refine Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) a hal ?_ ?_ (by omega)
    · rw [hlast']; exact hza
    · intro i hi heq
      have := huniq i (by omega) heq
      omega
  have hRt : ∀ a ∈ A, a + 4 ≤ l.length ∨ a < i₀ := by
    intro a ha
    by_contra hcon
    push Not at hcon
    obtain ⟨hal, z, hz, hza⟩ := (hA a).1 ha
    obtain ⟨y', hy', hyz⟩ := b21_other huv hvw huw z
    obtain ⟨s, hs, snd, sch, hsR, hlen, hhead, -⟩ := b21_path huv hvw huw h1 h2 h3 hz hy' (Ne.symm hyz)
    refine Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) a hal ?_ ?_ (by omega)
    · rw [hhead]; exact (G.adj_comm _ _).1 hza
    · intro i hi hil heq
      have := huniq i hil heq
      omega
  have hM : ∀ a ∈ A, ∀ b ∈ A, a < b → a + 2 ≤ b ∧ (a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b)) := by
    intro a ha b hbA hab
    have hdis : a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hal, _⟩ := (hA a).1 ha
      obtain ⟨hbl, _⟩ := (hA b).1 hbA
      obtain ⟨y1, hy1, y2, hy2, hy12, hy1a, hy2b⟩ := hcross a ha b hbA (by omega)
      obtain ⟨s, hs, snd, sch, hsR, hlen, hhead, hlast'⟩ := b21_path huv hvw huw h1 h2 h3 hy1 hy2 hy12
      refine Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) a b hab hbl ?_ ?_ ?_ (by omega)
      · rw [hhead]; exact (G.adj_comm _ _).1 hy1a
      · rw [hlast']; exact hy2b
      · intro i hi1 hi2 heq
        have := huniq i (by omega) heq
        have := hcon.2
        omega
    refine ⟨?_, hdis⟩
    omega
  exact ⟨hcross, hL, hRt, hM⟩
lemma b21_pack (A : Finset ℕ) {m i₀ : ℕ} (hS2 : 2 ≤ A.card)
    (hS1 : ∀ a ∈ A, 1 ≤ a ∧ a + 2 ≤ m) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ m)
    (hL : ∀ a ∈ A, 3 ≤ a ∨ i₀ < a) (hRt : ∀ a ∈ A, a + 4 ≤ m ∨ a < i₀)
    (hM : ∀ a ∈ A, ∀ b ∈ A, a < b → a + 2 ≤ b ∧ (a + 4 ≤ b ∨ (a < i₀ ∧ i₀ < b))) :
    4 * A.card + 1 ≤ m := by
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have := pack A ∅ m 3 i₀ (by norm_num) hAne (Finset.empty_subset _) hS1 hi
    (by have := hL _ (Finset.min'_mem A hAne); omega)
    (by have := hRt _ (Finset.max'_mem A hAne); omega)
    (by
      intro a ha b hb hab _
      have := hM a ha b hb hab
      refine ⟨this.1, fun _ => ?_⟩
      omega)
  simpa using this
set_option maxHeartbeats 2000000 in
lemma b21_core [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (P Q i₀ : ℕ) (hs : (secondSmallestDegree G = 3 ∧ l.length = 9) ∨ (secondSmallestDegree G = 4 ∧ l.length = 10) ∨
      (secondSmallestDegree G = 4 ∧ l.length = 11))
    (h1P : 1 ≤ P) (hQ : Q + 2 ≤ l.length) (hPQ : P < Q) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length)
    (hLP : 3 ≤ P ∨ i₀ < P) (hLQ : 3 ≤ Q ∨ i₀ < Q) (hRP : P + 4 ≤ l.length ∨ P < i₀)
    (hRQ : Q + 4 ≤ l.length ∨ Q < i₀) (hM : P + 2 ≤ Q ∧ (P + 4 ≤ Q ∨ (P < i₀ ∧ i₀ < Q)))
    (hi₀ : l.getD i₀ x₀ = x₀)
    (hAny : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD P x₀) ∨ G.Adj y (l.getD Q x₀))
    (hAll : 4 ≤ secondSmallestDegree G → ∀ y ∈ ({u, v, w} : Finset V),
      G.Adj y (l.getD P x₀) ∧ G.Adj y (l.getD Q x₀))
    (hcr : ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD P x₀) ∧ G.Adj y2 (l.getD Q x₀))
    (hcore : i₀ ≤ P + 1 ∨ i₀ = Q ∨ (i₀ = P + 2 ∧ Q = P + 4)) : False := by
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  have hcard : ({u, v, w} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  have hB17 : secondSmallestDegree G ≤ 4 → Q = P + 2 → i₀ = P + 1 → False := by
    intro hs4 hQ2 hi
    subst hQ2 hi
    obtain ⟨y1, hy1, y2, hy2, hy12, hy1a, hy2b⟩ := hcr
    obtain ⟨s, hs, snd, sch, hsR, hlen, hhead, hlast'⟩ := b21_path huv hvw huw h1 h2 h3 hy1 hy2 hy12
    have := Cadre.hole_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt ({u, v, w} : Finset V) hRl P h1P (by omega) hi₀ hAny s hs snd sch
      (fun x hx => hRl x (hsR x hx)) (by rw [hhead]; exact (G.adj_comm _ _).1 hy1a)
      (by rw [hlast']; exact hy2b)
    omega
  have hB18 : secondSmallestDegree G = 4 → (i₀ = P ∨ i₀ = Q) → False := by
    intro hs4 hi
    have := Cadre.x0_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt ({u, v, w} : Finset V) hRl i₀ (by omega) (by omega) hi₀
      (by
        intro y hy
        have := hAll (by omega) y hy
        rcases hi with rfl | rfl
        · rw [← hi₀]; exact this.1
        · rw [← hi₀]; exact this.2)
    omega
  have hB19 : secondSmallestDegree G = 4 → i₀ = P + 1 → P + 3 ≤ Q → Q ≤ P + 4 → False := by
    intro hs4 hi hq1 hq2
    subst hi
    obtain ⟨s, hs, snd, sch, hsR, hlen, -, -⟩ := b21_path huv hvw huw h1 h2 h3
      (y1 := u) (y2 := v) (by simp) (by simp) huv
    exact Cadre.walk_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt s hs snd sch (fun x hx => hRl x (hsR x hx)) P Q h1P hq1 (by omega) hi₀
      (fun y hy => (hAll (by omega) y (hsR y hy)).1) (fun y hy => (hAll (by omega) y (hsR y hy)).2)
      (by omega) (by omega)
  rcases hcore with hc | hc | hc
  · rcases lt_or_ge i₀ P with hlt' | hge
    · rcases hs with ⟨hσ, hm⟩ | ⟨hσ, hm⟩ | ⟨hσ, hm⟩
      · omega
      · have e : P = 2 ∧ Q = 6 ∧ i₀ = 1 := by omega
        obtain ⟨rfl, rfl, rfl⟩ := e
        exact Cadre.C1 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀
      · have e : (P = 2 ∧ Q = 6 ∧ i₀ = 1) ∨ (P = 2 ∧ Q = 7 ∧ i₀ = 1) ∨ (P = 3 ∧ Q = 7 ∧ (i₀ = 1 ∨ i₀ = 2)) := by
          omega
        rcases e with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hi12⟩
        · exact Cadre.C3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀
        · exact Cadre.C4 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀
        · exact Cadre.C5 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy)
            (by rcases hi12 with rfl | rfl; exacts [Or.inl hi₀, Or.inr hi₀])
    · have hσ4 : secondSmallestDegree G ≤ 4 := by omega
      rcases (by omega : i₀ = P ∨ (i₀ = P + 1 ∧ Q = P + 2) ∨ (i₀ = P + 1 ∧ P + 3 ≤ Q)) with he | ⟨he, hq⟩ | ⟨he, hq⟩
      · exact hB18 (by omega) (Or.inl he)
      · exact hB17 hσ4 hq he
      · exact hB19 (by omega) he hq (by omega)
  · exact hB18 (by omega) (Or.inr hc)
  · obtain ⟨hi2, hq⟩ := hc
    have hσ : secondSmallestDegree G = 4 := by omega
    have hm : l.length = 11 := by omega
    have e : P = 3 ∧ Q = 7 ∧ i₀ = 5 := by omega
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact Cadre.C9 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ hm u v w hR huv hvw huw h1 h2 h3 (fun y hy => hAll (by omega) y hy) hi₀
set_option maxHeartbeats 2000000 in
lemma b21_fin2 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (P Q i₀ : ℕ) (hs : (secondSmallestDegree G = 3 ∧ l.length = 9) ∨ (secondSmallestDegree G = 4 ∧ l.length = 10) ∨
      (secondSmallestDegree G = 4 ∧ l.length = 11))
    (h1P : 1 ≤ P) (hQ : Q + 2 ≤ l.length) (hPQ : P < Q) (hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length)
    (hLP : 3 ≤ P ∨ i₀ < P) (hLQ : 3 ≤ Q ∨ i₀ < Q) (hRP : P + 4 ≤ l.length ∨ P < i₀)
    (hRQ : Q + 4 ≤ l.length ∨ Q < i₀) (hM : P + 2 ≤ Q ∧ (P + 4 ≤ Q ∨ (P < i₀ ∧ i₀ < Q)))
    (hi₀ : l.getD i₀ x₀ = x₀)
    (hAny : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD P x₀) ∨ G.Adj y (l.getD Q x₀))
    (hAll : 4 ≤ secondSmallestDegree G → ∀ y ∈ ({u, v, w} : Finset V),
      G.Adj y (l.getD P x₀) ∧ G.Adj y (l.getD Q x₀))
    (hcr : ∃ y1 ∈ ({u, v, w} : Finset V), ∃ y2 ∈ ({u, v, w} : Finset V),
      y1 ≠ y2 ∧ G.Adj y1 (l.getD P x₀) ∧ G.Adj y2 (l.getD Q x₀)) : False := by
  by_cases hcore : i₀ ≤ P + 1 ∨ i₀ = Q ∨ (i₀ = P + 2 ∧ Q = P + 4)
  · exact b21_core hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 P Q i₀ hs h1P hQ hPQ hi hLP hLQ hRP hRQ hM hi₀ hAny hAll hcr hcore
  · obtain ⟨hne', hnd', hch', hmem', hhd', hlast', hmax', hlt'⟩ := Cadre.reverse hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hR' : (Finset.univ.filter (fun t => t ∉ l.reverse)) = {u, v, w} := by
      simpa [List.mem_reverse] using hR
    have hrev : ∀ j, j < l.length → l.reverse.getD (l.length - 1 - j) x₀ = l.getD j x₀ := by
      intro j hj
      rw [Cadre.getD_reverse l x₀ (by omega)]
      have : l.length - 1 - (l.length - 1 - j) = j := by omega
      rw [this]
    refine b21_core (l := l.reverse) hconn hb hH hmin hx0 hδ hne' hnd' hch' hmem' hhd' hlast' hmax' hlt'
      u v w hR' huv hvw huw h1 h2 h3 (l.length - 1 - Q) (l.length - 1 - P) (l.length - 1 - i₀)
      (by rw [List.length_reverse]; exact hs)
      (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega) (by (try simp only [List.length_reverse]); omega)
      (by rw [hrev i₀ (by omega)]; exact hi₀)
      (fun y hy => by rw [hrev Q (by omega), hrev P (by omega)]; exact (hAny y hy).symm)
      (fun h y hy => by
        rw [hrev Q (by omega), hrev P (by omega)]
        exact ⟨(hAll h y hy).2, (hAll h y hy).1⟩)
      (by
        obtain ⟨y1, hy1, y2, hy2, hne2, ha, hb2⟩ := hcr
        exact ⟨y2, hy2, y1, hy1, Ne.symm hne2, by rw [hrev Q (by omega)]; exact hb2,
          by rw [hrev P (by omega)]; exact ha⟩)
      (by (try simp only [List.length_reverse]); omega)
lemma b21_fin3r [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V} (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V) (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w) (hσ : secondSmallestDegree G = 5) (hm : l.length = 13)
    (hA : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD 3 x₀) ∧ G.Adj y (l.getD 5 x₀) ∧ G.Adj y (l.getD 9 x₀))
    (hx : l.getD 4 x₀ = x₀) : False := by
  obtain ⟨hne', hnd', hch', hmem', hhd', hlast', hmax', hlt'⟩ := Cadre.reverse hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  have hR' : (Finset.univ.filter (fun t => t ∉ l.reverse)) = {u, v, w} := by
    simpa [List.mem_reverse] using hR
  have hrev : ∀ j, j < l.length → l.reverse.getD (l.length - 1 - j) x₀ = l.getD j x₀ := by
    intro j hj
    rw [Cadre.getD_reverse l x₀ (by omega)]
    have : l.length - 1 - (l.length - 1 - j) = j := by omega
    rw [this]
  have e3 : l.reverse.getD 3 x₀ = l.getD 9 x₀ := by
    have := hrev 9 (by omega); rwa [show l.length - 1 - 9 = 3 by omega] at this
  have e7 : l.reverse.getD 7 x₀ = l.getD 5 x₀ := by
    have := hrev 5 (by omega); rwa [show l.length - 1 - 5 = 7 by omega] at this
  have e9 : l.reverse.getD 9 x₀ = l.getD 3 x₀ := by
    have := hrev 3 (by omega); rwa [show l.length - 1 - 3 = 9 by omega] at this
  have e8 : l.reverse.getD 8 x₀ = l.getD 4 x₀ := by
    have := hrev 4 (by omega); rwa [show l.length - 1 - 4 = 8 by omega] at this
  exact Cadre.C10 (l := l.reverse) hconn hb hH hmin hx0 hδ hne' hnd' hch' hmem' hhd' hlast' hmax' hlt'
    hσ (by rw [List.length_reverse]; exact hm) u v w hR' huv hvw huw h1 h2 h3
    (fun y hy => by
      rw [e3, e7, e9]
      exact ⟨(hA y hy).2.2, (hA y hy).2.1, (hA y hy).1⟩)
    (by rw [e8]; exact hx)
set_option maxHeartbeats 4000000 in
lemma Cadre.K3 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (u v w : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {u, v, w}) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : G.Adj u v) (h2 : G.Adj v w) (h3 : G.Adj u w)
    (hm : l.length = 2 * secondSmallestDegree G + 2 ∨ l.length = 2 * secondSmallestDegree G + 3) :
    False := by
  have hRl : ∀ y ∈ ({u, v, w} : Finset V), y ∉ l := fun y hy => (b21_mem hR).1 hy
  obtain ⟨i₀, hi₀l, hi₀⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ := by
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hmem
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact he⟩
  have hi₀b : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length := by
    have hpos := List.length_pos_of_ne_nil hne
    have h0 : l.head hne = l.getD 0 x₀ := by
      cases l with
      | nil => exact absurd rfl hne
      | cons a t => simp
    have hL' : l.getLast hne = l.getD (l.length - 1) x₀ := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    constructor
    · by_contra h
      have : i₀ = 0 := by omega
      subst this
      exact hhd (h0.trans hi₀)
    · by_contra h
      have : i₀ = l.length - 1 := by omega
      subst this
      exact hlast (hL'.trans hi₀)
  obtain ⟨A, hAdef⟩ : ∃ A : Finset ℕ, A = (Finset.range l.length).filter
      (fun i => ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀)) := ⟨_, rfl⟩
  have hA : ∀ i, i ∈ A ↔ i < l.length ∧ ∃ z ∈ ({u, v, w} : Finset V), G.Adj z (l.getD i x₀) := by
    intro i; rw [hAdef, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7⟩ := b21_a hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 A hA
  obtain ⟨hcross, hL, hRt, hM⟩ := b21_c hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 A hA i₀ ⟨hi₀l, hi₀⟩ hS2 hS7
  have hpk := b21_pack A hS2 hS1 hi₀b hL hRt hM
  have hr : A.card = 2 ∨ A.card = 3 := by omega
  rcases hr with hr | hr
  · obtain ⟨a, b, hab, hAab⟩ := Finset.card_eq_two.mp hr
    have key : ∀ P Q, P < Q → A = {P, Q} → False := by
      intro P Q hPQ hAPQ
      have hPA : P ∈ A := by rw [hAPQ]; simp
      have hQA : Q ∈ A := by rw [hAPQ]; simp
      have h1P := hS1 P hPA
      have h1Q := hS1 Q hQA
      have hLP := hL P hPA
      have hLQ := hL Q hQA
      have hRP := hRt P hPA
      have hRQ := hRt Q hQA
      have hMPQ := hM P hPA Q hQA hPQ
      have hAny : ∀ y ∈ ({u, v, w} : Finset V), G.Adj y (l.getD P x₀) ∨ G.Adj y (l.getD Q x₀) := by
        intro y hy
        obtain ⟨a', ha', hya⟩ := hS5 y hy
        rw [hAPQ] at ha'
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with rfl | rfl
        · exact Or.inl hya
        · exact Or.inr hya
      have hAll : 4 ≤ secondSmallestDegree G → ∀ y ∈ ({u, v, w} : Finset V),
          G.Adj y (l.getD P x₀) ∧ G.Adj y (l.getD Q x₀) :=
        fun h y hy => ⟨hS6 y hy (by omega) P hPA, hS6 y hy (by omega) Q hQA⟩
      have hcr := hcross P hPA Q hQA (by omega)
      have hs34 : (secondSmallestDegree G = 3 ∧ l.length = 9) ∨ (secondSmallestDegree G = 4 ∧ l.length = 10) ∨
          (secondSmallestDegree G = 4 ∧ l.length = 11) := by omega
      exact b21_fin2 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 P Q i₀ hs34 (by omega) (by omega) hPQ hi₀b hLP hLQ hRP hRQ hMPQ hi₀ hAny hAll hcr
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h hAab
    · exact key b a h (by rw [hAab]; exact Finset.pair_comm a b)
  · obtain ⟨a, b, c, hab, hac, hbc, hAabc⟩ := Finset.card_eq_three.mp hr
    have hAe : ∀ x, x ∈ A ↔ x = a ∨ x = b ∨ x = c := by
      intro x; rw [hAabc]; simp
    have haA : a ∈ A := (hAe a).2 (Or.inl rfl)
    have hbA : b ∈ A := (hAe b).2 (Or.inr (Or.inl rfl))
    have hcA : c ∈ A := (hAe c).2 (Or.inr (Or.inr rfl))
    have hσ5 : secondSmallestDegree G = 5 := by omega
    have hm13 : l.length = 13 := by omega
    have hAll3 : ∀ y ∈ ({u, v, w} : Finset V), ∀ x ∈ A, G.Adj y (l.getD x x₀) :=
      fun y hy x hx => hS6 y hy (by omega) x hx
    have e1 := hS1 a haA
    have e2 := hS1 b hbA
    have e3 := hS1 c hcA
    have hLa := hL a haA
    have hLb := hL b hbA
    have hLc := hL c hcA
    have hRa := hRt a haA
    have hRb := hRt b hbA
    have hRc := hRt c hcA
    have mab := hM a haA b hbA
    have mba := hM b hbA a haA
    have mac := hM a haA c hcA
    have mca := hM c hcA a haA
    have mbc := hM b hbA c hcA
    have mcb := hM c hcA b hbA
    have hvals : (i₀ = 8 ∧ (a = 3 ∨ a = 7 ∨ a = 9) ∧ (b = 3 ∨ b = 7 ∨ b = 9) ∧ (c = 3 ∨ c = 7 ∨ c = 9)) ∨
        (i₀ = 4 ∧ (a = 3 ∨ a = 5 ∨ a = 9) ∧ (b = 3 ∨ b = 5 ∨ b = 9) ∧ (c = 3 ∨ c = 5 ∨ c = 9)) := by
      omega
    rcases hvals with ⟨hi8, -, -, -⟩ | ⟨hi4, -, -, -⟩
    · have m3 : 3 ∈ A := by rw [hAe]; omega
      have m7 : 7 ∈ A := by rw [hAe]; omega
      have m9 : 9 ∈ A := by rw [hAe]; omega
      exact Cadre.C10 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hσ5 hm13 u v w hR huv hvw huw h1 h2 h3
        (fun y hy => ⟨hAll3 y hy 3 m3, hAll3 y hy 7 m7, hAll3 y hy 9 m9⟩) (by subst hi8; exact hi₀)
    · have m3 : 3 ∈ A := by rw [hAe]; omega
      have m5 : 5 ∈ A := by rw [hAe]; omega
      have m9 : 9 ∈ A := by rw [hAe]; omega
      exact b21_fin3r hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw h1 h2 h3 hσ5 hm13
        (fun y hy => ⟨hAll3 y hy 3 m3, hAll3 y hy 5 m5, hAll3 y hy 9 m9⟩) (by subst hi4; exact hi₀)
lemma b23_getD_inj {l : List V} (hnd : l.Nodup) (x₀ : V) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : l.getD i x₀ = l.getD j x₀) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff hnd).mp h
lemma b23_gamma (P : ℕ → Prop) (m : ℕ) (Jz Ja : Finset ℕ) (hJ : Jz.Nonempty)
    (hbd : ∀ j ∈ Jz, 0 < j ∧ j + 1 < m)
    (hpr1 : ∀ j ∈ Jz, j ≠ Jz.max' hJ → j + 2 ∈ Jz)
    (hpr2 : ∀ j ∈ Jz, j ≠ Jz.min' hJ → 2 ≤ j ∧ j - 2 ∈ Jz)
    (hsub : Ja ⊆ Jz) (hβ : ∀ j, j ∈ Jz → j + 2 ∈ Jz → (j ∈ Ja ∨ j + 2 ∈ Ja) → P (j + 1))
    (hinj : ∀ i i', i < m → i' < m → P i → P i' → i = i')
    (h5a : ∀ j ∈ Jz, j + 1 ∉ Jz) (hca : 2 ≤ Ja.card) (hcz : 3 ≤ Jz.card) : False := by
  have key : ∀ j ∈ Ja, j = Jz.max' hJ ∨ j = Jz.min' hJ := by
    intro j hj
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hjz := hsub hj
    have e1 := hpr1 j hjz h1
    obtain ⟨h2a, e2⟩ := hpr2 j hjz h2
    have p1 : P (j + 1) := hβ j hjz e1 (Or.inl hj)
    have e3 : j - 2 + 2 = j := Nat.sub_add_cancel h2a
    have p2 : P (j - 2 + 1) := hβ (j - 2) e2 (by rw [e3]; exact hjz)
      (Or.inr (by rw [e3]; exact hj))
    have hb1 := (hbd j hjz).2
    have := hinj _ _ (by omega) (by omega) p1 p2
    omega
  have hsub2 : Ja ⊆ {Jz.max' hJ, Jz.min' hJ} := by
    intro j hj
    rcases key j hj with h | h <;> simp [h]
  have hc2 := Finset.card_le_card hsub2
  have hne : Jz.max' hJ ≠ Jz.min' hJ := by
    intro h
    rw [h] at hc2
    simp at hc2
    omega
  have hEq : Ja = {Jz.max' hJ, Jz.min' hJ} :=
    Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hne]; omega)
  have hMa : Jz.max' hJ ∈ Ja := by rw [hEq]; simp
  have hma : Jz.min' hJ ∈ Ja := by rw [hEq]; simp
  have hmz : Jz.min' hJ ∈ Jz := Finset.min'_mem _ _
  have hMz : Jz.max' hJ ∈ Jz := Finset.max'_mem _ _
  have hlt : Jz.min' hJ < Jz.max' hJ :=
    lt_of_le_of_ne (Finset.min'_le _ _ hMz) (Ne.symm hne)
  have e1 := hpr1 _ hmz (ne_of_lt hlt)
  obtain ⟨h2a, e2⟩ := hpr2 _ hMz hne
  have p1 : P (Jz.min' hJ + 1) := hβ _ hmz e1 (Or.inl hma)
  have e3 : Jz.max' hJ - 2 + 2 = Jz.max' hJ := Nat.sub_add_cancel h2a
  have p2 : P (Jz.max' hJ - 2 + 1) := hβ _ e2 (by rw [e3]; exact hMz)
    (Or.inr (by rw [e3]; exact hMa))
  have hb1 := (hbd _ hMz).2
  have hb2 := (hbd _ hmz).2
  have h22 := hinj _ _ (by omega) (by omega) p1 p2
  have hM : Jz.max' hJ = Jz.min' hJ + 2 := by omega
  have hsub3 : Jz ⊆ {Jz.min' hJ, Jz.min' hJ + 2} := by
    intro j hj
    have h1 := Finset.min'_le _ _ hj
    have h2 := Finset.le_max' _ _ hj
    have h3 : j ≠ Jz.min' hJ + 1 := by
      intro h; exact h5a _ hmz (h ▸ hj)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have := Finset.card_le_card hsub3
  have h4 := Finset.card_le_two (a := Jz.min' hJ) (b := Jz.min' hJ + 2)
  omega
lemma Cadre.R4_nonclique [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (z z' a b : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {z, z', a, b}) (hd : z ≠ z' ∧ z ≠ a ∧ z ≠ b ∧ z' ≠ a ∧ z' ≠ b ∧ a ≠ b)
    (hzz : ¬ G.Adj z z') (h1 : G.Adj z a) (h2 : G.Adj z b) (h3 : G.Adj z' a) (h4 : G.Adj z' b)
    (hm : l.length = 2 * secondSmallestDegree G + 2) : False := by
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  have hmemR : ∀ t, t ∉ l ↔ t ∈ ({z, z', a, b} : Finset V) := by
    intro t; rw [← hR]; simp
  have hz : z ∉ l := (hmemR z).mpr (by simp)
  have hz' : z' ∉ l := (hmemR z').mpr (by simp)
  have ha : a ∉ l := (hmemR a).mpr (by simp)
  have hbl : b ∉ l := (hmemR b).mpr (by simp)
  have hirr : ∀ t : V, ¬ G.Adj t t := fun t => G.loopless.irrefl t
  have hm0 : 0 < l.length := List.length_pos_of_ne_nil hne
  have hσ4 : 4 ≤ secondSmallestDegree G := by
    by_contra hlt4
    push Not at hlt4
    have hcardR : (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by
      rw [hR]; simp [Finset.card_insert_of_notMem, d1, d2, d3, d4, d5, d6]
    have hham : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∃ s : List V, s.Nodup ∧
        s.IsChain G.Adj ∧ s.toFinset = (Finset.univ.filter (fun t => t ∉ l)) ∧
        s.getLast? = some y := by
      intro y hy
      rw [hR] at hy ⊢
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h | h | h <;> rw [h]
      · refine ⟨[a, z', b, z], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, z, b, z'], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp; tauto
        · simp
      · refine ⟨[z, b, z', a], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp; tauto
        · simp
      · refine ⟨[z, a, z', b], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm]
        · ext t; simp <;> tauto
        · simp
    have hd2 : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∀ y' ∈ (Finset.univ.filter (fun t => t ∉ l)),
        y ≠ y' → G.Adj y y' ∨ ∃ w ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y w ∧ G.Adj w y' := by
      intro y hy y' hy' hne'
      rw [hR] at hy hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
      have hza : z ∈ (Finset.univ.filter (fun t => t ∉ l)) := by rw [hR]; simp
      have haa : a ∈ (Finset.univ.filter (fun t => t ∉ l)) := by rw [hR]; simp
      rcases hy with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;>
        rw [h, h'] at hne' <;> rw [h, h'] <;>
        first
        | exact absurd rfl hne'
        | exact Or.inl h1 | exact Or.inl h1.symm | exact Or.inl h2 | exact Or.inl h2.symm
        | exact Or.inl h3 | exact Or.inl h3.symm | exact Or.inl h4 | exact Or.inl h4.symm
        | exact Or.inr ⟨a, haa, h1, h3.symm⟩ | exact Or.inr ⟨a, haa, h3, h1.symm⟩
        | exact Or.inr ⟨z, hza, h1.symm, h2⟩ | exact Or.inr ⟨z, hza, h2.symm, h1⟩
    have := Cadre.small_sigma hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hham hd2
    omega
  have hdz := Cadre.degree_split (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
    hhd hlast hmax hlt hz
  have hda := Cadre.degree_split (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
    hhd hlast hmax hlt ha
  have hx0ne : ∀ y, y ∉ l → y ≠ x₀ := fun y hy h => hy (h ▸ hmem)
  have hσz := hx0 z (hx0ne z hz)
  have hσa := hx0 a (hx0ne a ha)
  have hNz : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj z)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card (t := {a, b}) ?_) Finset.card_le_two
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have := (hmemR t).mp ht1
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with h | h | h | h
    · subst h; exact absurd ht2 (hirr _)
    · subst h; exact absurd ht2 hzz
    · exact Or.inl h
    · exact Or.inr h
  have hNa : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj a)).card ≤ 3 := by
    refine le_trans (Finset.card_le_card (t := {z, z', b}) ?_) Finset.card_le_three
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have := (hmemR t).mp ht1
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst h; exact absurd ht2 (hirr _)
    · exact Or.inr (Or.inr h)
  set Jz := (Finset.range l.length).filter (fun i => G.Adj z (l.getD i x₀)) with hJz
  set Ja := (Finset.range l.length).filter (fun i => G.Adj a (l.getD i x₀)) with hJa
  have hbdz : ∀ j ∈ Jz, 0 < j ∧ j + 1 < l.length := fun j hj =>
    Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hz hj
  have hbda : ∀ j ∈ Ja, 0 < j ∧ j + 1 < l.length := fun j hj =>
    Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt ha hj
  set Bp : Finset V := l.toFinset.filter (fun x => ¬ G.Adj z x ∧ G.Adj a x) with hBp
  have hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj z w ∧ ∃ r, r ∉ l ∧ G.Adj z r ∧ G.Adj r w := by
    intro w hw
    simp only [hBp, Finset.mem_filter, List.mem_toFinset] at hw
    exact ⟨hw.1, hw.2.1, a, ha, h1, hw.2.2⟩
  have hK : ∀ w ∈ ({z'} : Finset V), w ∉ l ∧ w ≠ z ∧ ¬ G.Adj z w ∧ ∃ r, G.Adj z r ∧ G.Adj r w := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hz', Ne.symm d1, hzz, a, h1, h3.symm⟩
  have hB9 := Cadre.count_Q2 (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
    hhd hlast hmax hlt z hz Bp {z'} hB hK
  rw [← hJz] at hB9
  have hring := ring_card Jz (fun h0 => by have := (hbdz 0 h0).1; omega)
  have hJne : Jz.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h] at hdz; simp at hdz; omega
  have hTl := T_lt Jz hJne
  rw [Finset.card_singleton] at hB9
  have hBp0 : Bp.card = 0 := by omega
  have htz : (Jz.filter (fun j => j + 2 ∈ Jz)).card + 1 = Jz.card := by omega
  have hczσ : Jz.card + 2 = secondSmallestDegree G := by omega
  have hsub : Ja ⊆ Jz := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi)
    have hil := Finset.mem_range.mp hi'.1
    by_contra hnz
    have hmemB : l.getD i x₀ ∈ Bp := by
      simp only [hBp, Finset.mem_filter, List.mem_toFinset]
      refine ⟨?_, ?_, hi'.2⟩
      · rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem _
      · intro hadj; exact hnz (Finset.mem_filter.mpr ⟨hi'.1, hadj⟩)
    rw [Finset.card_eq_zero] at hBp0
    rw [hBp0] at hmemB
    simp at hmemB
  obtain ⟨hpr1, hpr2⟩ := prog Jz hJne htz
  have hβ : ∀ j, j ∈ Jz → j + 2 ∈ Jz → (j ∈ Ja ∨ j + 2 ∈ Ja) → l.getD (j + 1) x₀ = x₀ := by
    intro j hj hj2 hja
    by_contra hxj
    have hjb := hbdz j hj
    have hj2b := hbdz (j + 2) hj2
    have hzj : G.Adj z (l.getD j x₀) := (Finset.mem_filter.mp hj).2
    have hzj2 : G.Adj z (l.getD (j + 2) x₀) := (Finset.mem_filter.mp hj2).2
    have hxs : ∀ i, j < i → i < j + 2 → l.getD i x₀ ≠ x₀ := by
      intro i hi1 hi2
      have : i = j + 1 := by omega
      rw [this]; exact hxj
    rcases hja with h | h
    · have haj : G.Adj a (l.getD j x₀) := (Finset.mem_filter.mp h).2
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [a, z]
        (by simp) (by simp [d2, Ne.symm d2]) (by simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm])
        (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
        j (j + 2) (by omega) (by omega) haj.symm hzj2 hxs (by simp)
    · have haj : G.Adj a (l.getD (j + 2) x₀) := (Finset.mem_filter.mp h).2
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z, a]
        (by simp) (by simp [d2, Ne.symm d2]) (by simp [List.isChain_cons_cons, h1, h1.symm, h2, h2.symm, h3, h3.symm, h4, h4.symm])
        (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
        j (j + 2) (by omega) (by omega) hzj.symm haj hxs (by simp)
  have h5a : ∀ j ∈ Jz, j + 1 ∉ Jz := by
    intro j hj hj1
    have hzj : G.Adj z (l.getD j x₀) := (Finset.mem_filter.mp hj).2
    have hzj1 : G.Adj z (l.getD (j + 1) x₀) := (Finset.mem_filter.mp hj1).2
    have hjb := hbdz (j + 1) hj1
    exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z]
      (by simp) (by simp) (by simp) (by intro v hv; simp at hv; subst hv; exact hz)
      j (j + 1) (by omega) (by omega) hzj.symm hzj1 (by intro i h1 h2; omega) (by simp)
  have hinj : ∀ i i', i < l.length → i' < l.length → l.getD i x₀ = x₀ → l.getD i' x₀ = x₀ →
      i = i' := fun i i' hi hi' e e' => b23_getD_inj hnd x₀ hi hi' (e.trans e'.symm)
  have hcard_a : secondSmallestDegree G ≤ Ja.card + 3 := by omega
  by_cases h5 : 5 ≤ secondSmallestDegree G
  · exact b23_gamma (fun i => l.getD i x₀ = x₀) l.length Jz Ja hJne hbdz hpr1 hpr2 hsub hβ hinj h5a
      (by omega) (by omega)
  · have hσ4e : secondSmallestDegree G = 4 := by omega
    have hcz2 : Jz.card = 2 := by omega
    have hm10 : l.length = 10 := by omega
    have hlt2 : 1 < Jz.card := by omega
    have hmin' := Finset.min'_lt_max'_of_card Jz hlt2
    have hpz : Jz.min' hJne ∈ Jz := Finset.min'_mem _ _
    have hp2 : Jz.min' hJne + 2 ∈ Jz := hpr1 _ hpz (ne_of_lt hmin')
    set p := Jz.min' hJne with hp
    have hJeq : Jz = {p, p + 2} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption
      · rw [hcz2, Finset.card_pair (by omega)]
    have hJane : Ja.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h] at hcard_a; simp at hcard_a; omega
    obtain ⟨j0, hj0⟩ := hJane
    have hj0z := hsub hj0
    rw [hJeq] at hj0z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj0z
    have hpb := hbdz p hpz
    have hpb2 := hbdz (p + 2) hp2
    have hP : l.getD (p + 1) x₀ = x₀ := by
      apply hβ p hpz hp2
      rcases hj0z with rfl | rfl
      · exact Or.inl hj0
      · exact Or.inr hj0
    have hzp : G.Adj z (l.getD p x₀) := (Finset.mem_filter.mp hpz).2
    have hzp2 : G.Adj z (l.getD (p + 2) x₀) := (Finset.mem_filter.mp hp2).2
    have hp4 : 4 ≤ p := by
      by_contra hlt4
      push Not at hlt4
      refine Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [b, z', a, z]
        (by simp) ?_ ?_ ?_ p (by omega) hzp ?_ (by simp; omega)
      · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
          Ne.symm d5, Ne.symm d6]
      · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
        exact ⟨h4.symm, h3, h1.symm⟩
      · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> assumption
      · intro i hi he
        have := hinj i (p + 1) (by omega) (by omega) he hP
        omega
    refine Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [z, a, z', b]
      (by simp) ?_ ?_ ?_ (p + 2) (by omega) hzp2.symm ?_ (by simp; omega)
    · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
        Ne.symm d5, Ne.symm d6]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨h1, h3.symm, h4⟩
    · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> assumption
    · intro i hi hi2 he
      have := hinj i (p + 1) hi2 (by omega) he hP
      omega
lemma b24_c11 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (hσ : secondSmallestDegree G = 5) (hm : l.length = 12)
    (a b c d : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d}) (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hadj : G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)
    (hA : ∀ y ∈ ({a, b, c, d} : Finset V), G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 7 x₀))
    (hx : l.getD 1 x₀ = x₀) : False := by
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := id hd
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := id hadj
  have hmemR : ∀ t, t ∉ l ↔ t ∈ ({a, b, c, d} : Finset V) := by
    intro t; rw [← hR]; simp
  have hcardR : (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by
    rw [hR]; simp [Finset.card_insert_of_notMem, d1, d2, d3, d4, d5, d6]
  have hirr : ∀ t : V, ¬ G.Adj t t := fun t => G.loopless.irrefl t
  have hclq : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → G.Adj y y' := by
    intro y y' hy hy' hne'
    have hy2 := (hmemR y).mp hy
    have hy2' := (hmemR y').mp hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy2 hy2'
    rcases hy2 with h | h | h | h <;> rcases hy2' with h' | h' | h' | h' <;>
      rw [h, h'] at hne' <;> rw [h, h'] <;>
      first
      | exact absurd rfl hne'
      | assumption
      | exact SimpleGraph.Adj.symm (by assumption)
  have hother : ∀ y : V, y ∉ l → ∃ w, w ∉ l ∧ w ≠ y := by
    intro y hy
    have h1 : 1 < (Finset.univ.filter (fun t => t ∉ l)).card := by omega
    obtain ⟨w, hw', hwy⟩ := Finset.exists_mem_ne h1 y
    exact ⟨w, by simpa using hw', hwy⟩
  have hsd : ∀ y y' : V, 1 < ((Finset.univ.filter (fun t => t ∉ l)) \ {y, y'}).card := by
    intro y y'
    have h1 := Finset.le_card_sdiff ({y, y'} : Finset V) (Finset.univ.filter (fun t => t ∉ l))
    have h3 : ({y, y'} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  have hother2 : ∀ y y' : V, y ∉ l → y' ∉ l → ∃ w, w ∉ l ∧ w ≠ y ∧ w ≠ y' := by
    intro y y' hy hy'
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu
    exact ⟨u, hu.1, hu.2.1, hu.2.2⟩
  have hpath4 : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → ∃ u v : V, u ∉ l ∧ v ∉ l ∧
      [y, u, v, y'].Nodup ∧ [y, u, v, y'].IsChain G.Adj := by
    intro y y' hy hy' hyy
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu hv
    refine ⟨u, v, hu.1, hv.1, ?_, ?_⟩
    · simp [hyy, huv, hu.2.1, hu.2.2, hv.2.1, hv.2.2, Ne.symm hu.2.1, Ne.symm hu.2.2,
        Ne.symm hv.2.1, Ne.symm hv.2.2]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨hclq y u hy hu.1 (Ne.symm hu.2.1), hclq u v hu.1 hv.1 huv,
        hclq v y' hv.1 hy' hv.2.2⟩
  have hm12 : l.length = 12 := hm
  have hm0 : 0 < l.length := List.length_pos_of_ne_nil hne
  have hgd : ∀ (d d' : V) (i : ℕ), i < l.length → l.getD i d = l.getD i d' := by
    intro d d' i hi; rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
  have hXmem : ∀ i, i < l.length → l.getD i x₀ ∈ l := by
    intro i hi; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hinj : ∀ i j, i < l.length → j < l.length → l.getD i x₀ = l.getD j x₀ → i = j :=
    fun i j hi hj h => b23_getD_inj hnd x₀ hi hj h
  have hhead : l.head hne = l.getD 0 x₀ := by
    cases l with
    | nil => exact absurd rfl hne
    | cons h t => rfl
  have hlastv : l.getLast hne = l.getD 11 x₀ := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    congr 1; omega
  have hadjc : ∀ i, i + 1 < l.length → G.Adj (l.getD i x₀) (l.getD (i + 1) x₀) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
    exact List.isChain_iff_getElem.mp hch i hi
  have hmaxs := Cadre.hmax_sup hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := lemma4x hconn l hne hnd hch hmaxs hlt (by omega)
  rw [hhead] at c1 c4
  rw [hlastv] at c2 c4
  have h5b : ∀ y, y ∉ l → ∀ j, j < l.length → G.Adj y (l.getD j x₀) →
      0 < j ∧ j + 1 < l.length ∧ ¬ G.Adj y (l.getD (j + 1) x₀) ∧ ¬ G.Adj y (l.getD (j - 1) x₀) ∧
      ¬ G.Adj (l.getD 0 x₀) (l.getD (j + 1) x₀) ∧ ¬ G.Adj (l.getD 11 x₀) (l.getD (j - 1) x₀) := by
    intro y hy j hj hadj'
    have := lemma5abx hconn l hne hnd hch hmaxs y hy j hj (by rwa [hgd y x₀ j hj])
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := this
    rw [hhead, hgd y x₀ (j + 1) t2] at t5
    rw [hlastv, hgd y x₀ (j - 1) (by omega)] at t6
    rw [hgd y x₀ (j + 1) t2] at t3
    rw [hgd y x₀ (j - 1) (by omega)] at t4
    exact ⟨t1, t2, t3, t4, t5, t6⟩
  have hRA : ∀ y, y ∉ l → G.Adj y (l.getD 2 x₀) ∧ G.Adj y (l.getD 7 x₀) :=
    fun y hy => hA y ((hmemR y).mp hy)
  have ha : a ∉ l := (hmemR a).mpr (by simp)
  have hdist2 : ∀ y w z : V, y ≠ w → ¬ G.Adj y w → G.Adj y z → G.Adj z w → G.dist y w = 2 := by
    intro y w z hyw hnadj h1 h2
    have hle : G.dist y w ≤ 2 :=
      SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
    have hreach : G.Reachable y w :=
      ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)⟩
    have h0 : G.dist y w ≠ 0 := fun h => hyw ((SimpleGraph.Reachable.dist_eq_zero_iff hreach).mp h)
    have h1' : G.dist y w ≠ 1 := fun h => hnadj (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have hdl : d ∉ l := (hmemR d).mpr (by simp)
  have hsl0 : ∀ t ∈ [a, b, c, d], t ∉ l := by
    intro t ht; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h | h <;> rw [h] <;> exact (hmemR _).mpr (by simp)
  have hnd0 : [a, b, c, d].Nodup := by simp [d1, d2, d3, d4, d5, d6]
  have hch0 : [a, b, c, d].IsChain G.Adj := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨e1, e4, e6⟩
  have c4' : ∀ j, j + 1 < l.length → G.Adj (l.getD 0 x₀) (l.getD (j + 1) x₀) →
      ¬ G.Adj (l.getD j x₀) (l.getD 11 x₀) := by
    intro j hj h hl'
    exact c4 j hj (by rw [hgd (l.getD 0 x₀) x₀ (j + 1) hj]; exact h)
      (by rw [hgd (l.getD 0 x₀) x₀ j (by omega)]; exact hl')
  have hne0 : l.getD 0 x₀ ≠ x₀ := hhead ▸ hhd
  have hdeg0 : 5 ≤ G.degree (l.getD 0 x₀) := by rw [← hσ]; exact hx0 _ hne0
  have hE : ∀ j, 2 < j → j ≤ 6 → ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
    intro j h1 h2 hadj'
    exact Cadre.endE hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [a, b, c, d]
      (by simp) hnd0 hch0 hsl0 2 j h1 (by omega) hadj' (by simpa using (hRA d hdl).1)
      ⟨1, Or.inl (by omega), by omega, hx⟩ (by simp; omega)
  have hexcl : ∀ j, 0 < j → j < l.length → j ∉ ({1, 2, 7, 9, 10} : Finset ℕ) →
      ¬ G.Adj (l.getD 0 x₀) (l.getD j x₀) := by
    intro j h0 h12 hj
    have hcases : (2 < j ∧ j ≤ 6) ∨ j = 8 ∨ j = 11 := by simp at hj; omega
    rcases hcases with ⟨h1, h2⟩ | rfl | rfl
    · exact hE j h1 h2
    · exact (h5b a ha 7 (by omega) (hRA a ha).2).2.2.2.2.1
    · intro hadj'
      exact c4' 10 (by omega) hadj' (hadjc 10 (by omega))
  have hle0 := Cadre.head_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    ({1, 2, 7, 9, 10} : Finset ℕ) hexcl
  have hcard5 : ({1, 2, 7, 9, 10} : Finset ℕ).card = 5 := by decide
  have hforced := Cadre.head_forced hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    ({1, 2, 7, 9, 10} : Finset ℕ) (by intro j hj; simp at hj; omega) hexcl (by omega)
  have hX02 : G.Adj (l.getD 0 x₀) (l.getD 2 x₀) := hforced 2 (by simp)
  obtain ⟨S', hS'⟩ : ∃ S' : Finset V, S' = ({0, 1, 3, 6, 8} : Finset ℕ).image (fun i => l.getD i x₀) :=
    ⟨_, rfl⟩
  have hneA : ∀ i, i < l.length → a ≠ l.getD i x₀ := fun i hi h => ha (h ▸ hXmem i hi)
  have hdist : ∀ w ∈ S', G.dist a w = 2 := by
    intro w hw
    rw [hS'] at hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact hdist2 a _ (l.getD 2 x₀) (hneA _ (by omega)) (fun h => ha (c1 a h.symm))
        (hRA a ha).1 hX02.symm
    · exact hdist2 a _ (l.getD 2 x₀) (hneA _ (by omega))
        (h5b a ha 2 (by omega) (hRA a ha).1).2.2.2.1 (hRA a ha).1 (hadjc 1 (by omega)).symm
    · exact hdist2 a _ (l.getD 2 x₀) (hneA _ (by omega))
        (h5b a ha 2 (by omega) (hRA a ha).1).2.2.1 (hRA a ha).1 (hadjc 2 (by omega))
    · exact hdist2 a _ (l.getD 7 x₀) (hneA _ (by omega))
        (h5b a ha 7 (by omega) (hRA a ha).2).2.2.2.1 (hRA a ha).2 (hadjc 6 (by omega)).symm
    · exact hdist2 a _ (l.getD 7 x₀) (hneA _ (by omega))
        (h5b a ha 7 (by omega) (hRA a ha).2).2.2.1 (hRA a ha).2 (hadjc 7 (by omega))
  have hS'card : S'.card = 5 := by
    rw [hS', Finset.card_image_of_injOn]
    · decide
    · intro i hi j hj h
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi hj
      exact hinj i j (by omega) (by omega) h
  have hΓ : ∀ j, (j = 2 ∨ j = 7) → ¬ G.Adj (l.getD j x₀) (l.getD 11 x₀) := by
    intro j hj hadj'
    have hzj : G.Adj a (l.getD j x₀) := by
      rcases hj with rfl | rfl
      · exact (hRA a ha).1
      · exact (hRA a ha).2
    have hnot : l.getD 11 x₀ ∉ S' := by
      intro h
      rw [hS'] at h
      obtain ⟨i, hi, hi2⟩ := Finset.mem_image.mp h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      have := hinj i 11 (by omega) (by omega) hi2
      omega
    have hc := Finset.card_insert_of_notMem hnot
    have hb3 := card_le_gamma hconn hH a (insert (l.getD 11 x₀) S') (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact hdist2 a _ (l.getD j x₀) (hneA _ (by omega)) (fun h => ha (c2 a h.symm)) hzj
          hadj'
      · exact hdist w hw')
    omega
  have hexL : ∀ j, j + 1 < l.length → j ∉ ({8, 9, 10} : Finset ℕ) →
      ¬ G.Adj (l.getD j x₀) (l.getD (l.length - 1) x₀) := by
    intro j hj hnC hadj'
    have e11 : l.length - 1 = 11 := by omega
    rw [e11] at hadj'
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ (3 ≤ j ∧ j ≤ 6) ∨ j = 7 := by simp at hnC; omega
    rcases hcases with rfl | rfl | rfl | ⟨h1, h2⟩ | rfl
    · exact c4' 10 (by omega) hadj' (hadjc 10 (by omega))
    · exact (h5b a ha 2 (by omega) (hRA a ha).1).2.2.2.2.2 hadj'.symm
    · exact hΓ 2 (Or.inl rfl) hadj'
    · exact Cadre.endE_last hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [a, b, c, d]
        (by simp) hnd0 hch0 hsl0 7 j (by omega) (by omega) (by rw [e11]; exact hadj'.symm)
        (by simpa using (hRA a ha).2) ⟨1, Or.inr (by omega), by omega, hx⟩ (by simp; omega)
    · exact hΓ 7 (Or.inr rfl) hadj'
  have hleL := Cadre.last_deg_le hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    ({8, 9, 10} : Finset ℕ) hexL
  have hcard3 : ({8, 9, 10} : Finset ℕ).card = 3 := by decide
  have hneL : l.getD (l.length - 1) x₀ ≠ x₀ := by
    have e11 : l.length - 1 = 11 := by omega
    rw [e11, ← hlastv]; exact hlast
  have hdegL : 5 ≤ G.degree (l.getD (l.length - 1) x₀) := by rw [← hσ]; exact hx0 _ hneL
  omega
lemma b24_core [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (a b c d : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d}) (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hadj : G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)
    (hm : l.length = 2 * secondSmallestDegree G + 2)
    (hw : ∀ i, i < l.length → l.getD i x₀ = x₀ → 2 * i + 1 ≤ l.length) : False := by
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := id hd
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := id hadj
  have hmemR : ∀ t, t ∉ l ↔ t ∈ ({a, b, c, d} : Finset V) := by
    intro t; rw [← hR]; simp
  have hcardR : (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by
    rw [hR]; simp [Finset.card_insert_of_notMem, d1, d2, d3, d4, d5, d6]
  have hirr : ∀ t : V, ¬ G.Adj t t := fun t => G.loopless.irrefl t
  have hclq : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → G.Adj y y' := by
    intro y y' hy hy' hne'
    have hy2 := (hmemR y).mp hy
    have hy2' := (hmemR y').mp hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy2 hy2'
    rcases hy2 with h | h | h | h <;> rcases hy2' with h' | h' | h' | h' <;>
      rw [h, h'] at hne' <;> rw [h, h'] <;>
      first
      | exact absurd rfl hne'
      | assumption
      | exact SimpleGraph.Adj.symm (by assumption)
  have hother : ∀ y : V, y ∉ l → ∃ w, w ∉ l ∧ w ≠ y := by
    intro y hy
    have h1 : 1 < (Finset.univ.filter (fun t => t ∉ l)).card := by omega
    obtain ⟨w, hw', hwy⟩ := Finset.exists_mem_ne h1 y
    exact ⟨w, by simpa using hw', hwy⟩
  have hsd : ∀ y y' : V, 1 < ((Finset.univ.filter (fun t => t ∉ l)) \ {y, y'}).card := by
    intro y y'
    have h1 := Finset.le_card_sdiff ({y, y'} : Finset V) (Finset.univ.filter (fun t => t ∉ l))
    have h3 : ({y, y'} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  have hother2 : ∀ y y' : V, y ∉ l → y' ∉ l → ∃ w, w ∉ l ∧ w ≠ y ∧ w ≠ y' := by
    intro y y' hy hy'
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu
    exact ⟨u, hu.1, hu.2.1, hu.2.2⟩
  have hpath4 : ∀ y y' : V, y ∉ l → y' ∉ l → y ≠ y' → ∃ u v : V, u ∉ l ∧ v ∉ l ∧
      [y, u, v, y'].Nodup ∧ [y, u, v, y'].IsChain G.Adj := by
    intro y y' hy hy' hyy
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hsd y y')
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hu hv
    refine ⟨u, v, hu.1, hv.1, ?_, ?_⟩
    · simp [hyy, huv, hu.2.1, hu.2.2, hv.2.1, hv.2.2, Ne.symm hu.2.1, Ne.symm hu.2.2,
        Ne.symm hv.2.1, Ne.symm hv.2.2]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨hclq y u hy hu.1 (Ne.symm hu.2.1), hclq u v hu.1 hv.1 huv,
        hclq v y' hv.1 hy' hv.2.2⟩
  have hσ4 : 4 ≤ secondSmallestDegree G := by
    by_contra hlt4
    push Not at hlt4
    have hham : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∃ s : List V, s.Nodup ∧
        s.IsChain G.Adj ∧ s.toFinset = (Finset.univ.filter (fun t => t ∉ l)) ∧
        s.getLast? = some y := by
      intro y hy
      rw [hR] at hy ⊢
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h | h | h <;> rw [h]
      · refine ⟨[b, c, d, a], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, c, d, b], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, b, d, c], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
      · refine ⟨[a, b, c, d], ?_, ?_, ?_, ?_⟩
        · simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
            Ne.symm d5, Ne.symm d6]
        · simp [List.isChain_cons_cons, e1, e1.symm, e2, e2.symm, e3, e3.symm, e4, e4.symm,
            e5, e5.symm, e6, e6.symm]
        · ext t; simp <;> tauto
        · simp
    have hd2 : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), ∀ y' ∈ (Finset.univ.filter (fun t => t ∉ l)),
        y ≠ y' → G.Adj y y' ∨ ∃ w ∈ (Finset.univ.filter (fun t => t ∉ l)), G.Adj y w ∧ G.Adj w y' := by
      intro y hy y' hy' hne'
      exact Or.inl (hclq y y' (by simpa using hy) (by simpa using hy') hne')
    have := Cadre.small_sigma hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hham hd2
    omega
  have hm0 : 0 < l.length := List.length_pos_of_ne_nil hne
  obtain ⟨Jf, hJf⟩ : ∃ Jf : V → Finset ℕ, ∀ y, Jf y =
      (Finset.range l.length).filter (fun i => G.Adj y (l.getD i x₀)) := ⟨_, fun _ => rfl⟩
  have hJm : ∀ y i, i ∈ Jf y ↔ i < l.length ∧ G.Adj y (l.getD i x₀) := by
    intro y i; rw [hJf]; simp
  obtain ⟨A, hAm'⟩ : ∃ A : Finset ℕ, ∀ i, i ∈ A ↔
      i < l.length ∧ ∃ y, y ∉ l ∧ G.Adj y (l.getD i x₀) :=
    ⟨(Finset.range l.length).filter (fun i => ∃ y, y ∉ l ∧ G.Adj y (l.getD i x₀)),
      fun i => by simp⟩
  have hbnd : ∀ y, y ∉ l → ∀ j, j < l.length → G.Adj y (l.getD j x₀) →
      0 < j ∧ j + 1 < l.length := by
    intro y hy j hj hadj'
    exact Cadre.J_bounds hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt hy
      (by rw [← hJf]; exact (hJm y j).mpr ⟨hj, hadj'⟩)
  have hJA : ∀ y, y ∉ l → Jf y ⊆ A := by
    intro y hy i hi
    obtain ⟨h1, h2⟩ := (hJm y i).mp hi
    exact (hAm' i).mpr ⟨h1, y, hy, h2⟩
  have hAm : ∀ i ∈ A, 1 ≤ i ∧ i + 2 ≤ l.length := by
    intro i hi
    obtain ⟨h1, y, hy, h2⟩ := (hAm' i).mp hi
    have := hbnd y hy i h1 h2
    omega
  have hdegJ : ∀ y, y ∉ l → secondSmallestDegree G ≤ (Jf y).card + 3 := by
    intro y hy
    have hds := Cadre.degree_split (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch
      hmem hhd hlast hmax hlt hy
    rw [← hJf] at hds
    have hyx : y ≠ x₀ := fun h => hy (h ▸ hmem)
    have hσy := hx0 y hyx
    have hN : ((Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y)).card ≤ 3 := by
      have hsub : (Finset.univ.filter (fun t => t ∉ l)).filter (G.Adj y) ⊆
          (Finset.univ.filter (fun t => t ∉ l)).erase y := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [Finset.mem_erase]
        refine ⟨?_, ht.1⟩
        rintro rfl
        exact hirr _ ht.2
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by simpa using hy)] at h1
      omega
    omega
  have hXmem : ∀ i, i < l.length → l.getD i x₀ ∈ l := by
    intro i hi; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hinj : ∀ i j, i < l.length → j < l.length → l.getD i x₀ = l.getD j x₀ → i = j :=
    fun i j hi hj h => b23_getD_inj hnd x₀ hi hj h
  have hAJ : ∀ y, y ∉ l → (A \ Jf y).card ≤ 2 := by
    intro y hy
    obtain ⟨Bp, hBp⟩ : ∃ Bp : Finset V, ∀ w, w ∈ Bp ↔ w ∈ l ∧ ¬ G.Adj y w ∧ ∃ w2, w2 ∉ l ∧ G.Adj w2 w :=
      ⟨l.toFinset.filter (fun w => ¬ G.Adj y w ∧ ∃ w2, w2 ∉ l ∧ G.Adj w2 w), fun w => by simp⟩
    have hB : ∀ w ∈ Bp, w ∈ l ∧ ¬ G.Adj y w ∧ ∃ z, z ∉ l ∧ G.Adj y z ∧ G.Adj z w := by
      intro w hw
      obtain ⟨h1, h2, w2, hw2, h3⟩ := (hBp w).mp hw
      refine ⟨h1, h2, w2, hw2, ?_, h3⟩
      have hne2 : y ≠ w2 := by rintro rfl; exact h2 h3
      exact hclq y w2 hy hw2 hne2
    have hK : ∀ w ∈ (∅ : Finset V), w ∉ l ∧ w ≠ y ∧ ¬ G.Adj y w ∧ ∃ z, G.Adj y z ∧ G.Adj z w := by
      intro w hw; simp at hw
    have hB9 := Cadre.count_Q2 (G := G) (x₀ := x₀) (l := l) hconn hb hH hmin hx0 hδ hne hnd hch hmem
      hhd hlast hmax hlt y hy Bp ∅ hB hK
    rw [← hJf] at hB9
    have hdg := hdegJ y hy
    have hJne : (Jf y).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h] at hdg; simp at hdg; omega
    have hring := ring_card (Jf y) (fun h0 => by
      have := (hJm y 0).mp h0
      have := hbnd y hy 0 this.1 this.2
      omega)
    have hTl := T_lt (Jf y) hJne
    have hcardle : (A \ Jf y).card ≤ Bp.card := by
      apply Finset.card_le_card_of_injOn (fun i => l.getD i x₀)
      · intro i hi
        rw [Finset.mem_coe, Finset.mem_sdiff] at hi
        obtain ⟨hiA, hiJ⟩ := hi
        obtain ⟨hil, w2, hw2, hw2a⟩ := (hAm' i).mp hiA
        rw [Finset.mem_coe, hBp]
        refine ⟨hXmem i hil, ?_, w2, hw2, hw2a⟩
        intro hadj'
        exact hiJ ((hJm y i).mpr ⟨hil, hadj'⟩)
      · intro i hi j hj hij
        rw [Finset.mem_coe, Finset.mem_sdiff] at hi hj
        obtain ⟨hil, _⟩ := (hAm' i).mp hi.1
        obtain ⟨hjl, _⟩ := (hAm' j).mp hj.1
        exact hinj i j hil hjl hij
    simp only [Finset.card_empty] at hB9
    omega
  obtain ⟨i₀, hi₀l, hi₀⟩ : ∃ i, i < l.length ∧ l.getD i x₀ = x₀ := by
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact hx⟩
  have hX0 : ∀ i, i < l.length → l.getD i x₀ = x₀ → i = i₀ :=
    fun i hi he => hinj i i₀ hi hi₀l (he.trans hi₀.symm)
  have hi : 1 ≤ i₀ ∧ i₀ + 2 ≤ l.length := by
    have h0 : l.getD 0 x₀ = l.head hne := by
      cases l with
      | nil => exact absurd rfl hne
      | cons h t => rfl
    have h1 : l.getD (l.length - 1) x₀ = l.getLast hne := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
    have hn0 : i₀ ≠ 0 := by
      intro h; rw [h] at hi₀; exact hhd (h0 ▸ hi₀)
    have hn1 : i₀ ≠ l.length - 1 := by
      intro h; rw [h] at hi₀; exact hlast (h1 ▸ hi₀)
    omega
  obtain ⟨E, hE'⟩ : ∃ E : Finset ℕ, ∀ x, x ∈ E ↔ x ∈ A ∧ ∃ x2 ∈ A, x < x2 ∧
      (∀ z ∈ A, ¬ (x < z ∧ z < x2)) ∧ ∃ w, w ∉ l ∧ ∀ w', w' ∉ l →
        (G.Adj w' (l.getD x x₀) ∨ G.Adj w' (l.getD x2 x₀)) → w' = w :=
    ⟨A.filter (fun x => ∃ x2 ∈ A, x < x2 ∧ (∀ z ∈ A, ¬ (x < z ∧ z < x2)) ∧ ∃ w, w ∉ l ∧
      ∀ w', w' ∉ l → (G.Adj w' (l.getD x x₀) ∨ G.Adj w' (l.getD x2 x₀)) → w' = w),
      fun x => by simp [Finset.mem_filter]⟩
  have hEA : E ⊆ A := fun x hx => ((hE' x).mp hx).1
  have hM : ∀ x ∈ A, ∀ y ∈ A, x < y → (∀ z ∈ A, ¬ (x < z ∧ z < y)) →
      x + 2 ≤ y ∧ (x ∉ E → x + 4 + 1 ≤ y ∨ (x < i₀ ∧ i₀ < y)) := by
    intro x hx y hy hxy hcons
    obtain ⟨hxl, wx, hwx, hxw⟩ := (hAm' x).mp hx
    obtain ⟨hyl, wy, hwy, hyw⟩ := (hAm' y).mp hy
    constructor
    · by_contra hlt2
      have hy1 : y = x + 1 := by omega
      by_cases hww : wx = wy
      · subst hww
        exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [wx]
          (by simp) (by simp) (by simp)
          (by intro v hv; simp at hv; subst hv; exact hwx) x y hxy hyl hxw.symm hyw
          (by intro i h1 h2; omega) (by simp only [List.length_singleton]; omega)
      · exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [wx, wy]
          (by simp) (by simp [hww])
          (by simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
              exact hclq wx wy hwx hwy hww)
          (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption)
          x y hxy hyl hxw.symm hyw
          (by intro i h1 h2; omega) (by simp; omega)
    · intro hxE
      by_contra hcon
      push Not at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      have hyx5 : y < x + 5 := by omega
      have hxnx : ∀ i, x < i → i < y → l.getD i x₀ ≠ x₀ := by
        intro i h1 h2 he
        have := hX0 i (by omega) he
        have := hc2 (by omega)
        omega
      obtain ⟨u, v, hu, hv, huv, hu1, hv1⟩ : ∃ u v : V, u ∉ l ∧ v ∉ l ∧ u ≠ v ∧
          G.Adj u (l.getD x x₀) ∧ G.Adj v (l.getD y x₀) := by
        by_cases hww : wx = wy
        · subst hww
          have key : ∃ w, w ∉ l ∧ (G.Adj w (l.getD x x₀) ∨ G.Adj w (l.getD y x₀)) ∧ w ≠ wx := by
            by_contra hno
            push Not at hno
            exact hxE ((hE' x).mpr ⟨hx, y, hy, hxy, hcons, wx, hwx, fun w hw h => hno w hw h⟩)
          obtain ⟨w, hw, hwa, hwne⟩ := key
          rcases hwa with h | h
          · exact ⟨w, wx, hw, hwx, hwne, h, hyw⟩
          · exact ⟨wx, w, hwx, hw, hwne.symm, hxw, h⟩
        · exact ⟨wx, wy, hwx, hwy, hww, hxw, hyw⟩
      obtain ⟨p, q, hp, hq, hnd4, hch4⟩ := hpath4 u v hu hv huv
      exact Cadre.no_mid hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [u, p, q, v]
        (by simp) hnd4 hch4
        (by intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption)
        x y hxy hyl hu1.symm hv1 hxnx (by simp; omega)
  have hAne : A.Nonempty := by
    obtain ⟨x, y, hxy, hyl, ⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩ :=
      Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    exact ⟨x, (hAm' x).mpr ⟨by omega, w1, by simpa using hw1, h1⟩⟩
  have hA2 : 2 ≤ A.card := by
    obtain ⟨x, y, hxy, hyl, ⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩ :=
      Cadre.two_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hxA : x ∈ A := (hAm' x).mpr ⟨by omega, w1, by simpa using hw1, h1⟩
    have hyA : y ∈ A := (hAm' y).mpr ⟨hyl, w2, by simpa using hw2, h2⟩
    have : ({x, y} : Finset ℕ) ⊆ A := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have h3 := Finset.card_le_card this
    rwa [Finset.card_pair (by omega)] at h3
  have hL : 4 ≤ A.min' hAne ∨ i₀ < A.min' hAne := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hminA := Finset.min'_mem A hAne
    obtain ⟨hml, wy, hwy, hyw⟩ := (hAm' _).mp hminA
    obtain ⟨y2, hy2, hy2y⟩ := hother wy hwy
    obtain ⟨u, v, hu, hv, hnd4, hch4⟩ := hpath4 y2 wy hy2 hwy hy2y
    exact Cadre.no_pre hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [y2, u, v, wy]
      (by simp) hnd4 hch4
      (by intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption)
      (A.min' hAne) hml (by simpa using hyw)
      (by intro i hi' he; have := hX0 i (by omega) he; omega) (by simp; omega)
  have hR' : A.max' hAne + 4 + 1 ≤ l.length ∨ A.max' hAne < i₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hmaxA := Finset.max'_mem A hAne
    obtain ⟨hml, wy, hwy, hyw⟩ := (hAm' _).mp hmaxA
    obtain ⟨y2, hy2, hy2y⟩ := hother wy hwy
    obtain ⟨u, v, hu, hv, hnd4, hch4⟩ := hpath4 wy y2 hwy hy2 (Ne.symm hy2y)
    exact Cadre.no_suf hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt [wy, u, v, y2]
      (by simp) hnd4 hch4
      (by intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption)
      (A.max' hAne) hml (by simpa using hyw.symm)
      (by intro i hi1 hi2 he; have := hX0 i hi2 he; omega) (by simp; omega)
  have hE2 : ∀ x ∈ E, ∀ y ∈ E, x < y → False := by
    intro x hx y hy hxy
    obtain ⟨hxA, x2, hx2, hxx2, hcx, wx, hwx, hwxall⟩ := (hE' x).mp hx
    obtain ⟨hyA, y2, hy2, hyy2, hcy, wy, hwy, hwyall⟩ := (hE' y).mp hy
    obtain ⟨w, hw, hw1, hw2⟩ := hother2 wx wy hwx hwy
    have hn1 : ¬ G.Adj w (l.getD x x₀) := fun h => hw1 (hwxall w hw (Or.inl h))
    have hn2 : ¬ G.Adj w (l.getD y x₀) := fun h => hw2 (hwyall w hw (Or.inl h))
    have hn3 : ¬ G.Adj w (l.getD y2 x₀) := fun h => hw2 (hwyall w hw (Or.inr h))
    have hsub3 : ({x, y, y2} : Finset ℕ) ⊆ A \ Jf w := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [Finset.mem_sdiff]
      rcases ht with rfl | rfl | rfl
      · exact ⟨hxA, fun h => hn1 ((hJm w _).mp h).2⟩
      · exact ⟨hyA, fun h => hn2 ((hJm w _).mp h).2⟩
      · exact ⟨hy2, fun h => hn3 ((hJm w _).mp h).2⟩
    have h3 := Finset.card_le_card hsub3
    rw [Finset.card_eq_three.mpr ⟨x, y, y2, by omega, by omega, by omega, rfl⟩] at h3
    have := hAJ w hw
    omega
  have hEcard : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hne2
    rcases lt_or_gt_of_ne hne2 with h | h
    · exact hE2 x hx y hy h
    · exact hE2 y hy x hx h
  have hEempty : (∀ y, y ∉ l → A ⊆ Jf y) → E.card = 0 := by
    intro hsup
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxA, x2, hx2, hxx2, hcx, wx, hwx, hall⟩ := (hE' x).mp hx
    obtain ⟨w, hw, hwne⟩ := hother wx hwx
    exact hwne (hall w hw (Or.inl ((hJm w x).mp (hsup w hw hxA)).2))
  have hpack := pack A E l.length 4 i₀ (by norm_num) hAne hEA hAm hi hL hR' hM
  have ha : a ∉ l := (hmemR a).mpr (by simp)
  have hσA : secondSmallestDegree G ≤ A.card + 3 :=
    le_trans (hdegJ a ha) (by have := Finset.card_le_card (hJA a ha); omega)
  have hσ6 : secondSmallestDegree G ≤ 6 := by omega
  have hfull : A.card ≤ (secondSmallestDegree G) - 3 → ∀ y, y ∉ l → Jf y = A := by
    intro hr y hy
    exact Finset.eq_of_subset_of_card_le (hJA y hy) (by have := hdegJ y hy; omega)
  have hσcases : secondSmallestDegree G = 4 ∨ secondSmallestDegree G = 5 ∨
      secondSmallestDegree G = 6 := by omega
  rcases hσcases with h4 | h5 | h6
  ·
    have hr2 : A.card = 2 := by omega
    have hE1 : 1 ≤ E.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
    obtain ⟨hxA, x2, hx2, hxx2, hcx, wx, hwx, hall⟩ := (hE' x).mp hx
    have hAeq : A = {x, x2} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption
      · rw [hr2, Finset.card_pair (by omega)]
    obtain ⟨w, hw, hwne⟩ := hother wx hwx
    have hdw := hdegJ w hw
    obtain ⟨i, hi'⟩ := Finset.card_pos.mp (by omega : 0 < (Jf w).card)
    have hiA := hJA w hw hi'
    rw [hAeq] at hiA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiA
    have hadj' := ((hJm w i).mp hi').2
    rcases hiA with rfl | rfl
    · exact hwne (hall w hw (Or.inl hadj'))
    · exact hwne (hall w hw (Or.inr hadj'))
  ·
    have hr2 : A.card = 2 := by omega
    have hfl := hfull (by omega)
    have hallA : ∀ y, y ∉ l → ∀ i ∈ A, G.Adj y (l.getD i x₀) := fun y hy i hi' =>
      ((hJm y i).mp (by rw [hfl y hy]; exact hi')).2
    have hE0 := hEempty (fun y hy i hi' => by rw [hfl y hy]; exact hi')
    have hm12 : l.length = 12 := by omega
    have hw' := hw i₀ hi₀l hi₀
    set P := A.min' hAne with hP
    set Q := A.max' hAne with hQ
    have hPA : P ∈ A := Finset.min'_mem A hAne
    have hQA : Q ∈ A := Finset.max'_mem A hAne
    have hPQ : P < Q := Finset.min'_lt_max'_of_card A (by omega)
    have hAeq : A = {P, Q} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption
      · rw [hr2, Finset.card_pair (by omega)]
    have hcons : ∀ z ∈ A, ¬ (P < z ∧ z < Q) := by
      intro z hz hzz
      rw [hAeq] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      omega
    obtain ⟨hgap, hcross⟩ := hM P hPA Q hQA hPQ hcons
    have hPE : P ∉ E := by
      intro hmemE
      have := Finset.card_pos.mpr ⟨P, hmemE⟩
      omega
    have hcr := hcross hPE
    have hAmP := hAm P hPA
    have hAmQ := hAm Q hQA
    have hcardR4 := hcardR
    have hSmem : ∀ y ∈ (Finset.univ.filter (fun t => t ∉ l)), y ∉ l := by
      intro y hy; simpa using hy
    by_cases hx0A : i₀ = P ∨ i₀ = Q
    · have hi0A : i₀ ∈ A := by rcases hx0A with h | h <;> rw [h] <;> assumption
      have := Cadre.x0_attach hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
        (Finset.univ.filter (fun t => t ∉ l)) hSmem i₀ hi.1 (by omega) hi₀
        (by intro y hy; have := hallA y (hSmem y hy) i₀ hi0A; rwa [hi₀] at this)
      omega
    · obtain ⟨y2, hy2, hy2a⟩ := hother a ha
      obtain ⟨u, v, hu, hv, hnd4, hch4⟩ := hpath4 a y2 ha hy2 (Ne.symm hy2a)
      have hsl : ∀ t ∈ [a, u, v, y2], t ∉ l := by
        intro t ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption
      by_cases hq : Q = P + 2
      · have hi1 : i₀ = P + 1 := by omega
        have := Cadre.hole_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
          (Finset.univ.filter (fun t => t ∉ l)) hSmem P hAmP.1 (by omega)
          (by rw [← hi1]; exact hi₀)
          (fun y hy => Or.inl (hallA y (hSmem y hy) P hPA))
          [a, u, v, y2] (by simp) hnd4 hch4 hsl
          (by simpa using (hallA a ha P hPA).symm)
          (by rw [← hq]; simpa using (hallA y2 hy2 Q hQA))
        omega
      · have hcase : (i₀ = 1 ∧ P = 2 ∧ Q = 7) ∨ (i₀ = 5 ∧ P = 4 ∧ Q = 7) := by omega
        rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have h2A : 2 ∈ A := h2 ▸ hPA
          have h7A : 7 ∈ A := h3 ▸ hQA
          exact b24_c11 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt h5 hm12
            a b c d hR hd hadj
            (by intro y hy; exact ⟨hallA y ((hmemR y).mpr hy) 2 h2A, hallA y ((hmemR y).mpr hy) 7 h7A⟩)
            (h1 ▸ hi₀)
        · have h4A : 4 ∈ A := h2 ▸ hPA
          have h7A : 7 ∈ A := h3 ▸ hQA
          exact Cadre.walk_x0 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
            [a, u, v, y2] (by simp) hnd4 hch4 hsl 4 7 (by omega) (by omega) (by omega)
            (by rw [show (4:ℕ) + 1 = i₀ by omega]; exact hi₀)
            (fun t ht => hallA t (hsl t ht) 4 h4A) (fun t ht => hallA t (hsl t ht) 7 h7A)
            (by simp; omega) (by simp)
  ·
    have hr2 : A.card = 3 := by omega
    have hfl := hfull (by omega)
    have hE0 := hEempty (fun y hy i hi' => by rw [hfl y hy]; exact hi')
    omega
lemma Cadre.R4_clique [Nontrivial V] [DecidableRel G.Adj] {x₀ : V} {l : List V}
    (hconn : G.Connected) (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v)
    (hx0 : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v)
    (hδ : ∀ v, 2 ≤ G.degree v) (hne : l ≠ []) (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hmem : x₀ ∈ l) (hhd : l.head hne ≠ x₀) (hlast : l.getLast hne ≠ x₀)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → x₀ ∈ l' → l'.length ≤ l.length)
    (hlt : l.length < Fintype.card V)
    (a b c d : V) (hR : (Finset.univ.filter (fun t => t ∉ l)) = {a, b, c, d}) (hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hadj : G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d)
    (hm : l.length = 2 * secondSmallestDegree G + 2) : False := by
  classical
  by_cases hwl : ∀ i, i < l.length → l.getD i x₀ = x₀ → 2 * i + 1 ≤ l.length
  · exact b24_core hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt a b c d hR hd hadj
      hm hwl
  · obtain ⟨hne', hnd', hch', hmem', hhd', hlast', hmax', hlt'⟩ :=
      Cadre.reverse hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    refine b24_core (l := l.reverse) hconn hb hH hmin hx0 hδ hne' hnd' hch' hmem' hhd' hlast' hmax'
      hlt' a b c d ?_ hd hadj ?_ ?_
    · rw [← hR]; ext t; simp
    · rw [List.length_reverse]; exact hm
    · intro i hi he
      rw [List.length_reverse] at hi ⊢
      rw [Cadre.getD_reverse l x₀ hi] at he
      push Not at hwl
      obtain ⟨j, hj, hjx, hbad⟩ := hwl
      have := b23_getD_inj hnd x₀ (by omega) hj (he.trans hjx.symm)
      omega
lemma b25_hx0 [Nontrivial V] [DecidableRel G.Adj] {x₀ : V}
    (hmin : ∀ v, G.degree x₀ ≤ G.degree v) : ∀ v, v ≠ x₀ → secondSmallestDegree G ≤ G.degree v := by
  intro v hv
  by_contra hlt
  push Not at hlt
  have hlen : 1 < (degreeSequence G).length := by
    simp only [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hsorted : (degreeSequence G).Pairwise (· ≤ ·) := by
    simp [degreeSequence]
  have hb : secondSmallestDegree G = (degreeSequence G)[1] := by
    unfold secondSmallestDegree
    rw [List.getD_eq_getElem _ _ hlen]
  have hle1 : ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length ≤ 1 := by
    rcases hds : degreeSequence G with _ | ⟨a, _ | ⟨b, tail⟩⟩
    · simp [hds] at hlen
    · simp [hds] at hlen
    · have hbb : secondSmallestDegree G = b := by
        simp [secondSmallestDegree, hds]
      rw [hds] at hsorted
      have ht : ∀ t ∈ tail, b ≤ t := by
        intro t ht
        exact (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 t ht
      rw [hbb]
      simp only [List.filter_cons]
      have : tail.filter (fun d => decide (d < b)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro t htt; have := ht t htt; simp; omega
      simp only [this]
      by_cases h1 : a < b <;> simp [h1]
  have hcnt : 2 ≤ (Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G)).card := by
    have h2 : ({x₀, v} : Finset V) ⊆ Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact lt_of_le_of_lt (hmin v) hlt
      · exact hlt
    have := Finset.card_le_card h2
    rwa [Finset.card_pair (Ne.symm hv)] at this
  have heq : ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length
      = (Finset.univ.filter (fun w => G.degree w < secondSmallestDegree G)).card := by
    have hm : (degreeSequence G : Multiset ℕ) = Finset.univ.val.map (fun w => G.degree w) := by
      simp [degreeSequence]
    have := congrArg (fun m : Multiset ℕ => (m.filter (fun d => d < secondSmallestDegree G)).card) hm
    simp only [Multiset.filter_map, Multiset.card_map] at this
    rw [Finset.card_def, Finset.filter_val]
    have h3 : (Multiset.filter (fun d => d < secondSmallestDegree G) (degreeSequence G : Multiset ℕ)).card
        = ((degreeSequence G).filter (fun d => decide (d < secondSmallestDegree G))).length := by
      simp [Multiset.filter_coe]
    rw [← h3]
    simpa [Function.comp_def] using this
  omega
lemma thm_D_all [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hb : ∀ c : V, (G.induce {x | x ≠ c}).Connected)
    (hH : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G)
    (hn1 : 2 * secondSmallestDegree G + 3 ≤ Fintype.card V)
    (hn2 : Fintype.card V ≤ 2 * secondSmallestDegree G + 6) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x₀, hx₀⟩ := G.exists_minimal_degree_vertex
  have hmin : ∀ v, G.degree x₀ ≤ G.degree v := fun v => by
    rw [← hx₀]; exact G.minDegree_le_degree v
  have hx0 := b25_hx0 (G := G) hmin
  have hδ := h11 hconn hH hn1
  rcases Cadre.exists_cadre hconn hH hn1 hmin with ham | ⟨l, hne, hnd, hch, hmem, hhd, hlast, hmax, hlt⟩
  · exact ham
  · exfalso
    have hmg := Cadre.m_ge hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hg3 := Cadre.R_ge3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hrc := Cadre.R_card hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt
    have hcase : (Finset.univ.filter (fun t => t ∉ l)).card = 3 ∨
        (Finset.univ.filter (fun t => t ∉ l)).card = 4 := by omega
    rcases hcase with h3 | h4
    · obtain ⟨u, v, w, hR, huv, hvw, huw, h1, h2, h3'⟩ :=
        Cadre.R3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt h3
      exact Cadre.K3 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt u v w hR huv hvw huw
        h1 h2 h3' (by omega)
    · rcases Cadre.R4 hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt h4 with
        ⟨a, b, c, d, hR, hab, hac, had, hbc, hbd, hcd, h1, h2, h3, h4', h5, h6⟩ |
        ⟨z, z', a, b, hR, h1, h2, h3, h4', h5, h6, hzz, e1, e2, e3, e4⟩
      · exact Cadre.R4_clique hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt a b c d hR
          ⟨hab, hac, had, hbc, hbd, hcd⟩ ⟨h1, h2, h3, h4', h5, h6⟩ (by omega)
      · exact Cadre.R4_nonclique hconn hb hH hmin hx0 hδ hne hnd hch hmem hhd hlast hmax hlt z z' a b hR
          ⟨h1, h2, h3, h4', h5, h6⟩ hzz e1 e2 e3 e4 (by omega)
end Aux
end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2
end
end

section
section
namespace Graph189StepClosure
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
end Graph189StepClosure
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem splice_support (p : G.Walk x y) (hp : p.IsPath)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    ∃ u v, ∃ r : G.Walk u v, r.IsPath ∧ r.support = A ++ q.support ++ B := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  exact ⟨_,_,r,Walk.IsPath.mk' (by rwa [rs]),rs⟩
private theorem kept_gap (p : G.Walk x y) (hp : p.IsPath) (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (kept : p.support[t.val] ∈ A ∨ p.support[t.val] ∈ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  obtain ⟨u,v,r,hr,rs⟩ := splice_support p hp A J B split q hq disjoint left right
  have member : p.support[t.val] ∈ r.support := by
    rw [rs]
    rcases kept with h | h <;> simp [h]
  have cmp := longest r hr member
  have pr := p.length_support
  have qr := r.length_support
  rw [split] at pr
  rw [rs] at qr
  simp only [List.length_append] at pr qr
  omega
private theorem mem_kept_suffix {L : List V} {t i : Fin L.length} (hi : i ≤ t) :
    L[t.val] ∈ L.drop i.val := by
  apply List.mem_drop_iff_getElem.mpr
  have le : i.val ≤ t.val := hi
  exact ⟨t.val-i.val,by have := t.isLt; omega,by simp [Nat.add_sub_of_le le]⟩
private theorem mem_kept_prefix {L : List V} {t i : Fin L.length} (hi : t ≤ i) :
    L[t.val] ∈ L.take (i.val+1) := by
  apply List.mem_take_iff_getElem.mpr
  exact ⟨t.val,lt_min (by change t.val ≤ i.val at hi; omega) t.isLt,rfl⟩
theorem protected_prefix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (hi : i ≤ t) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := kept_gap p hp t longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (Or.inr (mem_kept_suffix hi)) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
theorem protected_suffix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (ht : t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := kept_gap p hp t longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (Or.inl (mem_kept_prefix ht)) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have ilt := i.isLt
  omega
theorem protected_interval_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i < j) (ht : j ≤ t ∨ t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := kept_gap p hp t longest _ _ _ split (ht.elim (fun h => Or.inr (mem_kept_suffix h))
    (fun h => Or.inl (mem_kept_prefix h))) q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def ExteriorRoute (p : G.Walk x y) (a b : V) (k : ℕ) : Prop :=
  ∃ q : G.Walk a b, q.IsPath ∧ List.Disjoint q.support p.support ∧ k ≤ q.support.length
theorem card_outside_add_path [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support) :
    W.card+p.support.length ≤ Fintype.card V := by
  have dis : Disjoint W p.support.toFinset := Finset.disjoint_left.mpr (by
    intro z hz h
    exact outside z hz (List.mem_toFinset.mp h))
  have bound := (W ∪ p.support.toFinset).card_le_univ
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup hp.support_nodup] at bound
  exact bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}
omit [Fintype V] in
theorem route_of_induced_hamilton (p : G.Walk x y) (K : Finset V)
    (outside : ∀ z∈K, z∉p.support) {a b : K}
    {q : (G.induce (K : Set V)).Walk a b} (hq : q.IsHamiltonian) :
    ExteriorRoute p a.val b.val K.card := by
  let e := SimpleGraph.Embedding.induce (G := G) (K : Set V)
  let r := q.map e.toHom
  refine ⟨r, hq.isPath.map e.injective, ?_, ?_⟩
  · rw [List.disjoint_left]
    intro z hz hp
    change z∈(q.map e.toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact outside w.val w.property hp
  · change K.card≤(q.map e.toHom).support.length
    rw [Walk.support_map,List.length_map,hq.length_support]
    simp
end Graph189ExteriorGap
end
section
open Finset
namespace Graph189ExteriorGap
variable {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
theorem hall_on_dense_vertices (neighbors : L → Finset R) (s : ℕ)
    (U : Finset L) (size : U.card=s) (degree : ∀ u∈U, s ≤ (neighbors u).card) :
    ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let links := fun u : U => neighbors u.val
  have h (T : Finset U) : T.card ≤ (T.biUnion links).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have subset : links u ⊆ T.biUnion links := by
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨u,hu,hz⟩
    have small : T.card ≤ U.card := by simpa using T.card_le_univ
    exact (small.trans (size.le.trans (degree u.val u.property))).trans (Finset.card_le_card subset)
  obtain ⟨f,hi,good⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' links).mp h
  exact ⟨⟨f,hi⟩,good⟩
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189ExteriorAttachment
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem marks_of_many_neighbors (p : G.Walk x y) (W : Finset V) (j : ℕ)
    (size : j ≤ W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  obtain ⟨U,uw,us⟩ := exists_subset_card_eq size
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  obtain ⟨f,edges⟩ := Graph189ExteriorGap.hall_on_dense_vertices N j U us (fun w hw => rows w (uw hw))
  let M := (univ : Finset U).image f
  let f' (u : U) : M := ⟨f u,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective f' := by
    constructor
    · intro a b eq; exact f.injective (congrArg Subtype.val eq)
    · intro m
      obtain ⟨u,_,eq⟩ := mem_image.mp m.property
      exact ⟨u,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective f' bij
  let inc : U ↪ W := ⟨fun u => ⟨u.val,uw u.property⟩,
    fun _ _ eq => Subtype.ext (congrArg (fun w : W => w.val) eq)⟩
  have card : M.card = U.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans us,equiv.symm.toEmbedding.trans inc,?_⟩
  intro m
  have eq : f (equiv.symm m) = m.val := congrArg Subtype.val (equiv.apply_symm_apply m)
  have edge := (mem_filter.mp (edges (equiv.symm m))).2
  rw [eq] at edge
  exact edge
end Graph189ExteriorAttachment
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem protected_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    {j m : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) m)
    (before : ∃ a, ExteriorRoute p a (port 0) m)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b m) :
    (j+1)*(m+1) ≤ p.support.length := by
  let pos (i : Fin (j+1)) := (mark i).val + if t < mark i then m else 0
  have first : m ≤ pos 0 := by
    by_cases h : t < mark 0
    · simp [pos,h]
    obtain ⟨a,q,hq,dis,order⟩ := before
    have bound := protected_prefix_of_detour p hp t longest (mark 0) (le_of_not_gt h)
      q hq dis (contacts 0).symm
    simpa [pos,h] using order.trans bound
  have step (i : Fin j) : pos i.castSucc + (m+1) ≤ pos i.succ := by
    have lt := mark.strictMono i.castSucc_lt_succ
    by_cases left : t < mark i.castSucc
    · obtain ⟨q,hq,dis,order⟩ := inner i
      have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inr left.le)
        q hq dis (contacts _) (contacts _).symm
      simp only [pos,if_pos left,if_pos (left.trans lt)]
      omega
    by_cases right : t < mark i.succ
    · simp only [pos,if_neg left,if_pos right]
      change (mark i.castSucc).val < (mark i.succ).val at lt
      omega
    obtain ⟨q,hq,dis,order⟩ := inner i
    have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inl (le_of_not_gt right))
      q hq dis (contacts _) (contacts _).symm
    simp only [pos,if_neg left,if_neg right]
    omega
  have positions (i : Fin (j+1)) : m+i.val*(m+1) ≤ pos i := by
    induction i using Fin.induction with
    | zero => simpa using first
    | succ i ih =>
      have hs := step i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have finish : pos (Fin.last j)+1 ≤ p.support.length := by
    by_cases h : t < mark (Fin.last j)
    · obtain ⟨b,q,hq,dis,order⟩ := after
      have bound := protected_suffix_of_detour p hp t longest _ h.le q hq dis (contacts _)
      simp only [pos,if_pos h]
      omega
    · simpa [pos,h] using (mark (Fin.last j)).isLt
  have last := positions (Fin.last j)
  simp only [Fin.val_last,Nat.succ_mul] at last ⊢
  omega
theorem protected_hamilton_connected_matching [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+1)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := protected_matched_route_order p hp t longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul] at bound ⊢
  omega
theorem protected_order_of_contacts [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath) {z : V} (zp : z ∈ p.support)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → z ∈ r.support → r.length ≤ p.length)
    (W : Finset V) (size : 1 < W.card) (outside : ∀ a ∈ W, a ∉ p.support)
    (hconn : ∀ a b : W, a ≠ b → ∃ q : (G.induce (W : Set V)).Walk a b, q.IsHamiltonian)
    {u : ℕ} (nonzero : 0 < u) (enough : u ≤ W.card)
    (rows : ∀ w ∈ W, u ≤ ((Finset.univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card) :
    (u+1)*W.card+u ≤ Fintype.card V := by
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp zp
  let t : Fin p.support.length := ⟨i,hi⟩
  obtain ⟨marks,card,attach,contacts⟩ :=
    Graph189ExteriorAttachment.marks_of_many_neighbors p W u enough rows
  have bound := protected_hamilton_connected_matching p hp t
    (fun r hr member => longest r hr (e ▸ member)) W size outside hconn marks
      (card_pos.mp (by omega)) attach contacts
  rwa [card] at bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def crossIndices (A B : Finset ℕ) : Finset ℕ :=
  (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) ∪ (B \ A)
noncomputable def contactPositions (p : G.Walk x y) (a : V) : Finset ℕ := by
  classical
  exact (Finset.range p.support.length).filter (fun i => G.Adj (p.getVert i) a)
theorem mem_contactPositions (p : G.Walk x y) (a : V) (i : ℕ) :
    i∈contactPositions p a ↔ i < p.support.length ∧ G.Adj (p.getVert i) a := by
  classical
  simp [contactPositions]
theorem get_at (p : G.Walk x y) {i : ℕ} (hi : i < p.support.length) :
    p.support[i] = p.getVert i := (p.getVert_eq_support_getElem (by
      have := p.length_support
      omega)).symm
theorem two_step_metric {a b z : V} (different : a≠b) (missing : ¬G.Adj a b)
    (az : G.Adj a z) (bz : G.Adj b z) : G.dist a b = 2 := by
  have h := SimpleGraph.edist_eq_two_iff.mpr ⟨different,missing,⟨z,az,bz⟩⟩
  simp [SimpleGraph.dist,h]
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem contact_card_neighbors (p : G.Walk x y) (hp : p.IsPath) (a : V) :
    (contactPositions p a).card = (G.neighborFinset a ∩ p.support.toFinset).card := by
  classical
  have inj : Set.InjOn p.getVert ((contactPositions p a : Finset ℕ) : Set ℕ) := by
    intro i hi j hj h
    have il := ((mem_contactPositions p a i).mp hi).1
    have jl := ((mem_contactPositions p a j).mp hj).1
    have ls := p.length_support
    exact hp.getVert_injOn (by change i ≤ p.length; omega) (by change j ≤ p.length; omega) h
  have eq : (contactPositions p a).image p.getVert = G.neighborFinset a ∩ p.support.toFinset := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have nb := ((mem_contactPositions p a i).mp hi).2.symm
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr nb,List.mem_toFinset.mpr (p.getVert_mem_support i)⟩
    · intro hz
      obtain ⟨hadj,hm⟩ := Finset.mem_inter.mp hz
      have hza := ((G.mem_neighborFinset a z).mp hadj).symm
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hm)
      have eql : p.getVert i=z := (get_at p hi).symm.trans he
      exact Finset.mem_image.mpr ⟨i,(mem_contactPositions p a i).mpr ⟨hi,eql ▸ hza⟩,eql⟩
  rw [←eq,Finset.card_image_of_injOn inj]
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem protected_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  constructor
  · by_contra! zero
    have le : i ≤ t := by change i.val ≤ t.val; omega
    have bound := protected_prefix_of_detour p hp t longest i le q hq hd contact.symm
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega
  · by_contra! last
    have le : t ≤ i := by change t.val ≤ i.val; have := t.isLt; omega
    have bound := protected_suffix_of_detour p hp t longest i le q hq hd contact
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega
theorem protected_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  by_contra! close
  have le : j ≤ t ∨ t ≤ i := by
    change j.val ≤ t.val ∨ t.val ≤ i.val
    change i.val < j.val at ordered
    omega
  have h := protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  simp only [q,Walk.support_nil,List.length_singleton] at h
  omega
theorem protected_cross_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val ∨ i.val+1=t.val ∧ t.val+1=j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  by_cases le : j ≤ t ∨ t ≤ i
  · left
    exact protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  · change ¬(j.val ≤ t.val ∨ t.val ≤ i.val) at le
    omega
private theorem card_protected_cross (A B : Finset ℕ) (t : ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t ∧ t+1=j) ∨ (j+1=t ∧ t+1=i)) :
    A.card+B.card ≤ (crossIndices A B).card+1 := by
  have overlap : ((A.image (fun i => i-1)) ∩ ((A∩B).image (fun i => i+1))) ⊆ {t} := by
    intro v hv
    obtain ⟨i,hi,ei⟩ := mem_image.mp (mem_inter.mp hv).1
    obtain ⟨j,hj,ej⟩ := mem_image.mp (mem_inter.mp hv).2
    have := positive i hi
    have := separated i hi j (mem_inter.mp hj).2
    apply mem_singleton.mpr
    omega
  have loss := Finset.card_le_card overlap
  rw [card_singleton] at loss
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      have := separated i hi t hb
      omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := separated i (Finset.mem_inter.mp hi).1 t hb
      omega
  have inj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj heq
    change i-1=j-1 at heq
    have := positive i hi
    have := positive j hj
    omega
  have cover : (B \ A) ∪ (A∩B) = B := by ext t; simp; tauto
  have dis : Disjoint (B \ A) (A∩B) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).1)
  have hc := Finset.card_union_of_disjoint dis
  rw [cover] at hc
  have total := card_union_add_card_inter (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1))
  rw [card_image_of_injOn inj,card_image_of_injective _
    (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)] at total
  rw [crossIndices,card_union_of_disjoint dis₂]
  omega
theorem protected_cross_indices [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    ((contactPositions p a).card + (contactPositions p b).card ≤
      (crossIndices (contactPositions p a) (contactPositions p b)).card+1) ∧
      ∀ i ∈ crossIndices (contactPositions p a) (contactPositions p b),
        i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact protected_contact_internal p hp t longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) :
      i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t.val ∧ t.val+1=j) ∨ (j+1=t.val ∧ t.val+1=i) := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · have h := protected_cross_spacing p hp t longest ha hb ab ⟨i,ri⟩ ⟨j,rj⟩ lt
        (by simpa [get_at] using ci) (by simpa [get_at] using cj)
      change i+3 ≤ j ∨ i+1=t.val ∧ t.val+1=j at h
      tauto
    · exact Or.inl same
    · have h := protected_cross_spacing p hp t longest hb ha ab.symm ⟨j,rj⟩ ⟨i,ri⟩ gt
        (by simpa [get_at] using cj) (by simpa [get_at] using ci)
      change j+3 ≤ i ∨ j+1=t.val ∧ t.val+1=i at h
      tauto
  have shell (i : ℕ) (hi : i∈crossIndices A B) : i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
    have different (j : ℕ) : a≠p.getVert j := fun eq => ha (eq ▸ p.getVert_mem_support j)
    have ls := p.length_support
    have via (i j : ℕ) (hpi : i < p.support.length) (hj : j∈A) (no : i∉A)
        (ij : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i)=2 := by
      have hc := ((mem_contactPositions p a j).mp hj).2
      exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hpi,h.symm⟩)) hc.symm ij
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨pos,back⟩ := inside j hj
        have inrange : j-1 < p.support.length := by omega
        refine ⟨inrange,via (j-1) j inrange hj (fun hi => ?_) ?_⟩
        · have aux := own (j-1) j hi hj (by omega)
          omega
        · have edge := p.adj_getVert_succ (i := j-1) (by omega)
          rwa [show j-1+1=j by omega] at edge
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have jA := (Finset.mem_inter.mp hj).1
        obtain ⟨_,back⟩ := inside j jA
        refine ⟨back,via (j+1) j back jA (fun hi => ?_) ?_⟩
        · have aux := own j (j+1) jA hi (by omega)
          omega
        · exact (p.adj_getVert_succ (i := j) (by omega)).symm
    · obtain ⟨hB,hA⟩ := Finset.mem_sdiff.mp h
      obtain ⟨ri,ci⟩ := (mem_contactPositions p b i).mp hB
      exact ⟨ri,two_step_metric (different _) (fun h => hA ((mem_contactPositions p a i).mpr ⟨ri,h.symm⟩)) ab ci⟩
  exact ⟨card_protected_cross A B t.val (fun i h => (inside i h).1) separate,shell⟩
theorem protected_cross_positions [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card+1 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  obtain ⟨count,shell⟩ := protected_cross_indices p hp t longest ha hb ab
  have inj : Set.InjOn p.getVert ((crossIndices A B : Finset ℕ) : Set ℕ) := by
    intro i hi j hj same
    exact hp.getVert_injOn (by change i ≤ p.length; have := (shell i hi).1; have := p.length_support; omega)
      (by change j ≤ p.length; have := (shell j hj).1; have := p.length_support; omega) same
  have incl : (crossIndices A B).image p.getVert ⊆ p.support.toFinset.filter (fun z => G.dist a z=2) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),(shell i hi).2⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injOn inj] at bound
  exact count.trans (Nat.add_le_add_right bound 1)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
theorem protected_exterior_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+2+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := protected_cross_positions p hp t longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card+1 at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+2+C.card
  omega
theorem protected_cross_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := protected_exterior_contact_degree p hp t longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+2+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+1+(A \ P).card
  omega
theorem protected_half_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree b) :
    G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1 := by
  have cross := protected_cross_contact_degree p hp t longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1
  omega
omit [Fintype V] [DecidableRel G.Adj] in
theorem protected_single_shell (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact protected_contact_internal p hp t longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let W := insert (m+1) B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_insert.mp hi with rfl|h
    · have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have maxoutside : m+1 ∉ B := by
    intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have lim : i ≤ m := Finset.le_max' _ _ hi
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = insert (m+1) B from rfl,card_insert_of_notMem maxoutside,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj] at count
  exact count
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*}
def terminalAdj (G : SimpleGraph V) (u v : V) : V ⊕ Bool → V ⊕ Bool → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr leaf => a = (if leaf then v else u)
  | .inr leaf, .inl a => a = (if leaf then v else u)
  | .inr _, .inr _ => False
def terminalLeaves (G : SimpleGraph V) (u v : V) : SimpleGraph (V ⊕ Bool) where
  Adj := terminalAdj G u v
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    intro a
    cases a with
    | inl a => exact G.irrefl
    | inr l => exact id
instance terminalDecidable (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (u v : V) :
    DecidableRel (terminalLeaves G u v).Adj := by
  intro a b
  cases a <;> cases b <;> simp only [terminalLeaves,terminalAdj] <;> infer_instance
theorem core_degree_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v z : V) : G.degree z ≤ (terminalLeaves G u v).degree (.inl z) := by
  classical
  have inc : (G.neighborFinset z).image (Sum.inl : V → V ⊕ Bool) ⊆
      (terminalLeaves G u v).neighborFinset (.inl z) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    simp only [SimpleGraph.mem_neighborFinset] at hc ⊢
    exact hc
  have h := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h)] at h
  exact h
theorem terminalLeaves_sup_edge (G : SimpleGraph V) (u v a b : V) :
    terminalLeaves (G ⊔ edge a b) u v =
      terminalLeaves G u v ⊔ edge (.inl a) (.inl b) := by
  ext x y
  cases x <;> cases y <;> simp [terminalLeaves,terminalAdj,SimpleGraph.edge_adj]
theorem leaf_traceable_of_core_edge [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v a b : V) (hne : a≠b) (hab : ¬G.Adj a b)
    (degree : Fintype.card V + 1 ≤ G.degree a + G.degree b)
    (path : ∃ x y, ∃ p : (terminalLeaves (G ⊔ edge a b) u v).Walk x y, p.IsHamiltonian) :
    ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian := by
  rw [terminalLeaves_sup_edge] at path
  apply Graph189StepClosure.traceable_of_sup_edge (G := terminalLeaves G u v) (x := .inl a) (y := .inl b)
  · exact fun h => hne (Sum.inl.inj h)
  · exact hab
  · have ha := core_degree_le G u v a
    have hb := core_degree_le G u v b
    simp only [Fintype.card_sum, Fintype.card_bool]
    omega
  · exact path
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} {G : SimpleGraph V} {u v : V}
theorem neighbor_of_leaf {y : V ⊕ Bool} {l : Bool}
    (h : (terminalLeaves G u v).Adj y (.inr l)) :
    y = .inl (if l then v else u) := by
  cases y with
  | inl y => exact congrArg Sum.inl h
  | inr y => exact False.elim h
theorem leaf_not_interior {a b : V ⊕ Bool} (p : (terminalLeaves G u v).Walk a b)
    (hp : p.IsPath) {i : ℕ} (hpos : 0 < i) (hbefore : i < p.length)
    {l : Bool} (atLeaf : p.getVert i = .inr l) : False := by
  have hi : i-1+1=i := by omega
  have left := p.adj_getVert_succ (i := i-1) (by omega)
  rw [hi,atLeaf] at left
  have right := (p.adj_getVert_succ hbefore).symm
  rw [atLeaf] at right
  have same : p.getVert (i-1) = p.getVert (i+1) :=
    (neighbor_of_leaf left).trans (neighbor_of_leaf right).symm
  have bad : i-1=i+1 := hp.getVert_injOn
      (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) same
  omega
theorem hamiltonian_leaf_at_end [DecidableEq V] {a b : V ⊕ Bool}
    (p : (terminalLeaves G u v).Walk a b) (hp : p.IsHamiltonian) (l : Bool) :
    a = .inr l ∨ b = .inr l := by
  obtain ⟨i,hi⟩ := hp.getVert_surjective (Sum.inr l)
  by_cases hz : i=0
  · left
    simpa [hz] using hi
  by_cases small : i < p.length
  · exact False.elim (leaf_not_interior p hp.isPath (i := i) (Nat.pos_of_ne_zero hz) small hi)
  · right
    rwa [p.getVert_of_length_le (by omega)] at hi
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
private theorem strip_oriented
    (p : (terminalLeaves G u v).Walk (.inr false) (.inr true)) (hp : p.IsHamiltonian) :
    ∃ q : G.Walk u v, q.IsHamiltonian := by
  have nonnil : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have first : p.snd = .inl u := neighbor_of_leaf (p.adj_snd nonnil).symm
  have qnn : ¬p.tail.Nil := Walk.not_nil_of_ne (by rw [first]; simp)
  have last : p.tail.penultimate = .inl v := neighbor_of_leaf (p.tail.adj_penultimate qnn)
  let t := p.tail.dropLast
  have parts : (.inr false) :: (t.support ++ [.inr true]) = p.support := by
    rw [show t.support ++ [.inr true] = p.tail.support from Walk.support_dropLast_concat qnn]
    exact Walk.cons_support_tail nonnil
  have nd := hp.isPath.support_nodup
  rw [←parts] at nd
  have ndf := List.nodup_cons.mp nd
  have core : ∀ z∈t.support, ∃ w : V, z = Sum.inl w := by
    intro z hz
    cases z with
    | inl w => exact ⟨w,rfl⟩
    | inr l =>
      cases l
      · exact (ndf.1 (List.mem_append_left _ hz)).elim
      · exact (List.disjoint_left.mp ndf.2.disjoint hz (by simp)).elim
  let project : V ⊕ Bool → V := Sum.elim id (fun l => if l then v else u)
  let L := t.support.map project
  have hn : L ≠ [] := by simp [L, t.support_ne_nil]
  have chain : L.IsChain G.Adj := by
    apply (List.isChain_map project).2
    apply t.isChain_adj_support.imp_of_mem_imp
    intro a b ha hb hab
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact hab
  have nodup : L.Nodup := by
    apply List.Nodup.map_on _ ndf.2.of_append_left
    intro a ha b hb h
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact congrArg Sum.inl h
  have all (w : V) : w ∈ L := by
    have hw := hp.mem_support (.inl w)
    rw [←parts] at hw
    have hmem : Sum.inl w ∈ t.support := by simpa using hw
    exact List.mem_map.mpr ⟨.inl w,hmem,rfl⟩
  let q := Walk.ofSupport L hn chain
  have qs : q.support = L := Walk.support_ofSupport hn chain
  have qh : q.IsHamiltonian := (Walk.IsPath.mk' (by rwa [qs])).isHamiltonian_of_mem
    (fun w => by rw [qs]; exact all w)
  have hstart : L.head hn = u := by
    simp [L,List.head_map,t,project,first]
  have hfinish : L.getLast hn = v := by
    simp [L,List.getLast_map,t,project,last]
  exact ⟨q.copy hstart hfinish, fun w => by simpa [Walk.support_copy] using qh w⟩
theorem prescribed_of_leaf_traceable
    (path : ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨x,y,p,hp⟩ := path
  rcases hamiltonian_leaf_at_end p hp false with hx | hy
  · subst x
    rcases hamiltonian_leaf_at_end p hp true with hf | hy
    · simp at hf
    · subst y
      exact strip_oriented p hp
  · subst y
    rcases hamiltonian_leaf_at_end p hp true with hx | hf
    · subst x
      apply strip_oriented p.reverse
      intro w
      simpa using hp w
    · simp at hf
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
def oldEmbedding (G : SimpleGraph V) (u v : V) : G →g terminalLeaves G u v where
  toFun := Sum.inl
  map_rel' := fun h => h
theorem leaf_traceable_of_prescribed {p : G.Walk u v} (hp : p.IsHamiltonian) :
    ∃ x y, ∃ q : (terminalLeaves G u v).Walk x y, q.IsHamiltonian := by
  let h₁ : (terminalLeaves G u v).Adj (.inr false) (.inl u) := rfl
  let h₂ : (terminalLeaves G u v).Adj (.inl v) (.inr true) := rfl
  let q := Walk.cons h₁ ((p.map (oldEmbedding G u v)).concat h₂)
  have qs : q.support = Sum.inr false :: (p.support.map Sum.inl ++ [Sum.inr true]) := by
    simp [q,oldEmbedding]
    intro a ha
    rfl
  have mapped : (p.support.map (Sum.inl : V → V⊕Bool)).Nodup :=
    hp.isPath.support_nodup.map (fun _ _ h => Sum.inl.inj h)
  have nd : q.support.Nodup := by
    rw [qs]
    simp [List.nodup_append',mapped]
  refine ⟨_,_,q,(Walk.IsPath.mk' nd).isHamiltonian_of_mem ?_⟩
  intro w
  rw [qs]
  cases w with
  | inl z => simp [hp.mem_support z]
  | inr l => cases l <;> simp
theorem prescribed_of_sup_edge [Fintype V] [DecidableRel G.Adj] {a b : V}
    (distinct : a≠b) (missing : ¬G.Adj a b)
    (degree : Fintype.card V+1 ≤ G.degree a+G.degree b)
    (path : ∃ p : (G⊔edge a b).Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨p,hp⟩ := path
  exact prescribed_of_leaf_traceable (leaf_traceable_of_core_edge G u v a b distinct missing degree
    (leaf_traceable_of_prescribed hp))
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem prescribed_of_supergraph {G H : SimpleGraph V} [DecidableRel G.Adj] (incl : G ≤ H)
    (degree : ∀ a b, H.Adj a b → ¬G.Adj a b → Fintype.card V+1 ≤ G.degree a+G.degree b)
    {u v : V} (path : ∃ p : H.Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  suffices all : ∀ J : SimpleGraph V, G ≤ J → J ≤ H → ∃ p : J.Walk u v, p.IsHamiltonian by
    exact all G le_rfl incl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro lower upper
    by_cases eq : J=H
    · subst J
      exact path
    have missing : ∃ a b, H.Adj a b ∧ ¬J.Adj a b := by
      by_contra! all
      exact eq (le_antisymm upper fun a b hab => all a b hab)
    obtain ⟨a,b,hab,hnot⟩ := missing
    have hEdge : edge a b ≤ H := by
      intro i j hij
      obtain ⟨h,_⟩ := (edge_adj a b i j).mp hij
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hab
      · exact hab.symm
    have strict : J < J⊔edge a b := by
      apply lt_of_le_of_ne le_sup_left
      intro same
      have key : (J⊔edge a b).Adj a b := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩)
      exact hnot (same.symm ▸ key)
    apply prescribed_of_sup_edge hab.ne hnot _ (ih _ strict (lower.trans le_sup_left) (sup_le upper hEdge))
    exact (degree _ _ hab (fun h => hnot (lower h))).trans
      (Nat.add_le_add (degree_le_of_le (v := a) lower) (degree_le_of_le (v := b) lower))
theorem complete_prescribed (u v : V) (hne : u ≠ v) :
    ∃ p : (⊤ : SimpleGraph V).Walk u v, p.IsHamiltonian := by
  classical
  let M := ((Finset.univ.erase u).erase v).toList
  let L := u :: (M ++ [v])
  have nd : L.Nodup := by
    simp [L,M,List.nodup_append',Finset.nodup_toList,hne]
  have chain : L.IsChain (⊤ : SimpleGraph V).Adj := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y A B eq
    apply (top_adj _ _).mpr
    intro same
    subst y
    rw [eq] at nd
    have tail := nd.of_append_right
    exact (List.nodup_cons.mp tail).1 (by simp)
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn chain
  have ps : p.support = L := Walk.support_ofSupport hn chain
  have ph : p.IsHamiltonian := (Walk.IsPath.mk' (by rwa [ps])).isHamiltonian_of_mem (by
    intro z
    rw [ps]
    by_cases hzu : z=u
    · simp [L,hzu]
    by_cases hzv : z=v <;> simp [L,M,hzu,hzv])
  have hs : L.head hn = u := by simp [L]
  have he : L.getLast hn = v := by simp [L]
  exact ⟨p.copy hs he, fun z => by simpa [Walk.support_copy] using ph z⟩
end Graph189TerminalLeafClosure
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
theorem degree_induce_filter {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (S : Set V) [Fintype S] [DecidablePred (· ∈ S)] (x : S) :
    (G.induce S).degree x = ((G.neighborFinset x.val).filter (fun v => v ∈ S)).card := by
  classical
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have same : ((G.induce S).neighborFinset x).map f =
      (G.neighborFinset x.val).filter (fun y => y ∈ S) := by
    ext y
    constructor
    · intro hy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hy
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (((G.induce S).mem_neighborFinset _ _).mp hu),u.property⟩
    · intro hy
      obtain ⟨he,hs⟩ := mem_filter.mp hy
      exact mem_map.mpr ⟨⟨y,hs⟩,((G.induce S).mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp he),rfl⟩
  have card := congrArg Finset.card same
  rwa [card_map,(G.induce S).card_neighborFinset_eq_degree] at card
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Finset Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem protected_exterior_minimum (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (x : (p.support.toFinsetᶜ : Finset V)) :
    G.secondSmallestDegree / 2 ≤ (G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).degree x := by
  classical
  let P := p.support.toFinset
  let E := Pᶜ
  let k := G.secondSmallestDegree
  have quota (v : V) : (univ.filter (fun y => G.dist v y = 2)).card ≤ k := by
    let T := univ.filter (fun y => G.dist v y = 2)
    have miss : v ∉ T := by simp [T]
    have sub : insert v T ⊆ univ.filter (fun y => Even (G.dist v y)) := by
      intro y hy
      rcases mem_insert.mp hy with rfl | h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
    have h := card_le_card sub
    rw [card_insert_of_notMem miss] at h
    change T.card+1 ≤ G.distEven v at h
    have capv := cap v
    change G.distEven v ≤ k+1 at capv
    change T.card ≤ k
    omega
  have high {v : V} (out : v ∉ p.support) : k ≤ G.degree v := by
    have ne : v ≠ p.support[t.val] := fun h => out (h ▸ List.getElem_mem _)
    exact (degree_pair (G:=G) v _ ne).resolve_right (Nat.not_le.mpr low)
  have outside : x.val ∉ p.support := fun h => (mem_compl.mp x.property) (List.mem_toFinset.mpr h)
  have gram : ((G.neighborFinset x.val).filter (fun u => u ∈ (E : Set V))) = G.neighborFinset x.val \ P := by
    ext v
    simp [E]
  change k/2 ≤ (G.induce (E : Set V)).degree x
  rw [degree_induce_filter,gram]
  obtain ⟨y,hy⟩ : (G.neighborFinset x.val \ P).Nonempty := by
    apply Classical.byContradiction
    intro empty
    have sub : G.neighborFinset x.val ⊆ P := by
      intro v hv
      by_contra out
      exact empty ⟨v,mem_sdiff.mpr ⟨hv,out⟩⟩
    have eq : (contactPositions p x.val).card = G.degree x.val := by
      rw [contact_card_neighbors p hp]
      change (G.neighborFinset x.val ∩ P).card = G.degree x.val
      rw [inter_eq_left.mpr sub, G.card_neighborFinset_eq_degree]
    have hx := high outside
    have pos : (contactPositions p x.val).Nonempty := card_pos.mp (by change _ < k at low; omega)
    have shift := protected_single_shell p hp t longest outside pos
    have shell : P.filter (fun y => G.dist x.val y=2) ⊆ univ.filter (fun y => G.dist x.val y=2) :=
      filter_subset_filter _ (subset_univ _)
    have count := (card_le_card shell).trans (quota _)
    change (contactPositions p x.val).card + 1 ≤ (P.filter _).card at shift
    omega
  have outy : y ∉ p.support := fun h => (mem_sdiff.mp hy).2 (List.mem_toFinset.mpr h)
  have bound := protected_half_degree p hp t longest outside outy
    ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1) (quota _) (high outy)
  have := high outside
  change G.degree x.val ≤ 2*(G.neighborFinset x.val \ P).card+1 at bound
  omega
theorem protected_exterior_hamilton_connected (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (room : (p.support.toFinsetᶜ : Finset V).card + 2 ≤ G.secondSmallestDegree)
    (x y : (p.support.toFinsetᶜ : Finset V)) (ne : x ≠ y) :
    ∃ q : (G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).Walk x y, q.IsHamiltonian := by
  classical
  let E := p.support.toFinsetᶜ
  let H := G.induce (E : Set V)
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _ (Graph189TerminalLeafClosure.complete_prescribed x y ne)
  intro i j _ _
  have hi := protected_exterior_minimum p hp t longest low cap i
  have hj := protected_exterior_minimum p hp t longest low cap j
  change G.secondSmallestDegree / 2 ≤ H.degree i at hi
  change G.secondSmallestDegree / 2 ≤ H.degree j at hj
  change E.card+2 ≤ _ at room
  change Fintype.card E+1 ≤ H.degree i + H.degree j
  rw [Fintype.card_coe]
  omega
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189DenseExteriorOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {x y : V}
theorem neighbors_on_path (p : G.Walk x y) (W : Finset V)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    {w : V} (hw : w ∈ W) :
    G.degree w+1 ≤ W.card+((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card := by
  classical
  let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let P := R.image (fun i => p.support[i.val])
  have sub : insert w (G.neighborFinset w) ⊆ W ∪ P := by
    intro v hv
    rcases mem_insert.mp hv with rfl | h
    · exact mem_union_left _ hw
    have edge := (G.mem_neighborFinset _ _).mp h
    by_cases vw : v ∈ W
    · exact mem_union_left _ vw
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (boundary w hw v edge vw)
    exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,
      mem_filter.mpr ⟨mem_univ _,by simpa only [eq] using edge.symm⟩,eq⟩)
  have h := (card_le_card sub).trans (card_union_le W P)
  rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
  exact h.trans (Nat.add_le_add_left card_image_le _)
end Graph189DenseExteriorOrder
end
section
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem protected_contact_witness (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → p.support[t.val] ∈ q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (omits : (p.support.toFinsetᶜ : Finset V).Nonempty)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree)
    (room : (p.support.toFinsetᶜ : Finset V).card+s ≤ G.secondSmallestDegree+1) :
    let m := (p.support.toFinsetᶜ : Finset V).card
    let u := G.secondSmallestDegree+1-m
    u ≤ m ∧ (u+1)*m+u ≤ Fintype.card V ∧
      ∀ v ∈ (p.support.toFinsetᶜ : Finset V), u ≤ ((univ : Finset (Fin p.support.length)).filter
        (fun i => G.Adj p.support[i.val] v)).card := by
  classical
  let E := p.support.toFinsetᶜ
  let m := E.card
  let k := G.secondSmallestDegree
  let u := k+1-m
  change m+s ≤ k+1 at room
  change 2*s ≤ k at small
  obtain ⟨v,hv⟩ := omits
  let w : E := ⟨v,hv⟩
  have half := protected_exterior_minimum p hp t longest low cap w
  have upper := (G.induce (E : Set V)).degree_lt_card_verts w
  change (G.induce (E : Set V)).degree w < Fintype.card E at upper
  rw [Fintype.card_coe] at upper
  change _ < m at upper
  change k/2 ≤ (G.induce (E : Set V)).degree w at half
  have enough : u ≤ m := by dsimp [u]; omega
  have su : s ≤ u := by dsimp [u]; omega
  have sm : s ≤ m := by omega
  have sum : m+u=k+1 := by dsimp [u]; omega
  have outside {v : V} (hv : v ∈ E) : v ∉ p.support :=
    fun h => (mem_compl.mp hv) (List.mem_toFinset.mpr h)
  have boundary (w : V) (_ : w ∈ E) (v : V) (_ : G.Adj w v) (hv : v ∉ E) : v ∈ p.support := by
    simpa [E] using hv
  have rows (v : V) (hv : v ∈ E) : u ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] v)).card := by
    have ne : v ≠ p.support[t.val] := fun eq => outside hv (eq ▸ List.getElem_mem _)
    have high := (degree_pair (G:=G) v _ ne).resolve_right (not_le.mpr low)
    have d := Graph189DenseExteriorOrder.neighbors_on_path p E boundary hv
    change k ≤ G.degree v at high
    change G.degree v+1 ≤ m+_ at d
    omega
  have bound := protected_order_of_contacts p hp (List.getElem_mem (l:=p.support) t.isLt) longest E
    (by change 1 < m; omega) (fun _ hv => outside hv)
    (protected_exterior_hamilton_connected p hp t longest low cap (by change m+2 ≤ k; omega))
    (by omega : 0 < u) enough rows
  exact ⟨enough,bound,rows⟩
theorem protected_order_of_exterior_size (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → p.support[t.val] ∈ q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (omits : (p.support.toFinsetᶜ : Finset V).Nonempty)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree)
    (room : (p.support.toFinsetᶜ : Finset V).card+s ≤ G.secondSmallestDegree+1) :
    (s+1)*(G.secondSmallestDegree-s+2) ≤ Fintype.card V+1 := by
  let m := (p.support.toFinsetᶜ : Finset V).card
  let k := G.secondSmallestDegree
  let u := k+1-m
  obtain ⟨enough,bound,_⟩ := protected_contact_witness p hp t longest low cap omits s3 small room
  change m+s ≤ k+1 at room
  change 2*s ≤ k at small
  change u ≤ m at enough
  change (u+1)*m+u ≤ Fintype.card V at bound
  have su : s ≤ u := by dsimp [u]; omega
  have sm : s ≤ m := by omega
  have sum : m+u=k+1 := by dsimp [u]; omega
  change (s+1)*(k-s+2) ≤ Fintype.card V+1
  zify [show s ≤ k by omega] at bound sum ⊢
  have x : 0 ≤ (m:ℤ)-s := by omega
  have y : 0 ≤ (u:ℤ)-s := by omega
  nlinarith only [bound,mul_nonneg x y,sum,congrArg (fun i : ℤ => (s:ℤ)*i) sum]
end Graph189ExteriorGap
end
end

section
namespace Graph189LowDegreeTwo
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem two_edges {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hne : a ≠ c) (hn : ¬ G.Adj a c) : G.dist a c = 2 := by
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  have hp : G.dist a c ≤ 2 := by simpa [p] using G.dist_le p
  have hpos : 0 < G.dist a c := Nat.pos_of_ne_zero
    (fun h => hne (p.reachable.dist_eq_zero_iff.mp h))
  have hone : G.dist a c ≠ 1 := fun h => hn (dist_eq_one_iff_adj.mp h)
  omega
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem split_two (h : G.Connected) {a c : V} (hd : G.dist a c = 2) :
    ∃ b, G.Adj a b ∧ G.Adj b c := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a c
  rw [hd] at hp
  have h1 := p.adj_getVert_succ (i := 0) (by omega)
  have h2 := p.adj_getVert_succ (i := 1) (by omega)
  rw [Walk.getVert_zero] at h1
  rw [show 1+1 = p.length by omega, Walk.getVert_length] at h2
  exact ⟨p.getVert 1,h1,h2⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem split_three (h : G.Connected) {a c : V} (hd : G.dist a c = 3) :
    ∃ b, G.dist a b = 2 ∧ G.Adj b c := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a c
  rw [hd] at hp
  let b := p.getVert 2
  have hstep := p.adj_getVert_succ (i := 2) (by omega)
  rw [show 2+1 = p.length by omega, Walk.getVert_length] at hstep
  have hle : G.dist a b ≤ 2 := (G.dist_le (p.take 2)).trans (by simp [Walk.take_length])
  have htri := h.dist_triangle (u := a) (v := b) (w := c)
  rw [hd,dist_eq_one_iff_adj.mpr hstep] at htri
  exact ⟨b,by omega,hstep⟩
end Graph189LowDegreeTwo
end

section
namespace Graph189DegreeTwoOuter
open SimpleGraph Graph189LowDegreeTwo
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Nontrivial V] [DecidableRel G.Adj] in
theorem distance_two_cap (s : ℕ) (hσ : ∀ x, G.distEven x ≤ 1 + s) (x : V) :
    (Finset.univ.filter (fun v => G.dist x v = 2)).card ≤ s := by
  let D := Finset.univ.filter (fun v => G.dist x v = 2)
  have hsub : insert x D ⊆ Finset.univ.filter (fun v => Even (G.dist x v)) := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp hv with rfl | hmem
    · simp
    · exact (Finset.mem_filter.mp hmem).2 ▸ (by decide : Even 2)
  have hne : x ∉ D := by simp [D]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hne] at hle
  change D.card + 1 ≤ G.distEven x at hle
  change D.card ≤ s
  have h := hσ x
  omega
theorem large_nonadjacent_layout (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree)
    (hn : 2 * G.secondSmallestDegree + 4 ≤ Fintype.card V)
    (z a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b})
    (hab : ¬ G.Adj a b) :
    let W := Finset.univ.filter (fun v => G.dist z v = 2)
    let R := Finset.univ.filter (fun v => G.dist z v = 3)
    W.card + R.card + 3 = Fintype.card V ∧
    W.card = G.secondSmallestDegree ∧ G.secondSmallestDegree + 1 ≤ R.card ∧
      G.degree a = G.secondSmallestDegree ∧ G.degree b = G.secondSmallestDegree ∧
        ∃ p ∈ W, ∃ q ∈ W, p ≠ q ∧
          (∀ x ∈ W, G.Adj a x ↔ x ≠ p) ∧ (∀ x ∈ W, G.Adj b x ↔ x ≠ q) ∧
          2 ≤ (R.filter (fun x => G.dist a x = 3)).card ∧
          2 ≤ (R.filter (fun x => G.dist b x = 3)).card := by
  classical
  have := h.nonempty
  let s := G.secondSmallestDegree
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  intro W' R'
  change W.card + R.card + 3 = Fintype.card V ∧ W.card = s ∧ s + 1 ≤ R.card ∧ _
  have hza : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have hzb : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have mW (x) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have ds (x y : V) : G.dist x y ≤ 3 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := x) (v := y)).trans hd
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hc : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by
      have := ds z x
      omega
    rcases hc with h0 | h1 | h2 | h3
    · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
    · have hNx := (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)
      simpa [hZ,or_assoc] using
        (Or.inr (Or.inl hNx) : x = z ∨ x ∈ G.neighborFinset z ∨ x ∈ W ∨ x ∈ R)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((mW x).mpr h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((mR x).mpr h3))))
  have hun : insert z (({a,b} : Finset V) ∪ W ∪ R) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton,Finset.mem_univ,iff_true]
    have hx := all x
    tauto
  have hT (x : V) (hx : x ∈ ({a,b} : Finset V)) : G.dist z x = 1 :=
    dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset z x).mp (hZ.symm ▸ hx))
  have hdisW : Disjoint ({a,b} : Finset V) W := by
    refine Finset.disjoint_left.mpr (fun x hx hw => ?_)
    have := hT x hx
    have := (mW x).mp hw
    omega
  have hdisR : Disjoint (({a,b} : Finset V) ∪ W) R := by
    refine Finset.disjoint_left.mpr (fun x hx hr => ?_)
    have := (mR x).mp hr
    rcases Finset.mem_union.mp hx with ht | hw
    · have := hT x ht
      omega
    · have := (mW x).mp hw
      omega
  have hzEmpty : z ∉ (({a,b} : Finset V) ∪ W ∪ R) := by
    simp [mW,mR, G.ne_of_adj hza, G.ne_of_adj hzb]
  have hL := congrArg Finset.card hun
  rw [Finset.card_insert_of_notMem hzEmpty,Finset.card_union_of_disjoint hdisR,
    Finset.card_union_of_disjoint hdisW,Finset.card_pair hne,Finset.card_univ] at hL
  have hOrder : W.card + R.card + 3 = Fintype.card V := by omega
  have hWcap : W.card ≤ s := distance_two_cap s hσ z
  have hRsize : s + 1 ≤ R.card := by change 2*s+4 ≤ Fintype.card V at hn; omega
  have reachW (r : V) (hr : r ∈ R) : ∃ w ∈ W, G.Adj w r := by
    obtain ⟨w,hw,hwr⟩ := split_three h ((mR r).mp hr)
    exact ⟨w,(mW w).mpr hw,hwr⟩
  have remoteNo {u r : V} (hu : G.Adj z u) (hr : r ∈ R) : ¬ G.Adj u r := by
    intro her
    have ht := h.dist_triangle (u := z) (v := u) (w := r)
    rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr her] at ht
    omega
  have countMiss {u v : V} (hu : G.Adj z u) (hv : G.Adj z v) (huv : u ≠ v)
      (hnuv : ¬ G.Adj u v) (hAll : ∀ x, x = z ∨ x = u ∨ x = v ∨ x ∈ W ∨ x ∈ R) :
      W.card = s ∧ G.degree u = s ∧
        (∃ p ∈ W, ∀ x ∈ W, G.Adj u x ↔ x ≠ p) ∧
          2 ≤ (R.filter (fun x => G.dist u x = 3)).card := by
    have hug : s ≤ G.degree u :=
      (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair u z (G.ne_of_adj hu.symm)).resolve_right (by
        change ¬ s ≤ G.degree z
        rw [hzd]
        exact Nat.not_le.mpr hs)
    have unear (r : V) (hr : r ∈ R) : G.dist u r = 2 ∨ G.dist u r = 3 := by
      have hur : u ≠ r := by
        intro he
        have hm := (mR r).mp hr
        rw [← he,dist_eq_one_iff_adj.mpr hu] at hm
        contradiction
      have hp : 0 < G.dist u r := h.pos_dist_of_ne hur
      have hn : G.dist u r ≠ 1 := fun e => remoteNo hu hr (dist_eq_one_iff_adj.mp e)
      have hm := ds u r
      omega
    let D := R.filter (fun x => G.dist u x = 2)
    have vNotR : v ∉ R := by simp [mR,dist_eq_one_iff_adj.mpr hv]
    have hDcap : D.card + 1 ≤ s := by
      have hsub : insert v D ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with e | hh
        · subst x
          simp [two_edges hu.symm hv huv hnuv]
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hh).2⟩
      have hle := (Finset.card_le_card hsub).trans (distance_two_cap s hσ u)
      rwa [Finset.card_insert_of_notMem (fun h => vNotR (Finset.mem_filter.mp h).1)] at hle
    let F := R.filter (fun x => G.dist u x = 3)
    have hpart : D ∪ F = R := by
      ext x
      simp only [D,F,Finset.mem_union,Finset.mem_filter]
      constructor
      · exact fun he => he.elim And.left And.left
      · intro hx
        exact (unear x hx).imp (fun he => ⟨hx,he⟩) (fun he => ⟨hx,he⟩)
    have hF : 2 ≤ F.card := by
      have hh := Finset.card_union_le D F
      rw [hpart] at hh
      omega
    obtain ⟨r,hr⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    obtain ⟨p,hpW,hpr⟩ := reachW r (Finset.mem_filter.mp hr).1
    have hMiss : ¬ G.Adj u p := by
      intro hup
      have ht := h.dist_triangle (u := u) (v := p) (w := r)
      rw [(Finset.mem_filter.mp hr).2,dist_eq_one_iff_adj.mpr hup,dist_eq_one_iff_adj.mpr hpr] at ht
      omega
    let J := W.filter (G.Adj u)
    have hNJ : G.neighborFinset u = insert z J := by
      ext x
      rw [G.mem_neighborFinset]
      simp only [Finset.mem_insert,Finset.mem_filter,J]
      constructor
      · intro he
        rcases hAll x with rfl | rfl | rfl | hw | hr
        · exact Or.inl rfl
        · exact (G.irrefl he).elim
        · exact (hnuv he).elim
        · exact Or.inr ⟨hw,he⟩
        · exact (remoteNo hu hr he).elim
      · exact fun hh => hh.elim (fun he => he.symm ▸ hu.symm) And.right
    have hzJ : z ∉ J := by simp [J,mW]
    have hJ : J.card + 1 = G.degree u := by
      rw [← Finset.card_insert_of_notMem hzJ,← hNJ,G.card_neighborFinset_eq_degree]
    have hpJ : p ∉ J := fun hm => hMiss (Finset.mem_filter.mp hm).2
    have hIJ : insert p J ⊆ W := by
      intro x hx
      rcases Finset.mem_insert.mp hx with he | hm
      · exact he.symm ▸ hpW
      · exact (Finset.mem_filter.mp hm).1
    have hPM := Finset.card_le_card hIJ
    rw [Finset.card_insert_of_notMem hpJ] at hPM
    have hW' : W.card = s := by omega
    have hu' : G.degree u = s := by omega
    have hIW := Finset.eq_of_subset_of_card_le hIJ (by
      rw [Finset.card_insert_of_notMem hpJ]; omega)
    have hUnique (x : V) (hx : x ∈ W) : G.Adj u x ↔ x ≠ p := by
      constructor
      · exact fun hadj he => hMiss (he ▸ hadj)
      · intro he
        have hx' := hIW.symm ▸ hx
        exact (Finset.mem_filter.mp ((Finset.mem_insert.mp hx').resolve_left he)).2
    exact ⟨hW',hu',⟨p,hpW,hUnique⟩,hF⟩
  have all' (x : V) : x = z ∨ x = b ∨ x = a ∨ x ∈ W ∨ x ∈ R := by
    simpa [or_comm,or_left_comm,or_assoc] using all x
  obtain ⟨hw,ha,⟨p,hp,hap⟩,hra⟩ := countMiss hza hzb hne hab all
  obtain ⟨_,hb,⟨q,hq,hbq⟩,hrb⟩ := countMiss hzb hza hne.symm (fun e => hab e.symm) all'
  have hpq : p ≠ q := by
    intro he
    obtain ⟨u,hzu,hup⟩ := split_two h ((mW p).mp hp)
    have hu : u = a ∨ u = b := by simpa [hZ] using (G.mem_neighborFinset z u).mpr hzu
    rcases hu with ea | eb
    · exact (hap p hp).mp (ea ▸ hup) rfl
    · exact (hbq p hp).mp (eb ▸ hup) he
  exact ⟨hOrder,hw,hRsize,ha,hb,p,hp,q,hq,hpq,hap,hbq,hra,hrb⟩
omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
theorem remote_unique_middle (h : G.Connected) {z u p r : V}
    (hr : G.dist z r = 3) (hur : G.dist u r = 3)
    (hmiss : ∀ x : V, G.dist z x = 2 → (G.Adj u x ↔ x ≠ p)) :
    G.Adj p r ∧ ∀ x : V, G.dist z x = 2 → G.Adj x r → x = p := by
  have only (x : V) (hx : G.dist z x = 2) (hxr : G.Adj x r) : x = p := by
    by_contra hne
    have hux := (hmiss x hx).mpr hne
    have ht := h.dist_triangle (u := u) (v := x) (w := r)
    rw [hur,dist_eq_one_iff_adj.mpr hux,dist_eq_one_iff_adj.mpr hxr] at ht
    omega
  obtain ⟨x,hx,hxr⟩ := split_three h hr
  exact ⟨only x hx hxr ▸ hxr,only⟩
theorem not_order_ten_of_nonadjacent (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 3)
    (z a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b})
    (hab : ¬ G.Adj a b) :
    Fintype.card V ≠ 10 := by
  classical
  intro hn
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  have hza : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have hzb : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have hL := large_nonadjacent_layout h hd hσ (by omega) (by omega)
    z a b hne hZ hab
  change W.card + R.card + 3 = Fintype.card V ∧ W.card = G.secondSmallestDegree ∧ _ at hL
  obtain ⟨hOrder,hW,_,_,_,p,hp,q,hq,hpq,hap,hbq,hRa,hRb⟩ := hL
  have hWcard : W.card = 3 := hW.trans hs
  have hRcard : R.card = 4 := by omega
  have mW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  let X := R.filter (fun x => G.dist a x = 3)
  let Y := R.filter (fun x => G.dist b x = 3)
  change 2 ≤ X.card at hRa
  change 2 ≤ Y.card at hRb
  have hxOnly {r : V} (hr : r ∈ X) :
      G.Adj p r ∧ ∀ x ∈ W, G.Adj x r → x = p := by
    obtain ⟨hr',ha⟩ := Finset.mem_filter.mp hr
    obtain ⟨hp',hu⟩ := remote_unique_middle h ((mR r).mp hr') ha
      (fun x hx => hap x ((mW x).mpr hx))
    exact ⟨hp',fun x hx => hu x ((mW x).mp hx)⟩
  have hyOnly {r : V} (hr : r ∈ Y) :
      G.Adj q r ∧ ∀ x ∈ W, G.Adj x r → x = q := by
    obtain ⟨hr',ha⟩ := Finset.mem_filter.mp hr
    obtain ⟨hq',hu⟩ := remote_unique_middle h ((mR r).mp hr') ha
      (fun x hx => hbq x ((mW x).mpr hx))
    exact ⟨hq',fun x hx => hu x ((mW x).mp hx)⟩
  have hdis : Disjoint X Y := by
    refine Finset.disjoint_left.mpr ?_
    intro r hrX hrY
    exact hpq ((hyOnly hrY).2 p hp (hxOnly hrX).1)
  have hcoverR : X ∪ Y = R := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
    rw [Finset.card_union_of_disjoint hdis,hRcard]
    omega
  have hWdiff : 0 < ((W.erase p).erase q).card := by
    have hq' : q ∈ W.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hq⟩
    rw [Finset.card_erase_of_mem hq',Finset.card_erase_of_mem hp,hWcard]
    decide
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hWdiff
  have hcq : c ≠ q := Finset.ne_of_mem_erase hc
  have hcp : c ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcW : c ∈ W := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hWcover : ({p,q,c} : Finset V) = W := by
    apply Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases (show x = p ∨ x = q ∨ x = c from by simpa using hx) with e | e | e
      · exact e.symm ▸ hp
      · exact e.symm ▸ hq
      · exact e.symm ▸ hcW
    · rw [hWcard]
      simp [Finset.card_insert_of_notMem,hpq,hcp.symm,hcq.symm]
  have remote_adj (v r : V) (hv : G.Adj z v) (hr : r ∈ R) : ¬ G.Adj v r := by
    intro hvr
    have ht := h.dist_triangle (u := z) (v := v) (w := r)
    rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hv,dist_eq_one_iff_adj.mpr hvr] at ht
    omega
  have reserve {u v p q : V} {D : Finset V} (hu : G.Adj z u) (hv : G.Adj z v)
      (huv : u ≠ v) (hnuv : ¬ G.Adj u v)
      (hpW : p ∈ W) (hup : ¬ G.Adj u p) (huc : G.Adj u c)
      (huq : G.Adj u q) (hD : 2 ≤ D.card) (hDR : D ⊆ R)
      (hDq : ∀ r ∈ D, G.Adj q r) :
      ¬ G.Adj c p := by
    intro hcAdj
    have hnep : u ≠ p := by
      intro he
      have h := (mW p).mp hpW
      rw [← he,dist_eq_one_iff_adj.mpr hu] at h
      contradiction
    have ph : G.dist u p = 2 := two_edges huc hcAdj hnep hup
    have vh : G.dist u v = 2 := two_edges hu.symm hv huv hnuv
    have hnear (r : V) (hr : r ∈ D) : G.dist u r = 2 := by
      have hr' := hDR hr
      have hne : u ≠ r := by
        intro he
        have h := (mR r).mp hr'
        rw [← he,dist_eq_one_iff_adj.mpr hu] at h
        contradiction
      exact two_edges huq (hDq r hr) hne (remote_adj u r hu hr')
    have hsub : insert p (insert v D) ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with e | hm
      · subst x; simp [ph]
      · rcases Finset.mem_insert.mp hm with e | hd'
        · subst x; simp [vh]
        · simp [hnear x hd']
    have hvD : v ∉ D := fun he => by
      have hh := (mR v).mp (hDR he)
      rw [dist_eq_one_iff_adj.mpr hv] at hh
      contradiction
    have hpD : p ∉ insert v D := by
      intro he
      rcases Finset.mem_insert.mp he with eq | hm
      · have hh := (mW p).mp hpW
        rw [eq,dist_eq_one_iff_adj.mpr hv] at hh
        contradiction
      · have hp' := (mW p).mp hpW
        have hp'' := (mR p).mp (hDR hm)
        omega
    have hl := (Finset.card_le_card hsub).trans (distance_two_cap _ hσ u)
    rw [Finset.card_insert_of_notMem hpD,Finset.card_insert_of_notMem hvD] at hl
    omega
  have hcpN : ¬ G.Adj c p := reserve hza hzb hne hab hp (fun e => (hap p hp).mp e rfl)
    ((hap c hcW).mpr hcp) ((hap q hq).mpr hpq.symm) hRb
    (Finset.filter_subset _ _) (fun _ hr => (hyOnly hr).1)
  have hcqN : ¬ G.Adj c q := reserve hzb hza hne.symm (fun e => hab e.symm) hq
    (fun e => (hbq q hq).mp e rfl) ((hbq c hcW).mpr hcq) ((hbq p hp).mpr hpq) hRa
    (Finset.filter_subset _ _) (fun _ hr => (hxOnly hr).1)
  have hcR (r : V) (hr : r ∈ R) : ¬ G.Adj c r := by
    intro he
    rw [← hcoverR] at hr
    rcases Finset.mem_union.mp hr with hX | hY
    · exact hcp ((hxOnly hX).2 c hcW he)
    · exact hcq ((hyOnly hY).2 c hcW he)
  have hsubN : G.neighborFinset c ⊆ ({a,b} : Finset V) := by
    intro x hx
    have hcx := (G.mem_neighborFinset c x).mp hx
    have := h.nonempty
    have hl := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := z) (v := x)).trans hd
    have casesDist : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases casesDist with h0 | h1 | h2 | h3
    · have hzx := (h.preconnected z x).dist_eq_zero_iff.mp h0
      subst x
      have hf := (mW c).mp hcW
      rw [dist_eq_one_iff_adj.mpr hcx.symm] at hf
      contradiction
    · exact hZ ▸ (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)
    · have hmem := (mW x).mpr h2
      rw [← hWcover] at hmem
      rcases (show x = p ∨ x = q ∨ x = c from by simpa using hmem) with e | e | e
      · exact (hcpN (e ▸ hcx)).elim
      · exact (hcqN (e ▸ hcx)).elim
      · exact (G.ne_of_adj hcx e.symm).elim
    · exact (hcR x ((mR x).mpr h3) hcx).elim
  have hlow := (Finset.card_le_card hsubN).trans Finset.card_le_two
  have hcNe : c ≠ z := by
    intro he
    have hh := (mW c).mp hcW
    simp [he] at hh
  have hhigh := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G := G) c z hcNe).resolve_right (by omega)
  change G.degree c ≤ 2 at hlow
  omega
end Graph189DegreeTwoOuter
end

section
namespace Graph189DegreeTwoAdjacent
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoOuter
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
theorem order_le_three_sigma_of_degree_two (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree)
    (z a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b}) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree := by
  classical
  by_contra! hn
  have := h.nonempty
  let s := G.secondSmallestDegree
  change 3 * s < Fintype.card V at hn
  change 3 ≤ s at hs
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  have mW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have az : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have bz : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have cap (u : V) : (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s :=
    distance_two_cap s hσ u
  have ds (x y : V) : G.dist x y ≤ 3 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := x) (v := y)).trans hd
  have anchors {u : V} (hu : G.Adj z u) : u = a ∨ u = b := by
    simpa [hZ] using (G.mem_neighborFinset z u).mpr hu
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hh := ds z x
    have hr : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases hr with h0 | h1 | h2 | h3
    · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
    · have hu := anchors (dist_eq_one_iff_adj.mp h1)
      exact hu.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((mW x).mpr h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((mR x).mpr h3))))
  have univ_eq : insert z (({a,b} : Finset V) ∪ W ∪ R) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton,Finset.mem_univ,iff_true]
    have hx := all x
    tauto
  have h₁ := Finset.card_insert_le z (({a,b} : Finset V) ∪ W ∪ R)
  rw [univ_eq,Finset.card_univ] at h₁
  have h₂ := Finset.card_union_le (({a,b} : Finset V) ∪ W) R
  have h₃ := Finset.card_union_le ({a,b} : Finset V) W
  rw [Finset.card_pair hne] at h₃
  have hN : Fintype.card V ≤ W.card + R.card + 3 := by omega
  have hWcap : W.card ≤ s := cap z
  have hRlarge : 2 * s - 2 ≤ R.card := by omega
  have reachW {r : V} (hr : r ∈ R) : ∃ w ∈ W, G.Adj w r := by
    obtain ⟨w,hw,hadj⟩ := split_three h ((mR r).mp hr)
    exact ⟨w,(mW w).mpr hw,hadj⟩
  have reachAnchor {w : V} (hw : w ∈ W) : G.Adj a w ∨ G.Adj b w := by
    obtain ⟨u,hu,hadj⟩ := split_two h ((mW w).mp hw)
    rcases anchors hu with e | e
    · exact Or.inl (e ▸ hadj)
    · exact Or.inr (e ▸ hadj)
  have remoteNo {u r : V} (hu : G.Adj z u) (hr : r ∈ R) : ¬ G.Adj u r := by
    intro hadj
    have ht := h.dist_triangle (u := z) (v := u) (w := r)
    rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr hadj] at ht
    omega
  have remoteTwo {u r w : V} (hu : G.Adj z u) (hr : r ∈ R) (huw : G.Adj u w)
      (hwr : G.Adj w r) : G.dist u r = 2 := by
    have hne : u ≠ r := by
      intro e
      have hh := (mR r).mp hr
      rw [← e,dist_eq_one_iff_adj.mpr hu] at hh
      contradiction
    exact two_edges huw hwr hne (remoteNo hu hr)
  let Da := R.filter (fun r => G.dist a r = 2)
  let Db := R.filter (fun r => G.dist b r = 2)
  let Ma := W.filter (fun w => ¬ G.Adj a w)
  let Mb := W.filter (fun w => ¬ G.Adj b w)
  have lim (u v : V) (huv : G.Adj u v) (hu : G.Adj z u)
      (hav : ∀ w ∈ W, G.Adj u w ∨ G.Adj v w) :
      (R.filter (fun r => G.dist u r = 2)).card + (W.filter (fun w => ¬ G.Adj u w)).card ≤ s ∧
        1 ≤ (W.filter (fun w => ¬ G.Adj u w)).card := by
    let D := R.filter (fun r => G.dist u r = 2)
    let M := W.filter (fun w => ¬ G.Adj u w)
    have hsub : D ∪ M ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_union.mp hx with hd' | hm
      · exact (Finset.mem_filter.mp hd').2
      · obtain ⟨hxW,hn⟩ := Finset.mem_filter.mp hm
        have hne : u ≠ x := by
          intro e
          have hh := (mW x).mp hxW
          rw [← e,dist_eq_one_iff_adj.mpr hu] at hh
          contradiction
        exact two_edges huv ((hav x hxW).resolve_left hn) hne hn
    have hdis : Disjoint D M := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      have hx' := (mR x).mp (Finset.mem_filter.mp hx).1
      have hy' := (mW x).mp (Finset.mem_filter.mp hy).1
      omega
    have hl := (Finset.card_le_card hsub).trans (cap u)
    rw [Finset.card_union_of_disjoint hdis] at hl
    refine ⟨hl,?_⟩
    by_contra! hg
    change M.card < 1 at hg
    have zero : M = ∅ := Finset.card_eq_zero.mp (by omega)
    have funiv : R ⊆ D := by
      intro r hr
      obtain ⟨w,hw,hwr⟩ := reachW hr
      have huw : G.Adj u w := by
        by_contra hn
        have hm : w ∈ M := Finset.mem_filter.mpr ⟨hw,hn⟩
        simp [zero] at hm
      exact Finset.mem_filter.mpr ⟨hr,remoteTwo hu hr huw hwr⟩
    have he := Finset.card_le_card funiv
    omega
  have limNon (u v p : V) (hu : G.Adj z u) (hv : G.Adj z v)
      (hne : u ≠ v) (hnuv : ¬ G.Adj u v) (hpW : p ∈ W)
      (hmiss : ∀ w ∈ W, G.Adj u w ↔ w ≠ p) :
      (R.filter (fun r => G.dist u r = 2)).card + (W.filter (fun w => ¬ G.Adj u w)).card ≤ s ∧
        1 ≤ (W.filter (fun w => ¬ G.Adj u w)).card := by
    let D := R.filter (fun r => G.dist u r = 2)
    let M := W.filter (fun w => ¬ G.Adj u w)
    have hM : M = {p} := by
      ext x
      constructor
      · intro hmem
        obtain ⟨hx,hx'⟩ := Finset.mem_filter.mp hmem
        by_contra hn
        exact hx' ((hmiss x hx).mpr (by simpa using hn))
      · intro he
        have hx : x = p := by simpa using he
        subst x
        exact Finset.mem_filter.mpr ⟨hpW,fun hh => (hmiss p hpW).mp hh rfl⟩
    have hvD : v ∉ D := by
      intro hmem
      have hm := (mR v).mp (Finset.mem_filter.mp hmem).1
      rw [dist_eq_one_iff_adj.mpr hv] at hm
      contradiction
    have hsub : insert v D ⊆ Finset.univ.filter (fun w => G.dist u w = 2) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with e | hmem
      · subst x
        simp [two_edges hu.symm hv hne hnuv]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hmem).2⟩
    have hbound := (Finset.card_le_card hsub).trans (cap u)
    rw [Finset.card_insert_of_notMem hvD] at hbound
    change D.card + M.card ≤ s ∧ 1 ≤ M.card
    simpa [hM] using hbound
  obtain ⟨⟨la,ha⟩,⟨lb,hb⟩⟩ :
      (Da.card + Ma.card ≤ s ∧ 1 ≤ Ma.card) ∧
      (Db.card + Mb.card ≤ s ∧ 1 ≤ Mb.card) := by
    by_cases hab : G.Adj a b
    · exact ⟨lim a b hab az (fun _ hx => reachAnchor hx),
        lim b a hab.symm bz (fun _ hx => (reachAnchor hx).symm)⟩
    · have hl := large_nonadjacent_layout h hd hσ (by exact hs) (by change 2*s+4 ≤ _; omega)
        z a b hne hZ hab
      obtain ⟨_,_,_,_,_,p,hp,q,hq,_,hap,hbq,_,_⟩ := hl
      exact ⟨limNon a b p az bz hne hab hp hap,
        limNon b a q bz az hne.symm (fun e => hab e.symm) hq hbq⟩
  have coverR : Da ∪ Db = R := by
    apply Finset.Subset.antisymm (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    intro r hr
    obtain ⟨w,hw,hwr⟩ := reachW hr
    apply Finset.mem_union.mpr
    exact (reachAnchor hw).imp
      (fun he => Finset.mem_filter.mpr ⟨hr,remoteTwo az hr he hwr⟩)
      (fun he => Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr he hwr⟩)
  have hsum := Finset.card_union_le Da Db
  rw [coverR] at hsum
  have hDa : Da.card = s - 1 := by omega
  have hDb : Db.card = s - 1 := by omega
  have hW : W.card = s := by omega
  have hMa : Ma.card = 1 := by omega
  have hMb : Mb.card = 1 := by omega
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hMa
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hMb
  have hpM : p ∈ Ma := by simp [hp]
  have hqM : q ∈ Mb := by simp [hq]
  obtain ⟨hpW,hpa⟩ := Finset.mem_filter.mp hpM
  obtain ⟨hqW,hqb⟩ := Finset.mem_filter.mp hqM
  have hpq : p ≠ q := by
    intro e
    exact (reachAnchor hpW).elim hpa (fun he => hqb (e ▸ he))
  have hpb : G.Adj b p := (reachAnchor hpW).resolve_left hpa
  have hqa : G.Adj a q := (reachAnchor hqW).resolve_right hqb
  have hx (u : V) (hx : u ∈ W) (hn : u ≠ p) : G.Adj a u := by
    by_contra he
    have hmu : u ∈ Ma := Finset.mem_filter.mpr ⟨hx,he⟩
    exact hn (by simpa [hp] using hmu)
  have hy (u : V) (hx : u ∈ W) (hn : u ≠ q) : G.Adj b u := by
    by_contra he
    have hmu : u ∈ Mb := Finset.mem_filter.mpr ⟨hx,he⟩
    exact hn (by simpa [hq] using hmu)
  have hcExists : 0 < ((W.erase p).erase q).card := by
    have hq' : q ∈ W.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hqW⟩
    rw [Finset.card_erase_of_mem hq',Finset.card_erase_of_mem hpW,hW]
    omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hcExists
  have hcq : c ≠ q := Finset.ne_of_mem_erase hc
  have hcp : c ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcW : c ∈ W := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hca := hx c hcW hcp
  have hcb := hy c hcW hcq
  have ddis : Disjoint Da Db := by
    by_contra hn
    have hh := Finset.card_union_add_card_inter Da Db
    rw [coverR,hDa,hDb] at hh
    have hpos : 0 < (Da ∩ Db).card := by
      have hh := Finset.disjoint_iff_inter_eq_empty.not.mp hn
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hh)
    omega
  have noRemote (r : V) (hr : r ∈ R) : ¬ G.Adj c r := by
    intro he
    have ha : r ∈ Da := Finset.mem_filter.mpr ⟨hr,remoteTwo az hr hca he⟩
    have hb : r ∈ Db := Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr hcb he⟩
    exact Finset.disjoint_left.mp ddis ha hb
  have layer_via {r : V} (hr : r ∈ R) (hn : r ∉ Da) : G.Adj p r := by
    obtain ⟨w,hw,hwr⟩ := reachW hr
    by_cases hwP : w = p
    · exact hwP ▸ hwr
    · exact (hn (Finset.mem_filter.mpr ⟨hr,remoteTwo az hr (hx w hw hwP) hwr⟩)).elim
  have layer_via' {r : V} (hr : r ∈ R) (hn : r ∉ Db) : G.Adj q r := by
    obtain ⟨w,hw,hwr⟩ := reachW hr
    by_cases hwQ : w = q
    · exact hwQ ▸ hwr
    · exact (hn (Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr (hy w hw hwQ) hwr⟩)).elim
  have acrossP (r : V) (hr : r ∈ Db) : G.Adj p r :=
    layer_via (Finset.mem_filter.mp hr).1 (fun he => Finset.disjoint_left.mp ddis he hr)
  have acrossQ (r : V) (hr : r ∈ Da) : G.Adj q r :=
    layer_via' (Finset.mem_filter.mp hr).1 (fun he => Finset.disjoint_left.mp ddis hr he)
  have hz2 : G.dist c z = 2 := by rw [dist_comm]; exact (mW c).mp hcW
  have hzR : z ∉ R := by intro hz; have hh := (mR z).mp hz; simp at hh
  have cDistance {v r : V} (hcv : G.Adj c v) (hvr : G.Adj v r) (hr : r ∈ R) :
      G.dist c r = 2 := by
    have hne : c ≠ r := by
      intro e
      have hl := (mW c).mp hcW
      have hh := (mR r).mp hr
      rw [e] at hl
      omega
    exact two_edges hcv hvr hne (noRemote r hr)
  have impossibleBoth (hP : G.Adj c p) (hQ : G.Adj c q) : False := by
    have hsub : insert z R ⊆ Finset.univ.filter (fun x => G.dist c x = 2) := by
      intro x hh
      rcases Finset.mem_insert.mp hh with e | hr
      · subst x; simp [hz2]
      · have h' := hr
        rw [← coverR] at h'
        rcases Finset.mem_union.mp h' with ha | hb
        · simp [cDistance hQ (acrossQ x ha) hr]
        · simp [cDistance hP (acrossP x hb) hr]
    have hcap := (Finset.card_le_card hsub).trans (cap c)
    rw [Finset.card_insert_of_notMem hzR] at hcap
    omega
  have excessive {v w : V} {D : Finset V} (hcv : G.Adj c v) (hwW : w ∈ W)
      (hw2 : G.dist c w = 2) (hD : D.card = s - 1) (hDR : D ⊆ R)
      (hVR : ∀ r ∈ D, G.Adj v r) : False := by
    have hwD : w ∉ D := by
      intro he
      have hw' := (mW w).mp hwW
      have hw'' := (mR w).mp (hDR he)
      omega
    have hzD : z ∉ insert w D := by
      intro he
      rcases Finset.mem_insert.mp he with e | h
      · have hh := (mW w).mp hwW
        simp [← e] at hh
      · exact hzR (hDR h)
    have hsub : insert z (insert w D) ⊆ Finset.univ.filter (fun x => G.dist c x = 2) := by
      intro x he
      rcases Finset.mem_insert.mp he with e | hm
      · subst x; simp [hz2]
      · rcases Finset.mem_insert.mp hm with e | hr
        · subst x; simp [hw2]
        · simp [cDistance hcv (hVR x hr) (hDR hr)]
    have hle := (Finset.card_le_card hsub).trans (cap c)
    rw [Finset.card_insert_of_notMem hzD,Finset.card_insert_of_notMem hwD,hD] at hle
    omega
  have noP : ¬ G.Adj c p := by
    intro hadj
    have hno : ¬ G.Adj c q := fun h => impossibleBoth hadj h
    exact excessive hadj hqW (two_edges hca.symm hqa hcq hno) hDb
      (Finset.filter_subset _ _) acrossP
  have noQ : ¬ G.Adj c q := by
    intro hadj
    exact excessive hadj hpW (two_edges hcb.symm hpb hcp noP) hDa
      (Finset.filter_subset _ _) acrossQ
  let S := ((W.erase p).erase q).erase c
  have hbound : G.neighborFinset c ⊆ ({a,b} : Finset V) ∪ S := by
    intro x hx
    have he := (G.mem_neighborFinset c x).mp hx
    rcases all x with e | e | e | hw | hr
    · subst x
      have hcz := (mW c).mp hcW
      rw [dist_eq_one_iff_adj.mpr he.symm] at hcz
      contradiction
    · exact Finset.mem_union_left _ (by simp [e])
    · exact Finset.mem_union_left _ (by simp [e])
    · have hxp : x ≠ p := fun eq => noP (eq ▸ he)
      have hxq : x ≠ q := fun eq => noQ (eq ▸ he)
      have hxc : x ≠ c := (G.ne_of_adj he).symm
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨hxc,Finset.mem_erase.mpr ⟨hxq,Finset.mem_erase.mpr ⟨hxp,hw⟩⟩⟩)
    · exact (noRemote x hr he).elim
  have hS : S.card = s - 3 := by
    have hq' : q ∈ W.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hqW⟩
    dsimp [S]
    rw [Finset.card_erase_of_mem hc,Finset.card_erase_of_mem hq',
      Finset.card_erase_of_mem hpW,hW]
    omega
  have hlow := (Finset.card_le_card hbound).trans (Finset.card_union_le _ _)
  rw [Finset.card_pair hne,hS] at hlow
  have hcNe : c ≠ z := by intro he; have hh := (mW c).mp hcW; simp [he] at hh
  have hhigh : s ≤ G.degree c := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G := G) c z hcNe).resolve_right (by
    change ¬ s ≤ G.degree z; omega)
  change G.degree c ≤ 2 + (s - 3) at hlow
  omega
theorem order_le_three_sigma (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree) (z : V) (hz : G.degree z = 2) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree := by
  have hz' : (G.neighborFinset z).card = 2 := hz
  obtain ⟨a,b,hne,hpair⟩ := Finset.card_eq_two.mp hz'
  exact order_le_three_sigma_of_degree_two h hd hσ hs z a b hne hpair
theorem order_le_nine_of_sigma_three (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 3)
    (z : V) (hz : G.degree z = 2) :
    Fintype.card V ≤ 9 := by
  simpa [hs] using order_le_three_sigma h hd hσ (by omega) z hz
end Graph189DegreeTwoAdjacent
end

open SimpleGraph Finset
namespace Graph189DiameterThree
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2
theorem traceable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) (diam : G.diam = 3)
    (point : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (low : G.minDegree ≤ 2) (upper : Fintype.card V ≤ 3 * (G.secondSmallestDegree + 1)) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases small : Fintype.card V ≤ 2 * G.secondSmallestDegree + 2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc point small
  have lower : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V := by omega
  by_cases uncut : ∀ c : V, (G.induce {x | x ≠ c}).Connected
  swap
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc point lower uncut
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have minimum (x : V) : G.degree z ≤ G.degree x := hz ▸ G.minDegree_le_degree x
  have two := h11 hc point lower
  have deg : G.degree z = 2 := by have := two z; omega
  have order (hk : 3 ≤ G.secondSmallestDegree) : Fintype.card V ≤ 3 * G.secondSmallestDegree :=
    Graph189DegreeTwoAdjacent.order_le_three_sigma hc diam.le point hk z deg
  by_cases short : Fintype.card V ≤ 2 * G.secondSmallestDegree + 6
  · exact thm_D_all hc uncut point lower short
  have three : 3 ≤ G.secondSmallestDegree := by omega
  have bound := order three
  have large : 7 ≤ G.secondSmallestDegree := by omega
  have high := b25_hx0 (G := G) minimum
  obtain ham | ⟨l,hne,hnd,hch,hmem,hhd,hlast,hmax,hlt⟩ := Cadre.exists_cadre hc point lower minimum
  · exact ham
  exfalso
  have length_bound := Cadre.m_ge hc uncut point minimum high two hne hnd hch hmem hhd hlast hmax hlt
  let p := Walk.ofSupport l hne hch
  have supp : p.support = l := Walk.support_ofSupport hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by rwa [supp])
  have contains : z ∈ p.support := by rwa [supp]
  obtain ⟨i,hi,atZ⟩ := List.mem_iff_getElem.mp contains
  let t : Fin p.support.length := ⟨i,hi⟩
  have eq : p.support[t.val] = z := atZ
  have longest {a b} (q : G.Walk a b) (hq : q.IsPath) (seen : p.support[t.val] ∈ q.support) : q.length ≤ p.length := by
    have h := hmax q.support hq.support_nodup q.isChain_adj_support (eq ▸ seen)
    rw [←supp,q.length_support,p.length_support] at h
    omega
  let E := (p.support.toFinsetᶜ : Finset V)
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length + E.card = Fintype.card V at total
  rw [←supp] at length_bound hlt
  have debit := Graph189ExteriorGap.protected_order_of_exterior_size p hp t longest
    (by rw [eq,deg]; omega) (fun v => by simpa only [Nat.add_comm] using point v)
    (card_pos.mp (by change 0 < E.card; omega)) (s := 3) (by decide) (by omega)
    (by change E.card + 3 ≤ G.secondSmallestDegree + 1; omega)
  omega
end Graph189DiameterThree

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1_H1_R1.H1 := by
  intro V _ _ _ G _ hc diam _ upper point _ _ low
  apply Graph189DiameterThree.traceable G hc diam point low
  exact upper.trans (Nat.mul_le_mul_right _ (by omega))
