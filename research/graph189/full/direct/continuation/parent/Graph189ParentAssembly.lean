import FormalConjectures.WrittenOnTheWallII.GraphConjecture189
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Sort
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Research assembly for WOW II 189. The final theorem assumes the two remaining cases.
The cut-vertex case is included. This file is a conditional research theorem.
-/

-- Reduction WrittenOnTheWallII.GraphConjecture189.conjecture189.R2 of WOWII Conjecture 189
-- Credit: @carl2sheriff
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Reduction of WOWII Conjecture 189 to the two cases `n ≥ 2σ + 3` (graph with a cut
vertex, resp. 2-connected graph). The case `n ≤ 2σ + 2` is proved here (Theorem C):
a longest path with both ends of degree `≥ σ` gives an Ore-type degree sum, and the
single low-degree vertex `x₀` is handled through a rotation / deletion argument.

Infrastructure adapted from reduction R1 by @computerfreak97, PR #2971, itself adapting
philipsaint's Dirac formalization (`degree_pair`, `rot`, `getD_zero`, `getD_last`,
`dist_iso`, `even_iso`, `second_iso`, start of `main`, and the longest-path / crossing-chord
argument of `trace_of_sum`).
-/

open SimpleGraph

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

/-- Case with a cut vertex and `2σ + 3 ≤ n`. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∃ c : V, ¬ (G.induce {x | x ≠ c}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- 2-connected case with `2σ + 3 ≤ n`. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

-- Fact 0 (adapted from R1).
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

-- Rotation and list helpers adapted from reduction R1.
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


/-- A Hamiltonian walk from a nodup chain through all vertices (adapted from R1). -/
lemma ham_of_list [DecidableRel G.Adj] (l : List V) (hne : l ≠ []) (hnd : l.Nodup)
    (hch : l.IsChain G.Adj) (hlen : l.length = Fintype.card V) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by simpa [p, Walk.support_ofSupport] using hnd)
  exact ⟨_, _, p, Walk.isHamiltonian_iff_isPath_and_length_eq.mpr
    ⟨hp, by simpa [p, Walk.length_ofSupport, hlen]⟩⟩

/-- Existence of a longest path, as a nodup chain list. -/
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

/-- Lemma 4 (Ore cycle on a longest path). -/
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

/-- Lemma 4 for a path `l` of the graph with a vertex `x₀` removed. -/
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
  -- The two index sets of possible crossing chords.
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

/-- A permutation of `y :: l` that is a chain contradicts maximality. -/
lemma longer_of_perm (l : List V) (hnd : l.Nodup)
    (hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length)
    (y : V) (hy : y ∉ l) {c : List V} (hc : c.Perm (y :: l)) (hch : c.IsChain G.Adj) : False := by
  have hnd' : c.Nodup := hc.nodup_iff.mpr (List.nodup_cons.2 ⟨hy, hnd⟩)
  have := hmax c hnd' hch
  rw [hc.length_eq] at this
  simp only [List.length_cons] at this
  omega

/-- Inserting an off-path vertex between two consecutive path vertices. -/
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

/-- Lemma 5 (a),(b): a vertex `y` off a longest path adjacent to `l[j]`. -/
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

/-- Two steps along a path give distance exactly two. -/
lemma dist_two (hconn : G.Connected) {y a b : V} (h1 : G.Adj y a) (h2 : G.Adj a b)
    (h3 : ¬ G.Adj y b) (h4 : b ≠ y) : G.dist y b = 2 := by
  have hle : G.dist y b ≤ 2 := by
    have := SimpleGraph.dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))
    simpa using this
  have h0 : G.dist y b ≠ 0 := fun h => h4 ((hconn.dist_eq_zero_iff.mp h).symm)
  have h1' : G.dist y b ≠ 1 := fun h => h3 (SimpleGraph.dist_eq_one_iff_adj.mp h)
  omega

/-- Lemma 5 (c): an off-path vertex with all neighbours on the path has many
vertices at even distance. -/
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

/-- Lemma 3, first part: neighbours of a vertex at odd distance `≥ 3` from `v`
lie at distance `≥ 2` from `v`. -/
lemma lemma3a (hconn : G.Connected) (v w : V) (hw : 3 ≤ G.dist v w)
    (u : V) (hu : G.Adj w u) : 2 ≤ G.dist v u := by
  by_contra hlt
  have h1 := hconn.dist_triangle (u := v) (v := u) (w := w)
  have h2 : G.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm
  omega

/-- Lemma 3, second part: counting of vertices outside the closed neighbourhood. -/
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

/-- Case A of Theorem C: some longest path has both ends different from `x₀`. -/
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
  -- the unique vertex off the path
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
  -- neighbours of y are neighbours of a
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

/-- A path leaving the vertex set of a list. -/
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

/-- Case B, the longest path starts at `x₀`. -/
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
    -- the unique vertex off the path
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

/-- Case B of Theorem C: every longest path has `x₀` as an end. -/
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

/-- Theorem C: `n ≤ 2σ + 2` and the even-distance bound give a Hamiltonian path. -/
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


theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture189.conjecture189 := by
  intro h1 h2 V _ _ _ G _ hc hb
  classical
  let e := Fintype.equivFin V
  let φ := SimpleGraph.Iso.map e G
  have : Nontrivial (Fin (Fintype.card V)) := e.symm.nontrivial
  have hc' := φ.connected_iff.mp hc
  have h : ∀ y, distEven (G.map e) y ≤ 1 + secondSmallestDegree (G.map e) := by
    intro y
    obtain ⟨x,rfl⟩ := φ.surjective y
    rw [even_iso φ hc, second_iso φ]
    exact (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))).trans hb
  obtain ⟨a,b,q,hq⟩ : ∃ a b : Fin (Fintype.card V), ∃ q : (G.map e).Walk a b, q.IsHamiltonian := by
    by_cases hn : Fintype.card (Fin (Fintype.card V)) ≤ 2 * secondSmallestDegree (G.map e) + 2
    · exact theorem_C hc' h hn
    · by_cases hart : ∃ c : Fin (Fintype.card V), ¬ ((G.map e).induce {x | x ≠ c}).Connected
      · exact h1 (G.map e) hc' h (by omega) hart
      · push Not at hart
        exact h2 (G.map e) hc' h (by omega) hart
  exact ⟨φ.symm a,φ.symm b,q.map φ.symm.toHom,hq.map _ φ.symm.bijective⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2

section
/-!
The parity estimate in Easwar–Johari, §5, applied directly to arbitrary sides
of a separating vertex. The side need not have been constructed as a block.
-/


namespace Graph189CutCore
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The defining expression of the upstream even-distance invariant. -/
noncomputable def evenCard (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter fun y => Even (G.dist v y)).card

/-- The defining expression of the upstream degree sequence. -/
noncomputable def sortedDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : V => G.degree v).sort (· ≤ ·)

/-- The defining expression of the upstream second-smallest degree. -/
noncomputable def secondDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (sortedDegrees G).getD 1 0

/-- All edges leaving a nonempty side pass through the gate. -/
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

/-- In a graph of order above the small-order threshold, every branch
contains two vertices, and consequently contains a vertex of high degree. -/
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
/-- If a branch contains a nonneighbor of its gate, it contains a vertex
at distance exactly two from the gate. -/
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

/-- At a branching cut, two other large branches exhaust both parity budgets.
This forces every vertex in the first branch to touch the gate. -/
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

/-- Under the large-order Graph 189 hypotheses, a single cut vertex cannot
have three disjoint branches. -/
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


/-- The ambient vertex set of one connected component after deleting the gate. -/
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

/-- The local block-branching obstruction. Removing any vertex leaves at most
two connected components. The exact Graph 189 degree statistic is used through
its defining order-statistic property. -/
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
/-- The order-statistic argument from OMA's
`WrittenOnTheWallII.GraphConjecture189.conjecture189.R1` (PR #2971). -/
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


/-- The cut-vertex branch of R2 can be restricted to a deletion with exactly
two components. No assumption is made on their sizes, connectivity, or shape. -/
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

/-- In the large-order cut-vertex branch of WOWII Graph 189, deleting a cut
vertex separates the graph into exactly two connected components. -/
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

/-- Passing from a component on the deletion subtype to its ambient vertex set
preserves connectedness of the induced graph. -/
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

/-- Two components after deletion supply the two disjoint connected sides
covering every vertex except the deleted vertex. -/
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

/-- A cut has a nonempty side opposite any specified surviving vertex. -/
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

/-- A vertex between the two gates has no edge into either remote side. -/
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

/-- Every vertex between two remote sides, other than the distinct gates,
has degree strictly below k. -/
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

-- Equal-size alternating-chain construction from OMA Graph 189 R1, also
-- used in the earlier bipartite branch of the conjecture.
/-- Alternate between equally sized sets of vertices, starting at an additional
vertex with a neighbor in the first set if that set is nonempty. -/
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

/-- A component of order exactly twice the second-degree threshold has a
spanning path starting at its gate. -/
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

/-- The large-order regime excludes all leaves and isolated vertices. -/
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

/-- The other side's gate parity budget bounds the order of a remote side. -/
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

/-- Splice two ambient vertex lists rooted at the common cut vertex. -/
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

/-- It suffices to construct the rooted path on components of order at most
twice the degree threshold minus one. The saturated size is proved outright. -/
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

/-- Transport the four small-side hypotheses to the induced graph, then
lift the resulting rooted list to the ambient vertex type. -/
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

end Graph189
end

section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*}
/-- Adjoin a marker of degree one next to c. -/
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

/-- Traceability can be tested after completing any high-degree set. -/
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
/-- A gate-rooted clique traversal lifts to a Hamilton path in a marked supergraph. -/
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

/-- The clique completion argument on a finite side with prescribed gate. -/
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

/-- A finite clique has a spanning path starting at any prescribed member. -/
theorem rootedCliqueList (s : Finset V) {r : V} (hr : r ∈ s)
    (hclique : ∀ {u v}, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x ∈ s := by
  let L := r :: (s.erase r).toList
  have hm (x : V) : x ∈ L ↔ x ∈ s := by
    by_cases hx : x = r <;> simp [L, hx, hr]
  have hn : L.Nodup := List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  exact ⟨L, rfl, hn, chain_of_clique_list hn (fun x hx => (hm x).mp hx) hclique, hm⟩

/-- A finite clique has a spanning path between distinct prescribed members. -/
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

/-- A graph that is a clique except at z has a rooted spanning path if z has a
clique neighbor different from the root, or if the root is z itself. -/
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

/-- Span a core from its gate after closure has made all but at most one core
vertex a clique. Two internal neighbors suffice for the exceptional vertex. -/
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

/-- A finite side of order at most 2k has a marked Hamilton path if
every pair off the gate contains a high vertex and all such vertices
have at least two neighbors. -/
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

/-- Every large-order graph in the cut-vertex branch of WOWII Graph 189
has a Hamiltonian path. This is the complete mathematical statement of R2.H1. -/
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

theorem Graph189ParentAssembly.cutVertex : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H1 := by
  intro V _ _ _ G _ hc hσ horder hcut
  exact Graph189CutH1.cut_vertex_case G hc hσ horder hcut

-- Reduction WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1 of step WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2
-- Credit: @ali-hamdan-007

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1

open SimpleGraph Finset
open scoped BigOperators

section PathProof

variable {V : Type*} {G : SimpleGraph V} {z u : V}

private theorem bound_list {v : V} (P : G.Walk z v)
    (longest : ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length)
    (L : List V) (h : L.head? = some z) (hc : L.IsChain G.Adj) (hn : L.Nodup) :
    L.length ≤ P.support.length := by
  have ne : L ≠ [] := by rintro rfl; simp at h
  have he : L.head ne = z := by simpa [List.head?_eq_some_head ne] using h
  subst z
  let Q := Walk.ofSupport L ne hc
  have qs : Q.support = L := Walk.support_ofSupport _ _
  have qp : Q.IsPath := Walk.IsPath.mk' (qs.symm ▸ hn)
  have le := longest Q qp
  have ql := Q.length_support
  rw [qs] at ql
  have pl := P.length_support
  omega

private theorem pos_eq (L : List V) (i : ℕ) (hi : i < L.length) (d : V) : L.getD i d = L[i] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem take_last (L : List V) (i : ℕ) (hi : i < L.length) (d : V) :
    (L.take (i+1)).getLast? = some (L.getD i d) := by
  rw [List.getLast?_take, pos_eq _ _ hi _]
  simp [List.getElem?_eq_getElem hi]

private theorem drop_head (L : List V) (i : ℕ) (hi : i < L.length) (d : V) :
    (L.drop i).head? = some (L.getD i d) := by
  rw [List.head?_drop, pos_eq _ _ hi _, List.getElem?_eq_getElem hi]

private theorem bridge {A B : List V} {a b : V} (ca : A.IsChain G.Adj) (cb : B.IsChain G.Adj)
    (ha : A.getLast? = some a) (hb : B.head? = some b) (e : G.Adj a b) :
    (A ++ B).IsChain G.Adj := by
  apply ca.append cb
  simpa [ha,hb] using e

private theorem insert_chain {L : List V} (hL : L.IsChain G.Adj) (i : ℕ) (hi : i < L.length)
    (X : List V) (x y : V) (hX : X.IsChain G.Adj) (hx : X.head? = some x)
    (hy : X.getLast? = some y) (d : V) (left : G.Adj (L.getD i d) x)
    (right : i+1 < L.length → G.Adj y (L.getD (i+1) d)) :
    ((L.take (i+1) ++ X) ++ L.drop (i+1)).IsChain G.Adj := by
  have pre := bridge (hL.take _) hX (take_last L i hi d) hx left
  apply pre.append (hL.drop _)
  intro a ha b hb
  have last : (L.take (i+1) ++ X).getLast? = some y := by simp [List.getLast?_append,hy]
  rw [last] at ha
  have eq : a = y := by simpa using ha.symm
  subst a
  by_cases hs : i+1 < L.length
  · rw [drop_head L _ hs d] at hb
    have eq : b = L.getD (i+1) d := by simpa using hb.symm
    exact eq ▸ right hs
  · have emp : L.drop (i+1) = [] := by simp [List.drop_eq_nil_iff.mpr (by omega : L.length ≤ i+1)]
    simp [emp] at hb

private theorem forbid_insert {L : List V} (head : L.head? = some z) (chain : L.IsChain G.Adj)
    (nodup : L.Nodup) (maximal : ∀ K : List V, K.head? = some z → K.IsChain G.Adj → K.Nodup → K.length ≤ L.length)
    (i : ℕ) (hi : i < L.length) (X : List V) (x y : V) (hX : X.IsChain G.Adj)
    (hx : X.head? = some x) (hy : X.getLast? = some y) (hn : X.Nodup) (dis : X.Disjoint L)
    (left : G.Adj (L.getD i z) x) (right : i+1 < L.length → G.Adj y (L.getD (i+1) z)) : False := by
  let A := L.take (i+1)
  let B := L.drop (i+1)
  have split : A ++ B = L := List.take_append_drop _ _
  have perm : ((A ++ X) ++ B).Perm (X ++ L) := by
    rw [← split, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  have n := perm.nodup_iff.mpr (List.nodup_append'.mpr ⟨hn,nodup,dis⟩)
  have hd : ((A ++ X) ++ B).head? = some z := by simp [A,List.head?_append,List.head?_take,head]
  have le := maximal _ hd (insert_chain chain i hi X x y hX hx hy z left right) n
  have equal := perm.length_eq
  have nx : 0 < X.length := by cases X <;> simp_all
  rw [equal] at le
  simp only [List.length_append] at le
  omega

private theorem forbid_cross {L : List V} (head : L.head? = some z) (chain : L.IsChain G.Adj)
    (nodup : L.Nodup) (maximal : ∀ K : List V, K.head? = some z → K.IsChain G.Adj → K.Nodup → K.length ≤ L.length)
    (outside : u ∉ L) (i j : ℕ) (hij : i < j) (hj : j+1 < L.length)
    (left : G.Adj (L.getD i z) u) (mid : G.Adj u (L.getD j z))
    (chord : G.Adj (L.getD (i+1) z) (L.getD (j+1) z)) : False := by
  let A := L.take (i+1)
  let B := (L.take (j+1)).drop (i+1)
  let C := L.drop (j+1)
  have ab : A ++ B = L.take (j+1) := by
    have h := List.take_append_drop (i+1) (L.take (j+1))
    simpa [A,B,List.take_take,Nat.min_eq_left (by omega : i+1 ≤ j+1)] using h
  have split : (A ++ B) ++ C = L := by rw [ab]; exact List.take_append_drop _ _
  have blen : (L.take (j+1)).length = j+1 := by simp [Nat.min_eq_left (by omega : j+1 ≤ L.length)]
  have bst : B.head? = some (L.getD (i+1) z) := by
    simp [B,List.head?_drop,show i+1 < j+1 by omega,
      List.getElem?_eq_getElem (by omega : i+1 < L.length)]
  have ben : B.getLast? = some (L.getD j z) := by
    dsimp only [B]
    rw [List.getLast?_drop,if_neg (by rw [blen]; omega)]
    exact take_last L _ (by omega) _
  have br := List.isChain_reverse.mpr (((chain.take (j+1)).drop (i+1)).imp fun _ _ h => h.symm)
  have c1 := bridge (chain.take (i+1)) (List.isChain_singleton u) (take_last L i (by omega) z) (by simp) left
  have c2 : ((A ++ [u]) ++ B.reverse).IsChain G.Adj := by
    apply bridge c1 br (a := u) (b := L.getD j z) (by simp) (by simpa using ben) mid
  have c3 : (((A ++ [u]) ++ B.reverse) ++ C).IsChain G.Adj := by
    apply bridge c2 (chain.drop _) (a := L.getD (i+1) z) (b := L.getD (j+1) z) _ (drop_head L _ hj z) chord
    rw [List.getLast?_append,List.getLast?_reverse,bst]
    rfl
  have p1 : ((A ++ [u]) ++ B.reverse).Perm ([u] ++ (A ++ B)) := by
    exact (List.perm_append_comm.append_right B.reverse).trans
      ((B.reverse_perm.append_left ([u] ++ A)).trans (by simp))
  have perm : (((A ++ [u]) ++ B.reverse) ++ C).Perm (u :: L) := by
    rw [← split]; simpa [List.append_assoc] using p1.append_right C
  have n := perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨outside,nodup⟩)
  have hd : (((A ++ [u]) ++ B.reverse) ++ C).head? = some z := by simp [A,List.head?_append,List.head?_take,head]
  have le := maximal _ hd c3 n
  have equal := perm.length_eq
  rw [equal] at le
  simp only [List.length_cons] at le
  omega

/-- Contacts and their oriented successors along a longest path with prescribed start. -/
private theorem successors_of_rooted_longest {v : V} (P : G.Walk z v) (hp : P.IsPath)
    (longest : ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length)
    (outside : u ∉ P.support) (touches : ∃ w ∈ P.support, G.Adj u w) :
    ∃ (W : Finset V) (succ : V → V), W.Nonempty ∧ Set.InjOn succ (↑W : Set V) ∧
      (∀ w ∈ W, G.Adj u w) ∧ (∀ w ∈ W, succ w ≠ u ∧ ¬G.Adj u (succ w)) ∧
      (∀ a ∈ W, ∀ b ∈ W, ¬G.Adj (succ a) (succ b)) ∧
      (∀ w ∈ W, ∀ y, G.Adj u y → G.Adj (succ w) y → y ∈ W) ∧
      (∀ w ∈ W, G.Adj w (succ w) ∧ succ w ≠ z) ∧ u ≠ z := by
  classical
  let L := P.support
  have head : L.head? = some z := by cases P <;> rfl
  have chain : L.IsChain G.Adj := P.isChain_adj_support
  have nodup : L.Nodup := hp.support_nodup
  have maximal := bound_list P longest
  let W := L.toFinset.filter (G.Adj u)
  have memW (w : V) : w ∈ W ↔ w ∈ L ∧ G.Adj u w := by simp [W]
  let idx (w : V) := L.idxOf w
  have at_idx (w : V) (hw : w ∈ L) : ∃ h : idx w < L.length, L[idx w] = w := by
    have hi := List.idxOf_lt_length_iff.mpr hw
    exact ⟨hi,List.getElem_idxOf hi⟩
  have at_w (w : V) (hw : w ∈ W) : L.getD (idx w) z = w := by
    obtain ⟨hi,eq⟩ := at_idx w ((memW w).mp hw).1
    exact (pos_eq _ _ hi _).trans eq
  have next_lt (w : V) (hw : w ∈ W) : idx w + 1 < L.length := by
    by_contra hn
    obtain ⟨hi,_⟩ := at_idx w ((memW w).mp hw).1
    exact forbid_insert head chain nodup maximal (idx w) hi [u] u u (by simp) (by simp) (by simp)
      (by simp) (by simpa using outside) (by rw [at_w w hw]; exact ((memW w).mp hw).2.symm) (fun h => (hn h).elim)
  let succ (w : V) := L.getD (idx w+1) z
  have succmem (w : V) (hw : w ∈ W) : succ w ∈ L := by
    change L.getD (idx w+1) z ∈ L
    rw [pos_eq _ _ (next_lt w hw) _]; exact List.getElem_mem _
  have noedge (w : V) (hw : w ∈ W) : ¬G.Adj u (succ w) := by
    intro e
    have hi := next_lt w hw
    exact forbid_insert head chain nodup maximal (idx w) (by omega) [u] u u (by simp) (by simp)
      (by simp) (by simp) (by simpa using outside)
      (by rw [at_w w hw]; exact ((memW w).mp hw).2.symm) (fun _ => e)
  have same (a b : V) (ha : a ∈ W) (hb : b ∈ W) (h : idx a = idx b) : a = b :=
    (at_w a ha).symm.trans ((congrArg (fun i => L.getD i z) h).trans (at_w b hb))
  have no_cross (a b : V) (ha : a ∈ W) (hb : b ∈ W) (h : idx a < idx b) : ¬G.Adj (succ a) (succ b) := by
    intro e
    apply forbid_cross head chain nodup maximal outside (idx a) (idx b) h (next_lt b hb) _ _ e
    · rw [at_w a ha]; exact ((memW a).mp ha).2.symm
    · rw [at_w b hb]; exact ((memW b).mp hb).2
  obtain ⟨w₀,hw₀,e₀⟩ := touches
  refine ⟨W,succ,⟨w₀,(memW _).mpr ⟨hw₀,e₀⟩⟩,?_,fun w hw => ((memW w).mp hw).2,
    fun w hw => ⟨fun he => outside (he ▸ succmem w hw),noedge w hw⟩,?_,?_,?_,?_⟩
  · intro a ha b hb he
    change L.getD (idx a+1) z = L.getD (idx b+1) z at he
    rw [pos_eq _ _ (next_lt a ha) _,pos_eq _ _ (next_lt b hb) _] at he
    have h := nodup.getElem_inj_iff.mp he
    exact same a b ha hb (by omega)
  · intro a ha b hb e
    rcases lt_trichotomy (idx a) (idx b) with h | h | h
    · exact no_cross a b ha hb h e
    · have eq := same a b ha hb h
      subst b
      exact e.ne rfl
    · exact no_cross b a hb ha h e.symm
  · intro w hw y uy sy
    apply (memW _).mpr
    refine ⟨?_,uy⟩
    by_contra hy
    have hi := next_lt w hw
    apply forbid_insert head chain nodup maximal (idx w) (by omega) [u,y] u y
      (by simpa using uy) (by simp) (by simp) (by simp [uy.ne]) _ _ (fun _ => sy.symm)
    · simpa [List.disjoint_cons_left,hy] using (show u ∉ L from outside)
    · rw [at_w w hw]; exact ((memW w).mp hw).2.symm
  · intro w hw
    have hn := next_lt w hw
    have hi : idx w < L.length := by omega
    have gadj : G.Adj (L.getD (idx w) z) (L.getD (idx w+1) z) := by
      rw [pos_eq _ _ hi _,pos_eq _ _ hn _]
      exact chain.getElem _ hn
    refine ⟨?_,?_⟩
    · rw [at_w w hw] at gadj
      exact gadj
    · intro he
      have h0 : 0 < L.length := by omega
      have hz : L.getD 0 z = z := by
        have eq := drop_head L 0 h0 z
        simpa [head] using eq.symm
      change L.getD (idx w+1) z = z at he
      rw [← hz,pos_eq _ _ hn _,pos_eq _ _ h0 _] at he
      have eq := nodup.getElem_inj_iff.mp he
      omega
  · intro h
    apply outside
    rw [h]
    exact P.start_mem_support

/-- A longest path starting at the prescribed vertex exists in every finite graph. -/
private theorem exists_rooted_longest [Fintype V] (G : SimpleGraph V) (z : V) :
    ∃ (v : V) (P : G.Walk z v), P.IsPath ∧
      ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length := by
  classical
  let Good (m : ℕ) := ∃ (v : V) (P : G.Walk z v), P.IsPath ∧ P.length = m
  have base : Good 0 := ⟨z,.nil,by simp,rfl⟩
  obtain ⟨v,P,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨v,P,hp,?_⟩
  intro b Q hQ
  rw [hlen]
  have card := hQ.support_nodup.length_le_card
  have size := Q.length_support
  exact Nat.le_findGreatest (by omega) (show Good Q.length from ⟨b,Q,hQ,rfl⟩)

/-- Connectivity supplies an omitted vertex that touches any nonspanning rooted path. -/
private theorem exists_exterior_contact {v : V} (P : G.Walk z v) (connected : G.Connected)
    (missing : ∃ x, x ∉ P.support) : ∃ u ∉ P.support, ∃ w ∈ P.support, G.Adj u w := by
  obtain ⟨x,hx⟩ := missing
  obtain ⟨R⟩ := connected z x
  obtain ⟨d,_,hin,hout⟩ := R.exists_boundary_dart {y | y ∈ P.support} P.start_mem_support hx
  exact ⟨d.snd,hout,d.fst,hin,d.adj.symm⟩

end PathProof

section ContactCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path contact and its successor violate local Ore for at least one
contact. The other hypotheses isolate the path-splicing part of the proof. -/
private theorem bad_wedge_of_successors (u : V) (W : Finset V) (succ : V → V)
    (hn : W.Nonempty) (inj : Set.InjOn succ (↑W : Set V))
    (touch : ∀ w ∈ W, G.Adj u w)
    (miss : ∀ w ∈ W, succ w ≠ u ∧ ¬G.Adj u (succ w))
    (indep : ∀ a ∈ W, ∀ b ∈ W, ¬G.Adj (succ a) (succ b))
    (common : ∀ w ∈ W, ∀ v, G.Adj u v → G.Adj (succ w) v → v ∈ W) :
    ∃ w ∈ W, G.degree u + G.degree (succ w) <
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset (succ w)).card := by
  classical
  let U := W.image succ
  by_contra! hall
  have row (w : V) (hw : w ∈ W) :
      ((U.filter fun v => G.Adj w v)).card + 1 ≤ ((W.filter fun v => G.Adj v (succ w))).card := by
    let A := G.neighborFinset u
    let B := G.neighborFinset (succ w)
    let C := G.neighborFinset w
    let D := C \ (A ∪ B)
    have hu : D ∪ (A ∪ B) = (A ∪ C) ∪ B := by ext a; simp [D]; tauto
    have dis : Disjoint D (A ∪ B) := by
      rw [Finset.disjoint_left]
      exact fun _ h => (Finset.mem_sdiff.mp h).2
    have join := Finset.card_union_of_disjoint dis
    rw [hu] at join
    have oi := Finset.card_union_add_card_inter A B
    have ah : A.card = G.degree u := G.card_neighborFinset_eq_degree u
    have bh : B.card = G.degree (succ w) := G.card_neighborFinset_eq_degree _
    have localbound := hall w hw
    change ((A ∪ C) ∪ B).card ≤ G.degree u + G.degree (succ w) at localbound
    have bound : D.card ≤ (A ∩ B).card := by omega
    have hsub : insert u ((U.filter fun v => G.Adj w v)) ⊆ D := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset _ _).mpr (touch w hw).symm,?_⟩
        intro hum
        rcases Finset.mem_union.mp hum with ha | hb
        · exact ((G.mem_neighborFinset _ _).mp ha).ne rfl
        · exact (miss _ hw).2 ((G.mem_neighborFinset _ _).mp hb).symm
      · obtain ⟨hvU,hvA⟩ := Finset.mem_filter.mp hv
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hvU
        apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset _ _).mpr hvA,?_⟩
        intro h
        rcases Finset.mem_union.mp h with ha | hB
        · exact (miss _ hb).2 ((G.mem_neighborFinset _ _).mp ha)
        · exact (indep _ hw _ hb) ((G.mem_neighborFinset _ _).mp hB)
    have hout : u ∉ (U.filter fun v => G.Adj w v) := by
      intro hu
      obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
      exact (miss _ hb).1 he
    have small := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hout] at small
    have other : A ∩ B ⊆ (W.filter fun v => G.Adj v (succ w)) := by
      intro v hv
      obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp hv
      have e₁ := (G.mem_neighborFinset _ _).mp h₁
      have e₂ := (G.mem_neighborFinset _ _).mp h₂
      exact Finset.mem_filter.mpr ⟨common _ hw v e₁ e₂,e₂.symm⟩
    exact small.trans (bound.trans (Finset.card_le_card other))
  have rows := Finset.sum_le_sum row
  have dbl : (∑ w ∈ W, (U.filter fun v => G.Adj w v).card) =
      ∑ v ∈ U, (W.filter fun w => G.Adj w v).card := by
    classical
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have im : (∑ v ∈ U, ((W.filter fun w => G.Adj w v)).card) =
      ∑ w ∈ W, ((W.filter fun v => G.Adj v (succ w))).card := Finset.sum_image inj
  rw [im] at dbl
  rw [Finset.sum_add_distrib] at rows
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at rows
  have pos := hn.card_pos
  omega

end ContactCount

section WedgeCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem predecessor {x z : V} {j : ℕ} (hz : G.dist x z = j+1) :
    ∃ a, G.dist x a = j ∧ G.Adj a z := by
  have hr : G.dist z x = j+1 := by rwa [dist_comm]
  have hp : G.Reachable z x := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hp.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at hz
  | cons he tail =>
    rename_i a
    have ht : tail.length = j := by rw [Walk.length_cons,hr] at hlen; omega
    have hh : G.dist x a ≤ j := by rw [dist_comm]; exact ht ▸ G.dist_le tail
    have := he.diff_dist_adj (u := x)
    exact ⟨a,by omega,he.symm⟩

/-- The order bound at an induced two-edge path with center x. -/
private theorem wedge_order (hc : G.Connected) {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z)
    (_hyz : ¬G.Adj y z) {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) :
    Fintype.card V + (k+1) * ((G.neighborFinset x ∪
        (G.neighborFinset y ∪ G.neighborFinset z)).card) ≤
        3*k+2 + k*(G.degree x + G.distEven x) + G.degree y + G.degree z := by
  classical
  let E (v : V) := Finset.univ.filter (fun w => Even (G.dist v w))
  let X := G.neighborFinset x
  let Y := G.neighborFinset y
  let Z := G.neighborFinset z
  let S := Y ∪ Z
  let U := X ∪ S
  let Q := X \ S
  let C := Y ∩ Z
  let I := C ∩ X
  let A := E x \ S
  let T := univ.filter (fun w => 3 ≤ G.dist x w ∧ 3 ≤ G.dist y w ∧ 3 ≤ G.dist z w ∧ ¬Even (G.dist x w))
  have ecap (v : V) : (E v).card ≤ k+1 := cap v
  have memN (v w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w := G.mem_neighborFinset v w
  have near_even (a v w : V) (ha : G.Adj a v) (hw : G.Adj v w) (hn : ¬G.Adj a w) : w ∈ E a := by
    have h := hc.dist_triangle (u:=a) (v:=v) (w:=w)
    rw [dist_eq_one_iff_adj.mpr ha, dist_eq_one_iff_adj.mpr hw] at h
    have hne : G.dist a w ≠ 1 := fun hh => hn (dist_eq_one_iff_adj.mp hh)
    exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
  have scset : S \ X ⊆ E x := by
    intro v hv
    obtain ⟨hs,hn⟩ := mem_sdiff.mp hv
    have hna : ¬G.Adj x v := fun hh => hn ((memN _ _).mpr hh)
    rcases mem_union.mp hs with hy|hz
    · exact near_even x y v hxy ((memN _ _).mp hy) hna
    · exact near_even x z v hxz ((memN _ _).mp hz) hna
  have ac : A.card + U.card ≤ G.distEven x + G.degree x := by
    have dj : Disjoint A (S \ X) := by
      rw [Finset.disjoint_left]
      exact fun _ ha hb => (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
    have sub : A ∪ (S \ X) ⊆ E x := by
      intro v hv
      exact (mem_union.mp hv).elim (fun ha => (mem_sdiff.mp ha).1) (fun hb => scset hb)
    have h := card_le_card sub
    rw [card_union_of_disjoint dj] at h
    have hc1 := Finset.card_sdiff_add_card_inter S X
    have hc2 := Finset.card_union_add_card_inter X S
    rw [Finset.inter_comm S X] at hc1
    have hd : X.card = G.degree x := G.card_neighborFinset_eq_degree x
    change _ ≤ G.distEven x at h
    change _ + (X ∪ S).card ≤ _
    omega
  have qc : Q.card + G.degree y + G.degree z = U.card + C.card := by
    have h1 := Finset.card_sdiff_add_card_inter X S
    have h2 := Finset.card_union_add_card_inter X S
    have h3 := Finset.card_union_add_card_inter Y Z
    have hy : Y.card = G.degree y := G.card_neighborFinset_eq_degree y
    have hz : Z.card = G.degree z := G.card_neighborFinset_eq_degree z
    change S.card+C.card=Y.card+Z.card at h3
    change (X \ S).card+_+_=(X ∪ S).card+C.card
    omega
  have ics : I.card + 1 ≤ C.card := by
    have notI : x ∉ I := fun h => (G.loopless.irrefl x) ((memN _ _).mp (mem_inter.mp h).2)
    have sub : insert x I ⊆ C := by
      intro b hb
      rcases mem_insert.mp hb with rfl|hh
      · exact mem_inter.mpr ⟨(memN _ _).mpr hxy.symm,(memN _ _).mpr hxz.symm⟩
      · exact (mem_inter.mp hh).1
    have hh := card_le_card sub
    rwa [card_insert_of_notMem notI] at hh
  have qs : Q ⊆ E y ∩ E z := by
    intro w hw
    obtain ⟨hh,hn⟩ := mem_sdiff.mp hw
    exact mem_inter.mpr ⟨near_even y x w hxy.symm ((memN _ _).mp hh)
      (fun h => hn (mem_union_left _ ((memN _ _).mpr h))),
      near_even z x w hxz.symm ((memN _ _).mp hh)
      (fun h => hn (mem_union_right _ ((memN _ _).mpr h)))⟩
  let row (a : V) := T.filter (fun w => G.Adj a w ∧ G.dist x w = G.dist x a+1)
  have rcap (a : V) : (row a).card ≤ k := by
    by_cases hn : (row a).Nonempty
    · obtain ⟨w,hw⟩ := hn
      obtain ⟨ht,_,he⟩ := mem_filter.mp hw
      have hh := (mem_filter.mp ht).2.1
      obtain ⟨b,hb,hab⟩ := predecessor (G := G) (x := x) (z := a) (j := G.dist x a-1) (by omega)
      have hs : insert b (row a) ⊆ E b := by
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
        · obtain ⟨_,hav,hvlen⟩ := mem_filter.mp hv
          have hlu := hc.dist_triangle (u := b) (v := a) (w := v)
          rw [dist_eq_one_iff_adj.mpr hab,dist_eq_one_iff_adj.mpr hav] at hlu
          have hlo := hc.dist_triangle (u := x) (v := b) (w := v)
          exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
      have hnb : b ∉ row a := by intro h; have := (mem_filter.mp h).2.2; omega
      have hsize := (card_le_card hs).trans (ecap b)
      rw [Finset.card_insert_of_notMem hnb] at hsize
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have tr : T ⊆ A.biUnion row := by
    intro w hw
    obtain ⟨hx,hy,hz,ho⟩ := (mem_filter.mp hw).2
    obtain ⟨a,ha,haw⟩ := predecessor (G := G) (x := x) (z := w) (j := G.dist x w-1) (by omega)
    have he : Even (G.dist x a) := by rw [Nat.even_iff] at ho ⊢; omega
    have naux (v : V) (hf : 3 ≤ G.dist v w) (hh : G.Adj v a) : False := by
      have ht := hc.dist_triangle (u := v) (v := a) (w := w)
      rw [dist_eq_one_iff_adj.mpr hh,dist_eq_one_iff_adj.mpr haw] at ht
      omega
    have hs : a ∉ S := by
      intro h
      rcases mem_union.mp h with yy|zz
      · exact naux y hy ((memN _ _).mp yy)
      · exact naux z hz ((memN _ _).mp zz)
    exact mem_biUnion.mpr ⟨a,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,he⟩,hs⟩,
      mem_filter.mpr ⟨hw,haw,by omega⟩⟩
  have tc : T.card ≤ k*A.card := calc
    T.card ≤ (A.biUnion row).card := card_le_card tr
    _ ≤ ∑ a ∈ A, (row a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, k := Finset.sum_le_sum fun a _ => rcap a
    _ = _ := by simp [Nat.mul_comm]
  have all : univ ⊆ (((E y ∪ E z) ∪ E x) ∪ I) ∪ T := by
    intro v _
    by_cases ey : Even (G.dist y v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,ey⟩))))
    by_cases ez : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ez⟩))))
    by_cases ex : Even (G.dist x v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ex⟩)))
    have y1 := hc.dist_triangle (u:=x) (v:=y) (w:=v)
    have y2 := hc.dist_triangle (u:=y) (v:=x) (w:=v)
    have z1 := hc.dist_triangle (u:=x) (v:=z) (w:=v)
    have z2 := hc.dist_triangle (u:=z) (v:=x) (w:=v)
    rw [dist_eq_one_iff_adj.mpr hxy] at y1
    rw [dist_eq_one_iff_adj.mpr hxy.symm] at y2
    rw [dist_eq_one_iff_adj.mpr hxz] at z1
    rw [dist_eq_one_iff_adj.mpr hxz.symm] at z2
    have ox := ex
    rw [Nat.even_iff] at ox ey ez
    by_cases hl : 3 ≤ G.dist x v
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hl,by omega,by omega,ex⟩)
    · have nx (a : V) (h : G.dist a v = 1) := (memN a v).mpr (dist_eq_one_iff_adj.mp h)
      exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨mem_inter.mpr ⟨nx y (by omega),nx z (by omega)⟩,nx x (by omega)⟩))
  have count := card_le_card all
  rw [card_univ] at count
  have h1 := Finset.card_union_add_card_inter (E y) (E z)
  have h2 := Finset.card_union_le (E y ∪ E z) (E x)
  have h3 := Finset.card_union_le ((E y ∪ E z) ∪ E x) I
  have h4 := Finset.card_union_le (((E y ∪ E z) ∪ E x) ∪ I) T
  have h5 := card_le_card qs
  have ecx := ecap x
  have ecy := ecap y
  have ecz := ecap z
  have hh : Fintype.card V + Q.card ≤ 3*k+2+C.card + k*A.card := by omega
  have hm := Nat.mul_le_mul_left k ac
  rw [Nat.mul_add, Nat.add_comm (G.distEven x) (G.degree x)] at hm
  change Fintype.card V + (k+1)*U.card ≤ _
  rw [Nat.add_mul, Nat.one_mul]
  omega

end WedgeCount

section WedgeOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Above the local degree-excess threshold, this wedge satisfies the local Ore condition. -/
private theorem local_ore_of_order (hc : G.Connected) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : ¬G.Adj y z)
    {k r : ℕ} (cap : ∀ v, G.distEven v ≤ k+1)
    (hdeg : G.degree x + G.distEven x ≤ G.degree y + G.degree z + r + 1)
    (hn : (3+r)*k+1 < Fintype.card V) :
    (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card ≤ G.degree y + G.degree z := by
  have h := wedge_order hc hxy hxz hyz cap
  let U := (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card
  change U ≤ G.degree y + G.degree z
  change Fintype.card V + (k+1)*U ≤ _ at h
  by_contra! bad
  have hm := Nat.mul_le_mul_left k (show G.degree y+G.degree z+1 ≤ U by omega)
  have hd := Nat.mul_le_mul_left k hdeg
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add k (G.degree x) (G.distEven x)] at h
  rw [Nat.add_mul, Nat.mul_comm r k] at hn
  simp only [Nat.mul_add, Nat.mul_one] at hm hd
  omega

end WedgeOrder

section RootedTrace

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A local Ore bound away from a single prescribed vertex gives a spanning
path starting at that vertex. -/
private theorem rooted_local_ore (hc : G.Connected) (z : V)
    (ore : ∀ {u w v : V}, u ≠ z → v ≠ z → G.Adj u w → G.Adj w v → ¬G.Adj u v →
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
        G.degree u + G.degree v) :
    ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian := by
  obtain ⟨v,P,hp,longest⟩ := exists_rooted_longest G z
  refine ⟨v,P,hp.isHamiltonian_iff.mpr ?_⟩
  intro x
  by_contra hx
  obtain ⟨u,hu,hcP⟩ := exists_exterior_contact P hc ⟨x,hx⟩
  obtain ⟨W,succ,hn,hi,ht,hm,ha,hc',hs,huz⟩ :=
    successors_of_rooted_longest P hp longest hu hcP
  obtain ⟨w,hw,hbad⟩ := bad_wedge_of_successors u W succ hn hi ht hm ha hc'
  exact (not_lt_of_ge (ore huz (hs _ hw).2 (ht _ hw) (hs _ hw).1 (hm _ hw).2)) hbad

end RootedTrace
/-- The range from the parent order threshold through three times the second-smallest degree plus two. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    Fintype.card V ≤ 3 * secondSmallestDegree G + 2 →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- The larger-order range with a local Ore obstruction at a higher-degree center. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    3 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∃ u w v : V,
      G.Adj u w ∧ G.Adj w v ∧ ¬ G.Adj u v ∧
      secondSmallestDegree G ≤ G.degree u ∧ secondSmallestDegree G ≤ G.degree v ∧
      G.degree u < G.degree w ∧ G.degree v < G.degree w ∧
      G.degree u + G.degree v <
        (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ∧
      Fintype.card V ≤ 3 * secondSmallestDegree G + 1 +
        secondSmallestDegree G * (G.degree w - max (G.degree u) (G.degree v))) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H2 := by
  intro smallCase obstructionCase V _ _ _ G _ hc cap parentOrder connectedDeletion
  classical
  by_cases small : Fintype.card V ≤ 3 * secondSmallestDegree G + 2
  · exact smallCase G hc cap parentOrder connectedDeletion small
  let k := secondSmallestDegree G
  have large : 3 * k + 3 ≤ Fintype.card V := by
    change ¬ Fintype.card V ≤ 3 * k + 2 at small
    omega
  have evenCap (x : V) : G.distEven x ≤ k + 1 := by
    simpa only [k, Nat.add_comm] using cap x
  obtain ⟨z, hz⟩ := G.exists_minimal_degree_vertex
  have high (x : V) (hx : x ≠ z) : k ≤ G.degree x := by
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.degree_pair
        (G := G) x z hx with h | h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree x)
  by_contra fail
  have ore {u w v : V} (huz : u ≠ z) (hvz : v ≠ z)
      (huw : G.Adj u w) (hwv : G.Adj w v) (huv : ¬ G.Adj u v) :
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
        G.degree u + G.degree v := by
    by_contra! bad
    have hu := high u huz
    have hv := high v hvz
    have hd : max (G.degree u) (G.degree v) + k ≤ G.degree u + G.degree v := by
      rcases le_total (G.degree u) (G.degree v) with h | h
      · rw [max_eq_right h]
        omega
      · rw [max_eq_left h]
        omega
    have greater : max (G.degree u) (G.degree v) < G.degree w := by
      by_contra! le
      have localDeg : G.degree w + G.distEven w ≤ G.degree u + G.degree v + 0 + 1 := by
        have := evenCap w
        omega
      have highOrder : (3 + 0) * k + 1 < Fintype.card V := by
        omega
      have bound := local_ore_of_order hc huw.symm hwv huv evenCap localDeg highOrder
      have bound' :
          (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
            G.degree u + G.degree v := by
        simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using bound
      exact (not_lt_of_ge bound') bad
    have orderBound : Fintype.card V ≤ 3 * k + 1 +
        k * (G.degree w - max (G.degree u) (G.degree v)) := by
      by_contra! outside
      let r := G.degree w - max (G.degree u) (G.degree v)
      have localDeg : G.degree w + G.distEven w ≤ G.degree u + G.degree v + r + 1 := by
        have := evenCap w
        dsimp only [r]
        omega
      have highOrder : (3 + r) * k + 1 < Fintype.card V := by
        change 3 * k + 1 + k * r < Fintype.card V at outside
        rw [Nat.add_mul, Nat.mul_comm r k]
        omega
      have bound := local_ore_of_order hc huw.symm hwv huv evenCap localDeg highOrder
      have bound' :
          (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
            G.degree u + G.degree v := by
        simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using bound
      exact (not_lt_of_ge bound') bad
    exact fail (obstructionCase G hc cap parentOrder connectedDeletion large
      ⟨u, w, v, huw, hwv, huv, hu, hv, lt_of_le_of_lt (le_max_left _ _) greater,
        lt_of_le_of_lt (le_max_right _ _) greater, bad, orderBound⟩)
  obtain ⟨v, p, hp⟩ := rooted_local_ore hc z ore
  exact fail ⟨z, v, p, hp⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1

namespace Graph189ParentAssembly

theorem parent_of_two_connected_cases
    (moderate : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1.H1)
    (large : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1.H2) :
    type_of% @WrittenOnTheWallII.GraphConjecture189.conjecture189 := by
  exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.main cutVertex (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1.main moderate large)

end Graph189ParentAssembly
