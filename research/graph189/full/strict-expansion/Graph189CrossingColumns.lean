module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Finset.Card

/-! Two disjoint full columns force a crossing column to have size two.
The hypothesis only bounds distance two, as in the strict-expansion theorem.
Owner credit: @ali-hamdan-007. Agent: Codex (GPT-6). -/

@[expose] public section

namespace Graph189CrossingColumns

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def column (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (c : V) : Finset V :=
  S.filter (G.Adj c)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem dist_two {x z c : V} (hne : x ≠ z) (hn : ¬G.Adj x z)
    (hcx : G.Adj c x) (hcz : G.Adj c z) : G.dist x z = 2 := by
  let w : G.Walk x z := .cons hcx.symm (.cons hcz .nil)
  have hlow := w.reachable.one_lt_dist_of_ne_of_not_adj hne hn
  have hhi : G.dist x z ≤ 2 := G.dist_le w
  omega

/-- A row meeting two columns sees the union except itself at distance two. -/
theorem union_card_le {S : Finset V} {k : ℕ}
    (hind : ∀ x ∈ S, ∀ z ∈ S, ¬G.Adj x z)
    (hcap : ∀ x ∈ S, (univ.filter (fun v => G.dist x v = 2)).card ≤ k)
    {p q x : V} (hp : x ∈ column G S p) (hq : x ∈ column G S q) :
    (column G S p ∪ column G S q).card ≤ k + 1 := by
  classical
  let U := column G S p ∪ column G S q
  obtain ⟨hxS, hpx⟩ := mem_filter.mp hp
  have hinc : U.erase x ⊆ univ.filter (fun v => G.dist x v = 2) := by
    intro z hz
    obtain ⟨hne, hzU⟩ := mem_erase.mp hz
    rcases mem_union.mp hzU with h | h
    · obtain ⟨hzS, hpz⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨mem_univ _, dist_two hne.symm (hind x hxS z hzS) hpx hpz⟩
    · obtain ⟨hzS, hqz⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨mem_univ _, dist_two hne.symm (hind x hxS z hzS)
        (mem_filter.mp hq).2 hqz⟩
  have hle := (card_le_card hinc).trans (hcap x hxS)
  have he := card_erase_add_one (show x ∈ U from mem_union_left _ hp)
  change U.card ≤ k + 1
  omega

/-- A column meeting two disjoint full columns has one row in each and no others. -/
theorem crossing_column_eq_pair {S : Finset V} {k : ℕ}
    (hind : ∀ x ∈ S, ∀ z ∈ S, ¬G.Adj x z)
    (hcap : ∀ x ∈ S, (univ.filter (fun v => G.dist x v = 2)).card ≤ k)
    {p q c x y : V}
    (hp : (column G S p).card = k) (hq : (column G S q).card = k)
    (hdis : Disjoint (column G S p) (column G S q))
    (hxp : x ∈ column G S p) (hxc : x ∈ column G S c)
    (hyq : y ∈ column G S q) (hyc : y ∈ column G S c) :
    x ≠ y ∧ column G S c = {x, y} := by
  classical
  let A := column G S p
  let B := column G S q
  let C := column G S c
  have hU := union_card_le hind hcap hxc hxp
  have hV := union_card_le hind hcap hyc hyq
  have hDA := card_sdiff_add_card C A
  have hDB := card_sdiff_add_card C B
  have hA : (C \ A).card ≤ 1 := by change (C ∪ A).card ≤ k+1 at hU; change A.card = k at hp; omega
  have hB : (C \ B).card ≤ 1 := by change (C ∪ B).card ≤ k+1 at hV; change B.card = k at hq; omega
  have hxB : x ∉ B := disjoint_left.mp hdis hxp
  have hyA : y ∉ A := disjoint_right.mp hdis hyq
  refine ⟨fun he => hxB (he ▸ hyq), ?_⟩
  apply Finset.Subset.antisymm
  · intro z hz
    by_cases hzA : z ∈ A
    · have hzB : z ∉ B := disjoint_left.mp hdis hzA
      have hxz := card_le_one.mp hB z (mem_sdiff.mpr ⟨hz, hzB⟩) x (mem_sdiff.mpr ⟨hxc, hxB⟩)
      simp [hxz]
    · have hyz := card_le_one.mp hA z (mem_sdiff.mpr ⟨hz, hzA⟩) y (mem_sdiff.mpr ⟨hyc, hyA⟩)
      simp [hyz]
  · intro z hz
    rcases mem_insert.mp hz with rfl | h
    · exact hxc
    · exact mem_singleton.mp h ▸ hyc

/-- Relative to a fixed full column, two other full columns that touch it
cannot introduce different outside rows. This bounds the entire union of an
intersecting class of full columns by k+1, irrespective of its size. -/
theorem full_columns_same_outsider {S : Finset V} {k : ℕ} (hk : 3 ≤ k)
    (hind : ∀ x ∈ S, ∀ z ∈ S, ¬G.Adj x z)
    (hcap : ∀ x ∈ S, (univ.filter (fun v => G.dist x v = 2)).card ≤ k)
    {a p q x y : V}
    (ha : (column G S a).card = k)
    (hp : (column G S p).card = k) (hq : (column G S q).card = k)
    (hAP : (column G S a ∩ column G S p).Nonempty)
    (hAQ : (column G S a ∩ column G S q).Nonempty)
    (hx : x ∈ column G S p \ column G S a)
    (hy : y ∈ column G S q \ column G S a) : x = y := by
  classical
  let A := column G S a
  let P := column G S p
  let Q := column G S q
  obtain ⟨u, hu⟩ := hAP
  obtain ⟨v, hv⟩ := hAQ
  have hU := union_card_le hind hcap (mem_inter.mp hu).1 (mem_inter.mp hu).2
  have hV := union_card_le hind hcap (mem_inter.mp hv).1 (mem_inter.mp hv).2
  have hAP' := card_sdiff_add_card A P
  have hAQ' := card_sdiff_add_card A Q
  change A.card = k at ha
  change P.card = k at hp
  change Q.card = k at hq
  change (A ∪ P).card ≤ k + 1 at hU
  change (A ∪ Q).card ≤ k + 1 at hV
  obtain ⟨r, hrA, hrP, hrQ⟩ : ∃ r ∈ A, r ∈ P ∧ r ∈ Q := by
    by_contra! hn
    have hsub : A ⊆ (A \ P) ∪ (A \ Q) := by
      intro z hz
      by_cases hzP : z ∈ P
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hz, hn z hz hzP⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hz, hzP⟩)
    have hb := (card_le_card hsub).trans (card_union_le _ _)
    omega
  by_contra hne
  obtain ⟨hxP, hxA⟩ := mem_sdiff.mp hx
  obtain ⟨hyQ, hyA⟩ := mem_sdiff.mp hy
  let T := insert y (insert x A)
  have hyx : y ∉ insert x A := by
    simp only [mem_insert, not_or]
    exact ⟨fun h => hne h.symm, hyA⟩
  have hcard : T.card = k + 2 := by
    change (insert y (insert x A)).card = _
    rw [card_insert_of_notMem hyx,
      card_insert_of_notMem hxA, ha]
  have hrT : r ∈ T := mem_insert_of_mem (mem_insert_of_mem hrA)
  have hrowS : r ∈ S := (mem_filter.mp hrA).1
  have hclose {t c : V} (ht : t ≠ r)
      (hr : r ∈ column G S c) (htc : t ∈ column G S c) : G.dist r t = 2 :=
    dist_two ht.symm (hind r hrowS t (mem_filter.mp htc).1)
      (mem_filter.mp hr).2 (mem_filter.mp htc).2
  have hsub : T.erase r ⊆ univ.filter (fun t => G.dist r t = 2) := by
    intro t ht
    obtain ⟨hne', ht⟩ := mem_erase.mp ht
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rcases mem_insert.mp ht with rfl | ht
    · exact hclose hne' hrQ hyQ
    rcases mem_insert.mp ht with rfl | ht
    · exact hclose hne' hrP hxP
    · exact hclose hne' hrA ht
  have hle := (card_le_card hsub).trans (hcap r hrowS)
  have he := card_erase_add_one hrT
  omega

#print axioms full_columns_same_outsider
#print axioms union_card_le
#print axioms crossing_column_eq_pair
end Graph189CrossingColumns
