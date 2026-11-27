import BalancedBipartiteCycle
import Mathlib.Data.Finset.Option

namespace BalancedBipartite

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- Delete a chosen vertex from a cyclic spanning ordering, retaining a
linear ordering of every other vertex. -/
theorem HasSpanningCycle.delete_vertex (h : HasSpanningCycle G) (v : V) :
    ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ v ∉ l ∧ ∀ w : V, w ≠ v → w ∈ l := by
  obtain ⟨l,a,b,hn,hall,hc,ha,hb,hba⟩ := h
  obtain ⟨P,Q,he⟩ := List.append_of_mem (hall v)
  rw [he] at hn hall hc ha hb
  have hd := List.nodup_append.mp hn
  have hvQ := (List.nodup_cons.mp hd.2.1).1
  have hvP : v ∉ P := fun hp => hd.2.2 v hp v (by simp) rfl
  have hdis : P.Disjoint Q := fun x hx hy => hd.2.2 x hx x (by simp [hy]) rfl
  have hQ := (List.nodup_cons.mp hd.2.1).2
  have hPc := hc.left_of_append
  have hQc := hc.right_of_append.tail
  refine ⟨Q++P,hQ.append hd.1 hdis.symm,?_,?_,?_⟩
  · by_cases hp : P = []
    · simpa [hp] using hQc
    by_cases hq : Q = []
    · simpa [hq] using hPc
    have hPa : P.head? = some a := by rwa [List.head?_append_of_ne_nil _ hp] at ha
    have hQb : Q.getLast? = some b := by
      rw [List.getLast?_append_of_ne_nil _ (by simp)] at hb
      simpa only [List.getLast?_cons_of_ne_nil hq] using hb
    exact join_chain hQc hPc hQb hPa hba
  · simp [hvP,hvQ]
  · intro w hne
    have hm := hall w
    simp only [List.mem_append,List.mem_cons,hne,false_or] at hm
    exact List.mem_append.mpr hm.symm

def paddedGraph (G : SimpleGraph V) (col : V → Bool) (c : Bool) : SimpleGraph (Option V) where
  Adj x y :=
    match x,y with
    | some a, some b => G.Adj a b
    | some a, none => col a ≠ c
    | none, some b => col b ≠ c
    | none, none => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> simp [G.adj_comm]⟩
  loopless := ⟨by
    intro x
    cases x <;> simp⟩

def paddedColor (col : V → Bool) (c : Bool) (v : Option V) : Bool :=
  v.elim c col

theorem paddedGraph.colored {col : V → Bool} {c : Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    {u v : Option V} (h : (paddedGraph G col c).Adj u v) :
    paddedColor col c u ≠ paddedColor col c v := by
  cases u <;> cases v
  · exact h.elim
  · exact fun he => h he.symm
  · exact h
  · exact hcol h

theorem paddedGraph.traceable [DecidableEq V] [Nonempty V] {col : V → Bool} {c : Bool}
    (h : HasSpanningCycle (paddedGraph G col c)) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨w,hn,hc,hno,hcover⟩ := h.delete_vertex none
  let l := w.filterMap id
  have hrestore (u : List (Option V)) (hu : none ∉ u) : (u.filterMap id).map some = u := by
    induction u with
    | nil => rfl
    | cons z u ih =>
      cases z with
      | none => exact (hu (by simp)).elim
      | some a =>
        have hu' : (none : Option V) ∉ u := fun h => hu (by simp [h])
        simpa using congrArg (some a :: ·) (ih hu')
  have hl : l.map some = w := hrestore w hno
  have hlno : l.Nodup := (List.nodup_map_iff (Option.some_injective V)).mp (hl.symm ▸ hn)
  have hlc : l.IsChain G.Adj := by
    have hmap : (l.map some).IsChain (paddedGraph G col c).Adj := hl.symm ▸ hc
    exact List.isChain_of_isChain_map some (fun _ _ hh => hh) hmap
  have hmem (v : V) : v ∈ l := by
    have hsome : some v ∈ l.map some := hl.symm ▸ hcover (some v) (by simp)
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hsome
    exact (Option.some.inj he) ▸ hz
  have hne : l ≠ [] := List.ne_nil_of_mem (hmem (Classical.choice inferInstance))
  let p := Walk.ofSupport l hne hlc
  have hs : p.support = l := Walk.support_ofSupport hne hlc
  exact ⟨_,_,p,(Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun v => by rw [hs]; exact hmem v)⟩

theorem padded_part_card [Fintype V] [DecidableEq V] (col : V → Bool) (c b : Bool) :
    (univ.filter fun v : Option V => paddedColor col c v = b).card =
      (univ.filter fun v : V => col v = b).card + if c=b then 1 else 0 := by
  classical
  let S : Finset (Option V) := univ.filter fun v => paddedColor col c v = b
  let T : Finset V := univ.filter fun v => col v=b
  have he : S.erase none = T.map Function.Embedding.some := by
    ext v
    cases v with
    | none => simp
    | some a =>
      have hs : some a ∈ S ↔ col a=b := by
        rw [mem_filter]
        exact and_iff_right (mem_univ _)
      simp [hs,T]
  change S.card = T.card + if c=b then 1 else 0
  by_cases h : c=b
  · have hm : none ∈ S := by simp [S,paddedColor,h]
    have hd := Finset.card_erase_of_mem hm
    have hpos := card_pos.mpr ⟨none,hm⟩
    rw [he,card_map] at hd
    simp only [h,if_true]
    omega
  · have hm : none ∉ S := fun hm => h ((mem_filter.mp hm).2)
    rw [Finset.erase_eq_of_notMem hm] at he
    simp [he,h]

theorem degree_le_padded [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {col : V → Bool} {c : Bool} [DecidableRel (paddedGraph G col c).Adj] (v : V) :
    G.degree v ≤ (paddedGraph G col c).degree (some v) := by
  classical
  have hsub : (G.neighborFinset v).image some ⊆
      (paddedGraph G col c).neighborFinset (some v) := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
    exact ((paddedGraph G col c).mem_neighborFinset (some v) (some z)).mpr
      ((G.mem_neighborFinset v z).mp hz)
  have h := card_le_card hsub
  rw [card_image_of_injective _ (Option.some_injective V)] at h
  exact h

theorem degree_succ_le_padded [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {col : V → Bool} {c : Bool} [DecidableRel (paddedGraph G col c).Adj] {v : V}
    (hv : col v ≠ c) :
    G.degree v + 1 ≤ (paddedGraph G col c).degree (some v) := by
  classical
  let S := (G.neighborFinset v).image some
  have hnone : (none : Option V) ∉ S := by simp [S]
  have hsub : insert none S ⊆ (paddedGraph G col c).neighborFinset (some v) := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact ((paddedGraph G col c).mem_neighborFinset (some v) none).mpr hv
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
      exact ((paddedGraph G col c).mem_neighborFinset (some v) (some z)).mpr
        ((G.mem_neighborFinset v z).mp hz)
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hnone] at hc
  change ((G.neighborFinset v).image some).card + 1 ≤ _ at hc
  rwa [card_image_of_injective _ (Option.some_injective V)] at hc

/-- When one bipartition class is short by one vertex, fill that class
with a new universal cross vertex and delete it from the spanning cycle. -/
theorem traceable_of_padded_cross_degree_sum [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableRel G.Adj] {r : ℕ} (hr : 2 ≤ r) {col : V → Bool} (c : Bool)
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hsmall : (univ.filter fun v => col v = c).card+1 = r)
    (hlarge : (univ.filter fun v => col v ≠ c).card = r)
    (hdeg : ∀ ⦃x y⦄, col x ≠ col y → ¬ G.Adj x y → r ≤ G.degree x + G.degree y) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let J := paddedGraph G col c
  let C := paddedColor col c
  have hfalse : (univ.filter fun v => C v = false).card = r := by
    rw [padded_part_card]
    cases c <;> simp_all
  have htrue : (univ.filter fun v => C v = true).card = r := by
    rw [padded_part_card]
    cases c <;> simp_all
  have hJcol : ∀ ⦃x y⦄, J.Adj x y → C x ≠ C y :=
    fun _ _ h => paddedGraph.colored hcol h
  have hJdeg : ∀ ⦃x y⦄, C x ≠ C y → ¬ J.Adj x y → r+1 ≤ J.degree x+J.degree y := by
    intro x y hxy hne
    cases x <;> cases y
    · exact (hxy rfl).elim
    · exact (hne hxy.symm).elim
    · exact (hne hxy).elim
    · rename_i x y
      have hbase := hdeg hxy hne
      by_cases hx : col x = c
      · have hy : col y ≠ c := fun hy => hxy (hx.trans hy.symm)
        have hxle := degree_le_padded (G:=G) (col:=col) (c:=c) x
        have hyle := degree_succ_le_padded (G:=G) hy
        change r+1 ≤ (paddedGraph G col c).degree (some x) +
          (paddedGraph G col c).degree (some y)
        omega
      · have hxle := degree_succ_le_padded (G:=G) hx
        have hyle := degree_le_padded (G:=G) (col:=col) (c:=c) y
        change r+1 ≤ (paddedGraph G col c).degree (some x) +
          (paddedGraph G col c).degree (some y)
        omega
  exact paddedGraph.traceable (cycle_of_cross_degree_sum hr hJcol hfalse htrue hJdeg)

#print axioms HasSpanningCycle.delete_vertex
#print axioms traceable_of_padded_cross_degree_sum

end BalancedBipartite
