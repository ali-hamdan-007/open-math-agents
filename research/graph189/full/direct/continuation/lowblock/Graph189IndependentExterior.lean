import Graph189ExteriorDegree
import Graph189SingleExteriorShift
import Graph189ExteriorPopulation

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

private theorem count_two {V : Type*} [Fintype V] {G : SimpleGraph V} (U : Finset V) {x : V} {k : ℕ}
    (two : ∀ v ∈ U, G.dist x v = 2) (cap : G.distEven x ≤ k+1) : U.card ≤ k := by
  classical
  have nx : x ∉ U := by intro hx; have h := two _ hx; simp at h
  have sub : insert x U ⊆ univ.filter (fun v => Even (G.dist x v)) := by
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|h
    · simp
    · rw [two v h]; decide
  have bound := card_le_card sub
  rw [card_insert_of_notMem nx] at bound
  change U.card+1 ≤ G.distEven x at bound
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the deletion of an arbitrary vertex w, any initially high vertex isolated
outside the longest path uses its entire original even budget on the path and
must be adjacent to w in the original graph. -/
theorem high_isolated_saturation (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (a : {u : V | u ≠ w}) (outside : a ∉ p.support)
    (isolated : ∀ b, (G.induce {u : V | u ≠ w}).Adj a b → b ∈ p.support)
    {k : ℕ} (pos : 2 ≤ k) (high : k ≤ G.degree a.val) (cap : G.distEven a.val ≤ k+1) :
    G.Adj a.val w ∧
    (p.support.toFinset.filter (fun v => (G.induce {u : V | u ≠ w}).dist a v = 2)).card = k := by
  classical
  let H := G.induce {u : V | u ≠ w}
  have sub : H.neighborFinset a ⊆ p.support.toFinset := by
    intro b hb
    exact List.mem_toFinset.mpr (isolated b ((H.mem_neighborFinset _ _).mp hb))
  have size : (contactPositions p a).card = H.degree a := by
    rw [contact_card_neighbors p hp,inter_eq_left.mpr sub,H.card_neighborFinset_eq_degree]
  have lost := degree_le_deletion_add_one (G:=G) w a
  change G.degree a.val ≤ H.degree a + 1 at lost
  have touch : (contactPositions p a).Nonempty := card_pos.mp (by omega)
  have least := single_positions_lt_path_shell p hp longest outside touch
  rw [size] at least
  let Q := p.support.toFinset.filter (fun v => H.dist a v = 2)
  have small : Q.card ≤ k := by
    have incl : Q ⊆ exactTwo H a := fun _ h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
    exact (card_le_card incl).trans (induced_second_layer _ a cap)
  change H.degree a+1 ≤ Q.card at least
  refine ⟨?_,by change Q.card = k; omega⟩
  by_contra no
  have same : H.degree a = G.degree a.val := by
    rw [degree_induce_filter]
    have eq : (G.neighborFinset a.val).filter (fun u => u ∈ {v : V | v ≠ w}) =
        G.neighborFinset a.val := by
      apply filter_eq_self.mpr
      intro v hv h
      exact no (Eq.mp (congrArg (G.Adj a.val) h) ((G.mem_neighborFinset a.val v).mp hv))
    rw [eq,G.card_neighborFinset_eq_degree]
  omega

/-- If the exterior is independent, two different originally high omitted
vertices would share w as an additional exact distance-two witness. -/
theorem unique_high_isolated (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (independent : ∀ a ∉ p.support, ∀ b ∉ p.support, ¬ (G.induce {u : V | u ≠ w}).Adj a b)
    {k : ℕ} (pos : 2 ≤ k) (cap : ∀ v, G.distEven v ≤ k+1)
    {a b : {u : V | u ≠ w}} (ha : a ∉ p.support) (hb : b ∉ p.support)
    (ahigh : k ≤ G.degree a.val) (bhigh : k ≤ G.degree b.val) : a = b := by
  classical
  by_contra diff
  have isolated (c : {u : V | u ≠ w}) (hc : c ∉ p.support) (t : {u : V | u ≠ w})
      (adj : (G.induce {u : V | u ≠ w}).Adj c t) : t ∈ p.support := by
    by_contra h
    exact independent c hc t h adj
  obtain ⟨aw,full⟩ := high_isolated_saturation w p hp longest a ha (isolated a ha) pos ahigh (cap a.val)
  obtain ⟨bw,_⟩ := high_isolated_saturation w p hp longest b hb (isolated b hb) pos bhigh (cap b.val)
  have extTwo : G.dist a.val b.val = 2 := two_step_metric
    (fun eq => diff (Subtype.ext eq)) (independent a ha b hb) aw bw
  let f : {u : V | u ≠ w} ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let Q := p.support.toFinset.filter (fun v => (G.induce {u : V | u ≠ w}).dist a v = 2)
  have missing : b.val ∉ Q.map f := by
    intro h
    obtain ⟨t,ht,eq⟩ := mem_map.mp h
    have same : t = b := Subtype.ext eq
    exact hb (same ▸ List.mem_toFinset.mp (mem_filter.mp ht).1)
  have cost := count_two (insert b.val (Q.map f)) (x:=a.val) (k:=k) (by
    intro v hv
    rcases mem_insert.mp hv with rfl|hm
    · exact extTwo
    · obtain ⟨t,ht,rfl⟩ := mem_map.mp hm
      exact original_dist_two (mem_filter.mp ht).2) (cap a.val)
  rw [card_insert_of_notMem missing,card_map] at cost
  change Q.card=k at full
  omega

/-- An independent exterior in any single-vertex deletion misses at most two
vertices of the deletion, including the one possible original low vertex. -/
theorem independent_omits_at_most_two [Nontrivial V] (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (independent : ∀ a ∉ p.support, ∀ b ∉ p.support, ¬ (G.induce {u : V | u ≠ w}).Adj a b)
    (pos : 2 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    (univ.filter (fun v => v ∉ p.support)).card ≤ 2 := by
  classical
  let X := univ.filter (fun v => v ∉ p.support)
  let high (a : {u : V | u ≠ w}) := G.secondSmallestDegree ≤ G.degree a.val
  have one : (X.filter high).card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨ha,ah⟩ := mem_filter.mp ha
    obtain ⟨hb,bh⟩ := mem_filter.mp hb
    exact unique_high_isolated w p hp longest independent pos cap (mem_filter.mp ha).2 (mem_filter.mp hb).2 ah bh
  have low : (X.filter (fun a => ¬high a)).card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro a b ha hb
    by_contra h
    have vne : a.val ≠ b.val := fun eq => h (Subtype.ext eq)
    exact (degree_pair (G:=G) a.val b.val vne).elim (mem_filter.mp ha).2 (mem_filter.mp hb).2
  have part := card_filter_add_card_filter_not (s:=X) (p:=high)
  change X.card ≤ 2
  omega

#print axioms independent_omits_at_most_two
#print axioms high_isolated_saturation
#print axioms unique_high_isolated
end Graph189ExteriorDegreeCycle
