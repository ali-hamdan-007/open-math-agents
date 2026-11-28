import Graph189CutClassification

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189CoSingleton

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B S D Y : Finset V}

omit [Fintype V] in
/-- An odd geodesic of length at most four from x to an opposite noncontact
must go straight from x to a separator neighbor at distance two from v. -/
theorem odd_to_nonport (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {x v : V} (ax : x ∈ A) (bv : v ∈ B) (np : ∀ j ∈ S, ¬G.Adj j v)
    (near : G.dist x v ≤ 4) (odd : ¬Even (G.dist x v)) :
    ∃ j ∈ S, G.Adj x j ∧ G.dist j v = 2 := by
  classical
  have no : G.dist x v ≠ 1 := fun h => sides.no_cross x ax v bv (dist_eq_one_iff_adj.mp h)
  have three : G.dist x v = 3 := by rw [Nat.even_iff] at odd; omega
  obtain ⟨p,hp⟩ := (hc x v).exists_walk_length_eq_dist
  obtain ⟨j,hj,mem⟩ := sides.meets ax bv p
  have split := congrArg SimpleGraph.Walk.length (Walk.take_spec p mem)
  rw [Walk.length_append] at split
  have left := G.dist_le (p.takeUntil j mem)
  have right := G.dist_le (p.dropUntil j mem)
  have tri := hc.dist_triangle (u:=x) (v:=j) (w:=v)
  have nz : G.dist x j ≠ 0 := fun eq =>
    Finset.disjoint_left.mp sides.left_cut ax ((hc.dist_eq_zero_iff.mp eq).symm ▸ hj)
  have nz' : G.dist j v ≠ 0 := fun eq =>
    Finset.disjoint_left.mp sides.right_cut bv ((hc.dist_eq_zero_iff.mp eq) ▸ hj)
  have none : G.dist j v ≠ 1 := fun h => np j hj (dist_eq_one_iff_adj.mp h)
  exact ⟨j,hj,dist_eq_one_iff_adj.mp (by omega),by omega⟩

private theorem dbl {k : ℕ} (s y : Finset V) (first second : V → V)
    (away : ∀ i ∈ s, first i ∉ y ∧ second i ∉ y) (cap : ∀ v, G.distEven v ≤ k+1)
    (twice : ∀ v ∈ y, 2 ≤ (s.filter (fun i => Even (G.dist (first i) v))).card +
      (s.filter (fun i => Even (G.dist (second i) v))).card) : y.card ≤ s.card*k := by
  classical
  have count (w : V) (nw : w ∉ y) : (y.filter (fun v => Even (G.dist w v))).card ≤ k := by
    let E := univ.filter (fun v => Even (G.dist w v))
    have ew : w ∈ E := by simp [E]
    have sub : y.filter (fun v => Even (G.dist w v)) ⊆ E.erase w := by
      intro v hv
      obtain ⟨hy,he⟩ := mem_filter.mp hv
      exact mem_erase.mpr ⟨fun eq => nw (eq ▸ hy),mem_filter.mpr ⟨mem_univ _,he⟩⟩
    have h := card_le_card sub
    rw [card_erase_of_mem ew] at h
    have b := cap w
    change E.card ≤ k+1 at b
    omega
  have swap (f : V → V) : (∑ v ∈ y, (s.filter (fun i => Even (G.dist (f i) v))).card) =
      ∑ i ∈ s, (y.filter (fun v => Even (G.dist (f i) v))).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have both := Finset.sum_le_sum twice
  rw [Finset.sum_add_distrib,swap first,swap second] at both
  have one := Finset.sum_le_sum (fun i hi => count (first i) (away i hi).1)
  have two := Finset.sum_le_sum (fun i hi => count (second i) (away i hi).2)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at one two both
  omega

/-- With at least three residual labels, co-singleton representatives make
two copies of the separator's even-distance budget cover every high vertex
on the opposite side twice. -/
theorem bound (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (ds : D ⊆ S) (ys : Y ⊆ B) (many : 3 ≤ D.card) {f : V → V}
    (reps : ∀ i ∈ D, f i ∈ A ∧ ¬G.Adj (f i) i ∧ ∀ j ∈ S, j ≠ i → G.Adj (f i) j)
    (diam : ∀ i ∈ D, ∀ v ∈ Y, G.dist (f i) v ≤ 4) {k : ℕ}
    (cap : ∀ v, G.distEven v ≤ k+1) : Y.card ≤ S.card*k := by
  classical
  let g (i : V) := if i ∈ D then f i else i
  have rdis (i : V) (hi : i ∈ S) : i ∉ Y := fun hv => Finset.disjoint_left.mp sides.right_cut (ys hv) hi
  refine dbl (G:=G) S Y id g ?_ cap ?_
  · intro i hi
    refine ⟨rdis i hi,?_⟩
    by_cases d : i ∈ D
    · simpa [g,d] using (show f i ∉ Y from fun hv =>
        Finset.disjoint_left.mp sides.apart (reps i d).1 (ys hv))
    · simpa [g,d] using rdis i hi
  · intro v hv
    let E := S.filter (fun i => Even (G.dist i v))
    let F := S.filter (fun i => Even (G.dist (g i) v))
    change 2 ≤ E.card + F.card
    by_cases port : ∃ j ∈ S, G.Adj j v
    · obtain ⟨j,hj,jv⟩ := port
      have incl : D.erase j ⊆ F := by
        intro i hi
        obtain ⟨ij,id'⟩ := mem_erase.mp hi
        have hit := Graph189PortDifference.cross_two hc sides (reps i id').1 (ys hv) ((reps i id').2.2 j hj ij.symm) jv
        exact mem_filter.mpr ⟨ds id',by simp [g,id',hit]⟩
      have n := card_le_card incl
      by_cases jd : j ∈ D
      · rw [card_erase_of_mem jd] at n; omega
      · rw [erase_eq_of_notMem jd] at n; omega
    · push Not at port
      have miss (i : V) (di : i ∈ D) (skip : ∀ j ∈ E, j=i) : i ∈ F := by
        apply mem_filter.mpr
        refine ⟨ds di,?_⟩
        simp only [g,if_pos di]
        by_contra odd
        obtain ⟨j,hj,hit,dj⟩ := odd_to_nonport hc sides (reps i di).1 (ys hv) port (diam i di v hv) odd
        have eq := skip j (mem_filter.mpr ⟨hj,by simp [dj]⟩)
        exact (reps i di).2.1 (eq ▸ hit)
      by_cases large : 2 ≤ E.card
      · omega
      have unique {i j : V} (hi : i ∈ E) (hj : j ∈ E) : i=j :=
        card_le_one_iff.mp (show E.card ≤ 1 by omega) hi hj
      by_cases empty : E = ∅
      · have incl : D ⊆ F := fun i hi => miss i hi (fun j hj => by simp [empty] at hj)
        have b := card_le_card incl; omega
      · obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        have pos := card_pos.mpr (show E.Nonempty from ⟨j,hj⟩)
        have other : j ∈ F := by
          by_cases jd : j ∈ D
          · exact miss j jd (fun i hi => unique hi hj)
          · exact mem_filter.mpr ⟨(mem_filter.mp hj).1,by simpa [g,jd] using (mem_filter.mp hj).2⟩
        have pos' := card_pos.mpr (show F.Nonempty from ⟨j,other⟩)
        omega

#print axioms odd_to_nonport
#print axioms bound
end Graph189CoSingleton
