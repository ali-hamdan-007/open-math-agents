import Graph189CutClassification

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TwofoldCover

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {A B S Y : Finset V}

omit [Fintype V] in
/-- A shortest odd path of length at most four from A to a B vertex
without separator neighbors starts by crossing to a label at distance two. -/
theorem odd_noncontact (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {x y : V} (hx : x ∈ A) (hy : y ∈ B) (bound : G.dist x y ≤ 4)
    (odd : ¬ Even (G.dist x y)) (nonport : ∀ j ∈ S, ¬ G.Adj j y) :
    ∃ j ∈ S, G.Adj x j ∧ G.dist j y = 2 := by
  have nx : G.dist x y ≠ 1 := fun eq => sides.no_cross x hx y hy (dist_eq_one_iff_adj.mp eq)
  have d3 : G.dist x y = 3 := by rw [Nat.even_iff] at odd; omega
  obtain ⟨p,hp⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨j,hj,hm⟩ := sides.meets hx hy p
  have lengths := congrArg SimpleGraph.Walk.length (Walk.take_spec p hm)
  rw [SimpleGraph.Walk.length_append] at lengths
  have left := G.dist_le (p.takeUntil j hm)
  have right := G.dist_le (p.dropUntil j hm)
  have tri := hc.dist_triangle (u:=x) (v:=j) (w:=y)
  have xj : G.dist x j ≠ 0 := fun eq =>
    Finset.disjoint_left.mp sides.left_cut hx ((hc.dist_eq_zero_iff.mp eq).symm ▸ hj)
  have jy : G.dist j y ≠ 0 := fun eq =>
    Finset.disjoint_left.mp sides.right_cut hy ((hc.dist_eq_zero_iff.mp eq) ▸ hj)
  have jy' : G.dist j y ≠ 1 := fun eq => nonport j hj (dist_eq_one_iff_adj.mp eq)
  exact ⟨j,hj,dist_eq_one_iff_adj.mp (by omega),by omega⟩

omit [Fintype V] [DecidableEq V] in
theorem transpose (S Y : Finset V) (r : V → V → Prop) [DecidableRel r] :
    (∑ i ∈ S, (Y.filter (r i)).card) =
      ∑ y ∈ Y, (S.filter (fun i => r i y)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

theorem outside_quota {k : ℕ} (cap : ∀ u, G.distEven u ≤ k+1)
    (Y : Finset V) {u : V} (outside : u ∉ Y) :
    (Y.filter (fun y => Even (G.dist u y))).card ≤ k := by
  classical
  let E := univ.filter (fun y => Even (G.dist u y))
  have su : u ∈ E := by simp [E]
  have incl : Y.filter (fun y => Even (G.dist u y)) ⊆ E.erase u := by
    intro y hy
    obtain ⟨ym,ye⟩ := mem_filter.mp hy
    exact mem_erase.mpr ⟨fun eq => outside (eq ▸ ym),mem_filter.mpr ⟨mem_univ _,ye⟩⟩
  have h := card_le_card incl
  have he := card_erase_add_one su
  have hcap : E.card ≤ k+1 := cap u
  omega

/-- Three labels with high representatives missing precisely the indicated
label force the opposite high population below the separator's total quota. -/
theorem twofold (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {D : Finset V} (sub : D ⊆ S) (three : 3 ≤ D.card) (ys : Y ⊆ B)
    (f : V → V) (rep : ∀ i ∈ D, f i ∈ A)
    (adj : ∀ i ∈ D, ∀ j ∈ S, G.Adj (f i) j ↔ i ≠ j)
    (diam : ∀ i ∈ D, ∀ y ∈ Y, G.dist (f i) y ≤ 4)
    {k : ℕ} (cap : ∀ u, G.distEven u ≤ k+1) : Y.card ≤ S.card*k := by
  classical
  let g (i : V) := if i ∈ D then f i else i
  let E (y : V) := S.filter (fun i => Even (G.dist i y))
  let F (y : V) := S.filter (fun i => Even (G.dist (g i) y))
  have point (y : V) (hy : y ∈ Y) : 2 ≤ (E y).card + (F y).card := by
    by_cases port : ∃ j ∈ S, G.Adj j y
    · obtain ⟨j,hj,edge⟩ := port
      have incl : D.erase j ⊆ F y := by
        intro i hi
        obtain ⟨ne,hd⟩ := mem_erase.mp hi
        have two := Graph189PortDifference.cross_two hc sides (rep i hd) (ys hy)
          ((adj i hd j hj).mpr ne) edge
        exact mem_filter.mpr ⟨sub hd,by simp [g,hd,two]⟩
      have c := card_le_card incl
      by_cases jd : j ∈ D
      · have := card_erase_add_one jd
        omega
      · rw [erase_eq_of_notMem jd] at c
        omega
    push Not at port
    by_cases two : 2 ≤ (E y).card
    · omega
    have oddlabel (i : V) (hi : i ∈ D) (odd : ¬ Even (G.dist (f i) y)) :
        ∃ j ∈ E y, i ≠ j := by
      obtain ⟨j,hj,xj,jy⟩ := odd_noncontact hc sides (rep i hi) (ys hy)
        (diam i hi y hy) odd port
      exact ⟨j,mem_filter.mpr ⟨hj,by simp [jy]⟩,(adj i hi j hj).mp xj⟩
    by_cases existsLabel : (E y).Nonempty
    · obtain ⟨j,hj⟩ := existsLabel
      have je : Even (G.dist j y) := (mem_filter.mp hj).2
      have one : (E y).card ≤ 1 := by omega
      have jf : j ∈ F y := by
        apply mem_filter.mpr
        refine ⟨(mem_filter.mp hj).1,?_⟩
        by_cases jd : j ∈ D
        · simp only [g,if_pos jd]
          by_contra odd
          obtain ⟨u,hu,ne⟩ := oddlabel j jd odd
          exact ne (card_le_one_iff.mp one hj hu)
        · simpa [g,jd] using je
      have epos := card_pos.mpr (show (E y).Nonempty from ⟨j,hj⟩)
      have fpos := card_pos.mpr (show (F y).Nonempty from ⟨j,jf⟩)
      omega
    · have incl : D ⊆ F y := by
        intro i hi
        refine mem_filter.mpr ⟨sub hi,?_⟩
        simp only [g,if_pos hi]
        by_contra odd
        obtain ⟨j,hj,_⟩ := oddlabel i hi odd
        exact existsLabel ⟨j,hj⟩
      have := card_le_card incl
      omega
  have first (i : V) (hi : i ∈ S) : (Y.filter (fun y => Even (G.dist i y))).card ≤ k :=
    outside_quota cap Y (fun hy => Finset.disjoint_left.mp sides.right_cut (ys hy) hi)
  have second (i : V) (hi : i ∈ S) : (Y.filter (fun y => Even (G.dist (g i) y))).card ≤ k := by
    apply outside_quota cap
    by_cases hd : i ∈ D
    · simpa only [g,if_pos hd] using
        (show f i ∉ Y from fun hy => Finset.disjoint_left.mp sides.apart (rep i hd) (ys hy))
    · simpa only [g,if_neg hd] using
        (show i ∉ Y from fun hy => Finset.disjoint_left.mp sides.right_cut (ys hy) hi)
  have p := sum_le_sum point
  have q := sum_le_sum first
  have r := sum_le_sum second
  dsimp only [E,F] at p
  rw [sum_add_distrib, ←transpose S Y (fun i y => Even (G.dist i y)),
    ←transpose S Y (fun i y => Even (G.dist (g i) y))] at p
  simp only [sum_const,smul_eq_mul] at p q r
  omega

variable [Nontrivial V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nontrivial V] in
/-- A unique label at distance two from an opposite noncontact has a
private predecessor in B on a two-edge geodesic. -/
theorem private_predecessor (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {i y : V} (hy : y ∈ B) (hi : i ∈ S) (two : G.dist i y = 2)
    (nonport : ∀ j ∈ S, ¬G.Adj j y)
    (unique : ∀ j ∈ S, G.dist j y = 2 → i = j) :
    ∃ v ∈ B, S.filter (G.Adj v) = {i} := by
  classical
  have ed : G.edist i y = 2 := by rw [←(hc i y).coe_dist_eq_edist,two]; rfl
  obtain ⟨v,hv⟩ := (edist_eq_two_iff.mp ed).2.2
  obtain ⟨iv,yv⟩ := G.mem_commonNeighbors.mp hv
  have vb : v ∈ B := by
    rcases sides.cover v with va | vb | vs
    · exact (sides.no_cross v va y hy yv.symm).elim
    · exact vb
    · exact (nonport v vs yv.symm).elim
  refine ⟨v,vb,?_⟩
  ext j
  constructor
  · intro h
    obtain ⟨js,vj⟩ := mem_filter.mp h
    have ne : j ≠ y := fun eq => Finset.disjoint_left.mp sides.right_cut hy (eq ▸ js)
    have lo := (hc j y).one_lt_dist_of_ne_of_not_adj ne (nonport j js)
    have up := hc.dist_triangle (u:=j) (v:=v) (w:=y)
    rw [dist_eq_one_iff_adj.mpr vj.symm,dist_eq_one_iff_adj.mpr yv.symm] at up
    exact mem_singleton.mpr (unique j js (by omega)).symm
  · rintro h
    obtain rfl := mem_singleton.mp h
    exact mem_filter.mpr ⟨hi,iv.symm⟩

/-- At a cut with a high contact at every label and too many opposite high
vertices, the co-singleton alternative leaves at most two noncommon labels. -/
theorem at_most_two_noncommon (hc : G.Connected)
    (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ u, G.distEven u ≤ 1+G.secondSmallestDegree)
    (big : S.card*G.secondSmallestDegree <
      (B.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card) :
    let X := A.filter (fun x => G.secondSmallestDegree ≤ G.degree x)
    (∀ j ∈ S, ∃ x ∈ X, G.Adj x j) →
    (∀ x ∈ X, (S.filter (fun j => ¬ G.Adj x j ∧ ∃ z ∈ X, G.Adj z j)).card ≤ 1) →
    (S.filter (fun j => ∃ x ∈ X, ¬ G.Adj x j)).card ≤ 2 := by
  classical
  intro X labels family
  let Y := B.filter (fun y => G.secondSmallestDegree ≤ G.degree y)
  let D := S.filter (fun j => ∃ x ∈ X, ¬ G.Adj x j)
  change D.card ≤ 2
  by_contra! three
  have missing (i : V) (hi : i ∈ D) : ∃ x ∈ X, ¬ G.Adj x i := (mem_filter.mp hi).2
  let f (i : V) := if h : i ∈ D then (missing i h).choose else i
  have spec (i : V) (hi : i ∈ D) : f i ∈ X ∧ ¬ G.Adj (f i) i := by
    simpa [f,hi] using (missing i hi).choose_spec
  have cap' (u : V) : G.distEven u ≤ G.secondSmallestDegree+1 := by
    simpa [Nat.add_comm] using cap u
  have adj (i : V) (hi : i ∈ D) (j : V) (hj : j ∈ S) : G.Adj (f i) j ↔ i ≠ j := by
    constructor
    · rintro edge rfl
      exact (spec i hi).2 edge
    · intro ne
      by_contra miss
      have si : i ∈ S := (mem_filter.mp hi).1
      exact ne (card_le_one_iff.mp (family _ (spec i hi).1) (mem_filter.mpr ⟨si,(spec i hi).2,labels i si⟩)
        (mem_filter.mpr ⟨hj,miss,labels j hj⟩))
  have diam (i : V) (hi : i ∈ D) (y : V) (hy : y ∈ Y) : G.dist (f i) y ≤ 4 := by
    have bound := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=f i) (v:=y)).trans
      (diameter_le_five hc cap)
    have ne : G.dist (f i) y ≠ 5 := by
      intro eq
      rcases five_endpoints hc cap' (f i) y eq with h | h
      · exact (not_lt_of_ge (mem_filter.mp (spec i hi).1).2) h
      · exact (not_lt_of_ge (mem_filter.mp hy).2) h
    omega
  exact (not_lt_of_ge (twofold hc sides (D:=D) (Y:=Y) (filter_subset _ _)
    (by omega) (filter_subset _ _) f (fun i hi => (mem_filter.mp (spec i hi).1).1)
    adj diam cap')) big

#print axioms twofold
#print axioms at_most_two_noncommon
end Graph189TwofoldCover
