import Graph189PrivatePredecessor
import Graph189PortDifference

namespace Graph189FullLabelExit
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

/-- A single high A vertex incident with every separator label forces a high
private B contact at every prescribed label when B has more than sk high vertices. -/
theorem at_every_label (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (big : S.card*G.secondSmallestDegree < (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    {a : V} (ha : a ∈ A) (high : G.secondSmallestDegree ≤ G.degree a)
    (full : ∀ j ∈ S, G.Adj a j) {i : V} (hi : i ∈ S) :
    ∃ b ∈ B, G.secondSmallestDegree ≤ G.degree b ∧ G.Adj i b ∧
      ∀ j ∈ S, G.Adj j b → j = i := by
  classical
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let R := insert a (S.erase i)
  have aout : a ∉ S := disjoint_left.mp sides.left_cut ha
  have ae : a ∉ S.erase i := fun h => aout (mem_erase.mp h).2
  have rc : R.card = S.card := by
    change (insert a (S.erase i)).card = S.card
    rw [card_insert_of_notMem ae]
    exact card_erase_add_one hi
  have dis : Disjoint R Y := by
    apply Finset.disjoint_left.mpr
    intro z hz hzy
    have zb := (mem_filter.mp hzy).1
    rcases mem_insert.mp hz with rfl | ze
    · exact disjoint_left.mp sides.apart ha zb
    · exact disjoint_left.mp sides.right_cut zb (mem_erase.mp ze).2
  have uncovered : ∃ y ∈ Y, ∀ j ∈ R, ¬Even (G.dist j y) := by
    by_contra! fail
    have b := Graph189PortDifference.even_cover (G := G) R Y _ dis cap fail
    rw [rc] at b
    exact (not_lt_of_ge b) big
  obtain ⟨y,hy,odd⟩ := uncovered
  have yB : y ∈ B := (mem_filter.mp hy).1
  have yh : G.secondSmallestDegree ≤ G.degree y := (mem_filter.mp hy).2
  have ao := odd a (mem_insert_self _ _)
  have cap' (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree := by simpa [Nat.add_comm] using cap v
  have max5 := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := a) (v := y)).trans
    (diameter_le_five hc cap')
  have ne5 : G.dist a y ≠ 5 := by
    intro h
    rcases five_endpoints hc cap a y h with h' | h' <;> omega
  have ayn : a ≠ y := fun e => disjoint_left.mp sides.apart ha (e ▸ yB)
  have near := hc.one_lt_dist_of_ne_of_not_adj ayn (sides.no_cross a ha y yB)
  rw [Nat.even_iff] at ao
  have far : G.dist a y = 3 := by omega
  have nonport (j : V) (hj : j ∈ S) : ¬G.Adj y j := by
    intro edge
    have c := hc.dist_triangle (u := a) (v := j) (w := y)
    rw [dist_eq_one_iff_adj.mpr (full j hj),dist_eq_one_iff_adj.mpr edge.symm] at c
    omega
  have sole (j : V) (hj : j ∈ S) (hjy : G.dist j y = 2) : j = i := by
    by_contra ne
    have o := odd j (mem_insert_of_mem (mem_erase.mpr ⟨ne,hj⟩))
    rw [hjy] at o
    exact o (by decide)
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a y
  obtain ⟨j,hj,hmem⟩ := sides.meets ha yB p
  have split := congrArg SimpleGraph.Walk.length (Walk.take_spec p hmem)
  rw [Walk.length_append] at split
  have dl := G.dist_le (p.takeUntil j hmem)
  have dr := G.dist_le (p.dropUntil j hmem)
  have t := hc.dist_triangle (u := a) (v := j) (w := y)
  have one := dist_eq_one_iff_adj.mpr (full j hj)
  have two : G.dist j y = 2 := by omega
  have iy : G.dist i y = 2 := sole j hj two ▸ two
  obtain ⟨b,hb,hbhigh,_,ib,priv⟩ := Graph189PrivatePredecessor.high_private hc sides
    cap hi yB iy nonport sole
  exact ⟨b,hb,hbhigh,ib,priv⟩

omit [Nontrivial V] in
/-- A vertex of A has closed neighborhood contained in A∪S. -/
theorem closed_size (sides : Graph189CutSides.CutSides G A B S) {a : V} (ha : a ∈ A) :
    G.degree a + 1 ≤ A.card+S.card := by
  classical
  have sub : insert a (G.neighborFinset a) ⊆ A ∪ S := by
    intro v h
    rcases mem_insert.mp h with rfl | hv
    · exact mem_union_left _ ha
    · rcases sides.cover v with h | h | h
      · exact mem_union_left _ h
      · exact (sides.no_cross a ha v h ((G.mem_neighborFinset a v).mp hv)).elim
      · exact mem_union_right _ h
  have b := card_le_card sub
  rw [card_insert_of_notMem (G.notMem_neighborFinset_self a),G.card_neighborFinset_eq_degree,
    card_union_of_disjoint sides.left_cut] at b
  exact b

omit [Nontrivial V] in
/-- At the tight side size, every high A member is a full port and is adjacent
to every other A vertex. -/
theorem tight_full (sides : Graph189CutSides.CutSides G A B S) {k : ℕ}
    (tight : A.card+S.card = k+1) {a : V} (ha : a ∈ A) (high : k ≤ G.degree a) :
    ∀ v ∈ A ∪ S, v ≠ a → G.Adj a v := by
  classical
  let U := insert a (G.neighborFinset a)
  have us : U ⊆ A ∪ S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_union_left _ ha
    · rcases sides.cover v with h | h | h
      · exact mem_union_left _ h
      · exact (sides.no_cross a ha v h ((G.mem_neighborFinset a v).mp hv)).elim
      · exact mem_union_right _ h
  have nc : U.card = G.degree a + 1 := by
    dsimp [U]
    rw [card_insert_of_notMem (G.notMem_neighborFinset_self a),G.card_neighborFinset_eq_degree]
  have total := card_union_of_disjoint sides.left_cut
  have same : U = A ∪ S := eq_of_subset_of_card_le us (by omega)
  intro v hv ne
  have vi : v ∈ U := same ▸ hv
  exact (G.mem_neighborFinset a v).mp ((mem_insert.mp vi).resolve_left ne)

/-- The lower endpoint X+s=k forces a private high B contact at a label
adjacent to every A vertex, including the unique low member of A. -/
theorem tight_exit (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (ns : 2 ≤ S.card)
    (big : S.card*G.secondSmallestDegree < (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    (positive : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).Nonempty)
    (tight : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card + S.card = G.secondSmallestDegree) :
    ∃ i ∈ S, ∃ b ∈ B, G.secondSmallestDegree ≤ G.degree b ∧
      S.filter (G.Adj b) = {i} ∧
      G.secondSmallestDegree+1 ≤ S.card+(A ∩ G.neighborFinset i).card := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  change X.card + S.card = _ at tight
  obtain ⟨a,ax⟩ := positive
  obtain ⟨ha,ah⟩ := mem_filter.mp ax
  have cs := closed_size sides ha
  obtain ⟨z,hz,low⟩ : ∃ z ∈ A, ¬ G.secondSmallestDegree ≤ G.degree z := by
    by_contra! h
    have eq : X = A := by ext v; exact ⟨fun hv => (mem_filter.mp hv).1,fun hv => mem_filter.mpr ⟨hv,h v hv⟩⟩
    rw [eq] at tight
    omega
  have high_else {v : V} (ne : v ≠ z) : G.secondSmallestDegree ≤ G.degree v :=
    (degree_pair (G := G) v z ne).resolve_right low
  have eq : insert z X = A := by
    ext v
    constructor
    · intro h
      rcases mem_insert.mp h with rfl | vx
      · exact hz
      · exact (mem_filter.mp vx).1
    · intro hv
      by_cases ne : v = z
      · exact mem_insert.mpr (Or.inl ne)
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hv,high_else ne⟩)
  have nx : z ∉ X := fun h => low (mem_filter.mp h).2
  have cards := congrArg Finset.card eq
  rw [card_insert_of_notMem nx] at cards
  have ac : A.card+S.card = G.secondSmallestDegree+1 := by omega
  have full {v : V} (va : v ∈ A) (vh : G.secondSmallestDegree ≤ G.degree v) (i : V) (hi : i ∈ S) : G.Adj v i :=
    tight_full sides ac va vh i (mem_union_right _ hi)
      (fun eqv => disjoint_left.mp sides.left_cut va (eqv ▸ hi))
  obtain ⟨i,hi,zi⟩ : ∃ i ∈ S, G.Adj z i := by
    by_contra! empty
    have az : G.Adj z a := (tight_full sides ac ha ah z (mem_union_left _ hz) (fun e => low (e ▸ ah))).symm
    have bc := Graph189PrivatePredecessor.nonport_full_neighbor hc sides cap ha hz az (full ha ah) empty
    have sm := Nat.mul_le_mul_right G.secondSmallestDegree ns
    have f := card_filter_le B (fun v => G.secondSmallestDegree ≤ G.degree v)
    omega
  have all (v : V) (hv : v ∈ A) : G.Adj v i := by
    by_cases e : v = z
    · exact e ▸ zi
    · exact full hv (high_else e) i hi
  obtain ⟨b,hb,hh,ib,sole⟩ := at_every_label hc sides cap big ha ah (full ha ah) hi
  have support : S.filter (G.Adj b) = {i} := by
    ext j
    constructor
    · intro h
      obtain ⟨js,edge⟩ := mem_filter.mp h
      exact mem_singleton.mpr (sole j js edge.symm)
    · intro h
      obtain rfl := mem_singleton.mp h
      exact mem_filter.mpr ⟨hi,ib.symm⟩
  have cover : A ∩ G.neighborFinset i = A := by
    apply inter_eq_left.mpr
    intro v hv
    exact (G.mem_neighborFinset i v).mpr (all v hv).symm
  exact ⟨i,hi,b,hb,hh,support,by rw [cover]; omega⟩

/-- Any high vertex on A gives the lower endpoint k≤X+s even if A contains the sole low vertex. -/
theorem high_lower (sides : Graph189CutSides.CutSides G A B S)
    {a : V} (ha : a ∈ A) (high : G.secondSmallestDegree ≤ G.degree a) :
    G.secondSmallestDegree ≤ (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card + S.card := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let L := A.filter (fun v => G.degree v < G.secondSmallestDegree)
  have few : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro v hv u hu
    by_contra ne
    rcases degree_pair (G := G) v u ne with h | h
    · exact (not_lt_of_ge h) (mem_filter.mp hv).2
    · exact (not_lt_of_ge h) (mem_filter.mp hu).2
  have sub : A ⊆ X ∪ L := by
    intro v h
    by_cases vh : G.secondSmallestDegree ≤ G.degree v
    · exact mem_union_left _ (mem_filter.mpr ⟨h,vh⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨h,lt_of_not_ge vh⟩)
  have size := (card_le_card sub).trans (card_union_le X L)
  have room := closed_size sides ha
  change _ ≤ X.card + S.card
  omega

/-- From one high full A port and a common label on the high A population,
produce the exact private B contact and capacity needed for the new minimum cut. -/
theorem full_exit (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (ns : 2 ≤ S.card)
    (big : S.card*G.secondSmallestDegree < (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    {a : V} (ha : a ∈ A) (high : G.secondSmallestDegree ≤ G.degree a)
    (full : ∀ j ∈ S, G.Adj a j)
    {i : V} (hi : i ∈ S) (common : ∀ v ∈ A, G.secondSmallestDegree ≤ G.degree v → G.Adj v i) :
    ∃ j ∈ S, ∃ b ∈ B, G.secondSmallestDegree ≤ G.degree b ∧
      S.filter (G.Adj b) = {j} ∧
      G.secondSmallestDegree+1 ≤ S.card+(A ∩ G.neighborFinset j).card := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  have xa : a ∈ X := mem_filter.mpr ⟨ha,high⟩
  have lo := high_lower sides ha high
  change _ ≤ X.card + S.card at lo
  by_cases eq : X.card+S.card = G.secondSmallestDegree
  · exact tight_exit hc sides cap ns big ⟨a,xa⟩ eq
  have sub : X ⊆ A ∩ G.neighborFinset i := by
    intro v hv
    obtain ⟨va,vh⟩ := mem_filter.mp hv
    exact mem_inter.mpr ⟨va,(G.mem_neighborFinset i v).mpr (common v va vh).symm⟩
  obtain ⟨b,hb,bh,ib,sole⟩ := at_every_label hc sides cap big ha high full hi
  have supp : S.filter (G.Adj b) = {i} := by
    ext j
    constructor
    · intro h
      obtain ⟨js,edge⟩ := mem_filter.mp h
      exact mem_singleton.mpr (sole j js edge.symm)
    · intro h
      obtain rfl := mem_singleton.mp h
      exact mem_filter.mpr ⟨hi,ib.symm⟩
  exact ⟨i,hi,b,hb,bh,supp,by have c := card_le_card sub; omega⟩

#print axioms full_exit
#print axioms tight_exit
#print axioms at_every_label
#print axioms tight_full
end Graph189FullLabelExit
