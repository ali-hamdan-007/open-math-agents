import Graph189MinimumCutOrder
import Graph189TrimmedRows

namespace Graph189MixedDebit
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private noncomputable def positiveEven (G : SimpleGraph V) (i : V) : Finset V := by
  classical
  exact (univ.filter fun y => Even (G.dist i y)).erase i

omit [DecidableRel G.Adj] in
private theorem quota {i : V} {k : ℕ} (cap : G.distEven i ≤ k+1) :
    (positiveEven G i).card ≤ k := by
  classical
  let E := univ.filter fun y => Even (G.dist i y)
  have mem : i ∈ E := by simp [E]
  change (E.erase i).card ≤ k
  have h := card_erase_add_one mem
  change E.card ≤ k+1 at cap
  omega

omit [DecidableRel G.Adj] in
private theorem two_mem {i v : V} (d : G.dist i v = 2) : v ∈ positiveEven G i := by
  classical
  have ne : v ≠ i := by rintro rfl; simp at d
  exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,by simp [d]⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem two {i p y : V} (ip : G.Adj i p) (py : G.Adj p y) (ne : i ≠ y)
    (miss : ¬G.Adj i y) : G.dist i y = 2 := by
  let walk : G.Walk i y := .cons ip (.cons py .nil)
  have hl := walk.reachable.one_lt_dist_of_ne_of_not_adj ne miss
  have hu : G.dist i y ≤ 2 := G.dist_le walk
  omega

private def block (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (c : V) :=
  insert c (T ∩ G.neighborFinset c)

private theorem block_subset {T : Finset V} {c : V} (hc : c ∈ T) : block G T c ⊆ T := by
  intro y hy
  exact (mem_insert.mp hy).elim (fun e => e ▸ hc) (fun h => (mem_inter.mp h).1)

private theorem block_near {T : Finset V} {i c : V} (h : G.Adj i c) (out : i ∉ T) :
    block G T c ⊆ G.neighborFinset i ∪ positiveEven G i := by
  classical
  intro y hy
  rcases mem_insert.mp hy with rfl | hy
  · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr h)
  obtain ⟨yt,ey⟩ := mem_inter.mp hy
  by_cases iy : G.Adj i y
  · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr iy)
  · exact mem_union_right _ (two_mem (two h ((G.mem_neighborFinset _ _).mp ey)
      (fun e => out (e ▸ yt)) iy))

private theorem block_degree {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S)
    {a : V} (ha : a ∈ A) : G.degree a+1 ≤ (block G A a).card + S.card := by
  classical
  have sub : G.neighborFinset a ⊆ (A ∩ G.neighborFinset a) ∪ S := by
    intro v hv
    rcases sides.cover v with h | h | h
    · exact mem_union_left _ (mem_inter.mpr ⟨h,hv⟩)
    · exact (sides.no_cross a ha v h ((G.mem_neighborFinset _ _).mp hv)).elim
    · exact mem_union_right _ h
  have old := (card_le_card sub).trans (card_union_le (A ∩ G.neighborFinset a) S)
  rw [G.card_neighborFinset_eq_degree] at old
  have non : a ∉ A ∩ G.neighborFinset a :=
    fun h => G.loopless.irrefl a ((G.mem_neighborFinset _ _).mp (mem_inter.mp h).2)
  unfold block
  rw [card_insert_of_notMem non]
  omega

/-- The mixed incidence bound at any crossed high pair with a common cut
neighbor. All vertices counted in the opposite side are high. -/
theorem mixed_cut_pair [Nontrivial V] {A B S : Finset V}
    (sides : Graph189CutSides.CutSides G A B S) (hc : G.Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree) {a b z : V}
    (ha : a ∈ A) (hb : b ∈ B) (az : G.Adj a z) (bz : G.Adj b z)
    (ah : G.secondSmallestDegree ≤ G.degree a)
    (highB : ∀ y ∈ B, G.secondSmallestDegree ≤ G.degree y) :
    B.card + ((G.neighborFinset a ∩ G.neighborFinset b).card-1)*
        (G.secondSmallestDegree+1-S.card) ≤
      (S.card+1)*G.secondSmallestDegree + (G.neighborFinset a ∩ G.neighborFinset b).card *
        (G.maxDegree-G.secondSmallestDegree+S.card-1) := by
  classical
  let k := G.secondSmallestDegree
  let e := G.maxDegree-k
  let R := G.neighborFinset a ∩ G.neighborFinset b
  let W := block G B b
  let C := block G A a
  let E (i : V) := B.filter fun y => G.dist i y = if G.Adj a i then 2 else 1
  have cap' (v : V) : G.distEven v ≤ k+1 := by simpa only [k,Nat.add_comm 1] using cap v
  have rout : R ⊆ S := by
    intro i hi
    obtain ⟨ai,bi⟩ := mem_inter.mp hi
    rcases sides.cover i with h | h | h
    · exact (sides.no_cross i h b hb ((G.mem_neighborFinset _ _).mp bi).symm).elim
    · exact (sides.no_cross a ha i h ((G.mem_neighborFinset _ _).mp ai)).elim
    · exact h
  have active : R.Nonempty := ⟨z,mem_inter.mpr
    ⟨(G.mem_neighborFinset _ _).mpr az,(G.mem_neighborFinset _ _).mpr bz⟩⟩
  have bcover : B ⊆ positiveEven G a ∪ S.biUnion E := by
    intro y hy
    have ne : a ≠ y := fun eq => Finset.disjoint_left.mp sides.apart (eq ▸ ha) hy
    by_cases even : Even (G.dist a y)
    · exact mem_union_left _ (mem_erase.mpr ⟨ne.symm,mem_filter.mpr ⟨mem_univ _,even⟩⟩)
    have diam := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := a) (v := y)).trans
      (diameter_le_five hc cap)
    have nofive : G.dist a y ≠ 5 := by
      intro d
      rcases five_endpoints hc cap' a y d with h | h
      · exact (not_lt_of_ge ah) h
      · exact (not_lt_of_ge (highB y hy)) h
    have noone : G.dist a y ≠ 1 := fun h => sides.no_cross a ha y hy (dist_eq_one_iff_adj.mp h)
    have d3 : G.dist a y = 3 := by rw [Nat.even_iff] at even; omega
    obtain ⟨p,hp⟩ := (hc a y).exists_walk_length_eq_dist
    obtain ⟨i,hi,hmem⟩ := sides.meets ha hy p
    have dlen := congrArg SimpleGraph.Walk.length (Walk.take_spec p hmem)
    rw [Walk.length_append] at dlen
    have d₁ := G.dist_le (p.takeUntil i hmem)
    have d₂ := G.dist_le (p.dropUntil i hmem)
    have d₃ := hc.dist_triangle (u := a) (v := i) (w := y)
    have ai0 : G.dist a i ≠ 0 := by
      intro hh
      exact Finset.disjoint_left.mp sides.left_cut ((hc.dist_eq_zero_iff.mp hh) ▸ ha) hi
    have iy0 : G.dist i y ≠ 0 := by
      intro hh
      exact Finset.disjoint_left.mp sides.right_cut hy ((hc.dist_eq_zero_iff.mp hh) ▸ hi)
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨i,hi,mem_filter.mpr ⟨hy,?_⟩⟩
    by_cases h : G.Adj a i
    · rw [if_pos h]
      have ai := dist_eq_one_iff_adj.mpr h
      omega
    · rw [if_neg h]
      have no : G.dist a i ≠ 1 := fun hh => h (dist_eq_one_iff_adj.mp hh)
      omega
  have row (i : V) (hi : i ∈ S) : (E i).card ≤ k := by
    by_cases ai : G.Adj a i
    · apply (card_le_card (t := positiveEven G i) ?_).trans (quota (cap' i))
      intro y hy
      have d := (mem_filter.mp hy).2
      rw [if_pos ai] at d
      exact two_mem d
    · obtain ⟨u,hu,ui⟩ := (sides.contacts_of_minimum smaller hi).1
      apply (card_le_card (t := positiveEven G u) ?_).trans (quota (cap' u))
      intro y hy
      obtain ⟨hyB,d⟩ := mem_filter.mp hy
      rw [if_neg ai] at d
      exact two_mem (two ui (dist_eq_one_iff_adj.mp d)
        (fun eq => Finset.disjoint_left.mp sides.apart (eq ▸ hu) hyB)
        (sides.no_cross u hu y hyB))
  have cwsize := block_degree sides ha
  change G.degree a+1 ≤ C.card+S.card at cwsize
  have Kdeg : k ≤ G.maxDegree := ah.trans (G.degree_le_maxDegree a)
  have sign : 0 < S.card := card_pos.mpr (active.mono rout)
  have marked (i : V) (hi : i ∈ R) : (E i ∪ W).card ≤ k+(e+S.card-1) := by
    obtain ⟨ai',bi'⟩ := mem_inter.mp hi
    have ai := (G.mem_neighborFinset _ _).mp ai'
    have bi := (G.mem_neighborFinset _ _).mp bi'
    have hiS := rout hi
    have wnear := block_near (G := G) bi.symm (T := B)
      (fun hy => Finset.disjoint_left.mp sides.right_cut hy hiS)
    have cnear := block_near (G := G) ai.symm (T := A)
      (fun hy => Finset.disjoint_left.mp sides.left_cut hy hiS)
    have ewB : E i ∪ W ⊆ B := by
      intro v hv
      exact (mem_union.mp hv).elim (fun h => (mem_filter.mp h).1) (fun h => block_subset (G := G) hb h)
    have dis : Disjoint (E i ∪ W) C := sides.apart.symm.mono ewB (block_subset ha)
    have all : (E i ∪ W) ∪ C ⊆ G.neighborFinset i ∪ positiveEven G i := by
      intro v hv
      rcases mem_union.mp hv with h | h
      · rcases mem_union.mp h with h | h
        · have d := (mem_filter.mp h).2
          rw [if_pos ai] at d
          exact mem_union_right _ (two_mem d)
        · exact wnear h
      · exact cnear h
    have upper := (card_le_card all).trans (card_union_le (G.neighborFinset i) (positiveEven G i))
    rw [card_union_of_disjoint dis,G.card_neighborFinset_eq_degree] at upper
    have deg := G.degree_le_maxDegree i
    have ev := quota (cap' i)
    change (E i ∪ W).card ≤ k+(G.maxDegree-k+S.card-1)
    omega
  have trim := trim_common_rows B (positiveEven G a) W S R E k (e+S.card-1)
    rout active bcover (quota (cap' a)) (fun i hi _ => row i hi) marked
  have wb := block_degree sides.swap hb
  change G.degree b+1 ≤ W.card+S.card at wb
  have bh := highB b hb
  change k ≤ G.degree b at bh
  have product := Nat.mul_le_mul_left (R.card-1) (show k+1-S.card ≤ W.card by omega)
  change B.card+(R.card-1)*(k+1-S.card) ≤ (S.card+1)*k+R.card*(e+S.card-1)
  omega

#print axioms mixed_cut_pair
end Graph189MixedDebit
