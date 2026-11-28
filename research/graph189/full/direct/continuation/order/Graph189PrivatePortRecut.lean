import Graph189MinimumCutOrder
import Graph189MaximumDegree

namespace Graph189CutSides
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} {G : SimpleGraph V} {A B S : Finset V}

private theorem cut_disconnected (sides : CutSides G A B S) :
    ¬ (G.induce {u : V | u ∉ S}).Connected := by
  classical
  intro conn
  obtain ⟨x,hx⟩ := sides.left_nonempty
  obtain ⟨y,hy⟩ := sides.right_nonempty
  let rest : Set V := {v | v ∉ S}
  have xs : x ∈ rest := fun h => disjoint_left.mp sides.left_cut hx h
  have ys : y ∈ rest := fun h => disjoint_left.mp sides.right_cut hy h
  obtain ⟨p⟩ := conn (⟨x,xs⟩ : rest) (⟨y,ys⟩ : rest)
  obtain ⟨u,v,hu,hv,step,_⟩ := walk_exits (G := G.induce rest)
    (fun z : rest => z.val ∈ A) p hx (fun h => disjoint_left.mp sides.apart h hy)
  rcases sides.cover v.val with ha | hb | hs
  · exact hv ha
  · exact sides.no_cross u.val hu v.val hb step
  · exact v.property hs

private theorem two_steps {v x y : V} (vx : G.Adj v x) (xy : G.Adj x y)
    (ne : v ≠ y) (miss : ¬ G.Adj v y) : G.dist v y = 2 := by
  let walk : G.Walk v y := .cons vx (.cons xy .nil)
  have lower := walk.reachable.one_lt_dist_of_ne_of_not_adj ne miss
  have upper : G.dist v y ≤ 2 := G.dist_le walk
  omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

namespace CutSides

/-- A private port v defines a second minimum cut around its closed
neighborhood on its own side. Its only neighbor on the new cut is precisely
its old label i, and the whole opposite old side survives on the far side. -/
theorem private_port_recut (sides : CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    {k : ℕ} {v i : V} (hv : v ∈ B) (support : S.filter (G.Adj v) = {i})
    (quota : G.distEven v ≤ 1+k)
    (many : k+1 ≤ S.card+(A ∩ G.neighborFinset i).card) :
    ∃ W F T : Finset V, CutSides G W F T ∧ T.card = S.card ∧
      W = insert v (B ∩ G.neighborFinset v) ∧ W.card = G.degree v ∧ A ⊆ F ∧
      v ∈ W ∧ T.filter (G.Adj v) = {i} := by
  classical
  let N := G.neighborFinset v
  let D := univ.filter fun y => G.dist v y = 2
  let W := insert v (N.erase i)
  let T := insert i (D \ A)
  let F := univ \ (W ∪ T)
  have vi' : i ∈ S.filter (G.Adj v) := by rw [support]; simp
  obtain ⟨hi,vi⟩ := mem_filter.mp vi'
  have only {y : V} (ys : y ∈ S) (vy : G.Adj v y) : y = i := by
    have yi : y ∈ S.filter (G.Adj v) := mem_filter.mpr ⟨ys,vy⟩
    simpa only [support,mem_singleton] using yi
  have ib : i ∉ B := fun h => disjoint_left.mp sides.right_cut h hi
  have ia : i ∉ A := fun h => disjoint_left.mp sides.left_cut h hi
  have bneigh : N.erase i = B ∩ G.neighborFinset v := by
    ext y
    constructor
    · intro h
      obtain ⟨ne,hy⟩ := mem_erase.mp h
      have vy := (G.mem_neighborFinset _ _).mp hy
      refine mem_inter.mpr ⟨?_,hy⟩
      rcases sides.cover y with ha | hb | hs
      · exact (sides.no_cross y ha v hv vy.symm).elim
      · exact hb
      · exact (ne (only hs vy)).elim
    · intro h
      obtain ⟨yb,vy⟩ := mem_inter.mp h
      exact mem_erase.mpr ⟨fun e => ib (e ▸ yb),vy⟩
  have wsub : W ⊆ B := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hn
    · exact hv
    · exact (mem_inter.mp (bneigh ▸ hn)).1
  have vw : v ∈ W := mem_insert_self _ _
  have iw : i ∉ W := fun h => ib (wsub h)
  have iN : i ∈ N := (G.mem_neighborFinset _ _).mpr vi
  have vN : v ∉ N.erase i := fun h => G.loopless.irrefl v
    ((G.mem_neighborFinset _ _).mp (mem_erase.mp h).2)
  have wcard : W.card = G.degree v := by
    change (insert v (N.erase i)).card = _
    rw [card_insert_of_notMem vN,card_erase_add_one iN,G.card_neighborFinset_eq_degree]
  have dcap : D.card ≤ k := by
    have outside : v ∉ D := by simp [D]
    have sub : insert v D ⊆ univ.filter fun y => Even (G.dist v y) := by
      intro y hy
      rcases mem_insert.mp hy with rfl | h
      · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have count := card_le_card sub
    rw [card_insert_of_notMem outside] at count
    change _ ≤ G.distEven v at count
    omega
  have cross : A ∩ G.neighborFinset i ⊆ D ∩ A := by
    intro y hy
    obtain ⟨ya,iy⟩ := mem_inter.mp hy
    have ne : v ≠ y := fun e => disjoint_left.mp sides.apart ya (e ▸ hv)
    have miss : ¬ G.Adj v y := fun h => sides.no_cross y ya v hv h.symm
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
      two_steps vi ((G.mem_neighborFinset _ _).mp iy) ne miss⟩,ya⟩
  have tsmall : T.card ≤ S.card := by
    have h := card_sdiff_add_card_inter D A
    have sub := card_le_card cross
    have tot : T.card ≤ (D \ A).card+1 := card_insert_le _ _
    omega
  have wt : Disjoint W T := by
    refine disjoint_left.mpr ?_
    intro y wy ty
    rcases mem_insert.mp ty with rfl | dy
    · exact iw wy
    · have dist : G.dist v y = 2 := (mem_filter.mp (mem_sdiff.mp dy).1).2
      rcases mem_insert.mp wy with rfl | ny
      · simp at dist
      · have e := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp (mem_erase.mp ny).2)
        omega
  have af : A ⊆ F := by
    intro y ya
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro h
    rcases mem_union.mp h with wy | ty
    · exact disjoint_left.mp sides.apart ya (wsub wy)
    · rcases mem_insert.mp ty with rfl | dy
      · exact ia ya
      · exact (mem_sdiff.mp dy).2 ya
  have cut : CutSides G W F T := by
    refine ⟨⟨v,vw⟩,sides.left_nonempty.mono af,?_,wt,?_,?_,?_⟩
    · exact disjoint_left.mpr fun y wy fy => (mem_sdiff.mp fy).2 (mem_union_left _ wy)
    · exact disjoint_left.mpr fun y fy ty => (mem_sdiff.mp fy).2 (mem_union_right _ ty)
    · intro y
      by_cases h : y ∈ W ∪ T
      · exact (mem_union.mp h).imp_right Or.inr
      · exact Or.inr (Or.inl (mem_sdiff.mpr ⟨mem_univ _,h⟩))
    · intro x wx y fy xy
      have outside := (mem_sdiff.mp fy).2
      have nw : y ∉ W := fun h => outside (mem_union_left _ h)
      have nt : y ∉ T := fun h => outside (mem_union_right _ h)
      have yi : y ≠ i := fun e => nt (e ▸ mem_insert_self _ _)
      have vy : ¬ G.Adj v y := fun h =>
        nw (mem_insert_of_mem (mem_erase.mpr ⟨yi,(G.mem_neighborFinset _ _).mpr h⟩))
      rcases mem_insert.mp wx with rfl | nx
      · exact vy xy
      · have vx := (G.mem_neighborFinset _ _).mp (mem_erase.mp nx).2
        have ya : y ∉ A := fun h => sides.no_cross y h x
          (wsub (mem_insert_of_mem nx)) xy.symm
        exact nt (mem_insert_of_mem (mem_sdiff.mpr ⟨mem_filter.mpr
          ⟨mem_univ _,two_steps vx xy (fun e => nw (e ▸ vw)) vy⟩,ya⟩))
  have eq : T.card = S.card := by
    by_contra h
    exact cut_disconnected cut (smaller T (by omega))
  have new_support : T.filter (G.Adj v) = {i} := by
    ext y
    constructor
    · intro h
      obtain ⟨ty,vy⟩ := mem_filter.mp h
      rcases mem_insert.mp ty with e | dy
      · exact mem_singleton.mpr e
      · have d : G.dist v y = 2 := (mem_filter.mp (mem_sdiff.mp dy).1).2
        have d' := dist_eq_one_iff_adj.mpr vy
        omega
    · intro h
      obtain rfl := mem_singleton.mp h
      exact mem_filter.mpr ⟨mem_insert_self _ _,vi⟩
  exact ⟨W,F,T,cut,eq,congrArg (insert v) bneigh,wcard,af,vw,new_support⟩

/-- A cut whose left order is at most half of the order outside the cut,
after reserving one exceptional vertex, has the smaller high population. -/
theorem high_orientation [Nontrivial V] (sides : CutSides G A B S)
    (room : 2*A.card+S.card+1 ≤ Fintype.card V) :
    (A.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card ≤
      (B.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card := by
  classical
  let Y := B.filter fun y => G.secondSmallestDegree ≤ G.degree y
  let L := B.filter fun y => G.degree y < G.secondSmallestDegree
  have few : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    by_contra ne
    rcases degree_pair (G := G) a b ne with h | h
    · exact (not_lt_of_ge h) (mem_filter.mp ha).2
    · exact (not_lt_of_ge h) (mem_filter.mp hb).2
  have all : univ ⊆ (A ∪ S) ∪ (Y ∪ L) := by
    intro y _
    rcases sides.cover y with ha | hb | hs
    · exact mem_union_left _ (mem_union_left _ ha)
    · by_cases hh : G.secondSmallestDegree ≤ G.degree y
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hb,hh⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hb,lt_of_not_ge hh⟩))
    · exact mem_union_left _ (mem_union_right _ hs)
  have pop := card_le_card all
  rw [card_univ] at pop
  have := card_union_le A S
  have := card_union_le Y L
  have := card_union_le (A ∪ S) (Y ∪ L)
  have := card_filter_le A (fun y => G.secondSmallestDegree ≤ G.degree y)
  change _ ≤ Y.card
  omega

/-- A uniform two-contact condition on the smaller high side of every minimum
cut precludes a high private port at an old label with enough opposite contacts. -/
theorem no_high_private_at_large_label [Nontrivial V] (sides : CutSides G A B S)
    (hc : G.Connected) (cap : ∀ y, G.distEven y ≤ 1+G.secondSmallestDegree)
    (minimum : S.card = G.vertexConnectivity)
    (order : 6*G.secondSmallestDegree+S.card+1 ≤ Fintype.card V)
    (uniform : ∀ W F T : Finset V, CutSides G W F T → T.card = G.vertexConnectivity →
      (W.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card ≤
      (F.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card →
      ∀ y ∈ W, G.secondSmallestDegree ≤ G.degree y → 2 ≤ (T.filter (G.Adj y)).card)
    {v i : V} (hv : v ∈ B) (high : G.secondSmallestDegree ≤ G.degree v)
    (support : S.filter (G.Adj v) = {i})
    (many : G.secondSmallestDegree+1 ≤ S.card+(A ∩ G.neighborFinset i).card) : False := by
  classical
  have smaller (T : Finset V) (lt : T.card < S.card) :=
    connected_after_smaller_deletion (G := G) T (lt.trans_eq minimum)
  obtain ⟨W,F,T,cut,sz,_,wc,_,vw,new_support⟩ :=
    sides.private_port_recut smaller hv support (cap v) many
  have deg := (G.degree_le_maxDegree v).trans
    (Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc cap)
  have orient := cut.high_orientation (by omega)
  have two := uniform W F T cut (sz.trans minimum) orient v vw high
  simp [new_support] at two

#print axioms private_port_recut
#print axioms high_orientation
#print axioms no_high_private_at_large_label
end CutSides
end Graph189CutSides
