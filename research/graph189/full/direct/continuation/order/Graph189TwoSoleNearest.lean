import Graph189SoleNearestData
import Graph189DenseSideRoute
import Graph189HighMinimumGap

open SimpleGraph Finset Graph189SoleNearestSides Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TwoSoleNearest
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

theorem same_anchor (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {x i y j : V} (left : Witness G A S x i) (right : Witness G B S y j) : i=j := by
  obtain ⟨p,len⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨a,as_,mem⟩ := sides.meets left.side right.side p
  have split := congrArg SimpleGraph.Walk.length (Walk.take_spec p mem)
  rw [Walk.length_append] at split
  have l := G.dist_le (p.takeUntil a mem)
  have r := G.dist_le (p.dropUntil a mem)
  have no (v : V) (ns : v∉S) (np : ¬G.Adj a v) : 2≤G.dist a v := by
    have nz : G.dist a v≠0 := fun h => ns ((hc.dist_eq_zero_iff.mp h) ▸ as_)
    have ne : G.dist a v≠1 := fun h => np (dist_eq_one_iff_adj.mp h)
    omega
  have lx := no x (fun h => Finset.disjoint_left.mp sides.left_cut left.side h) (left.nonport a as_)
  have ry := no y (fun h => Finset.disjoint_left.mp sides.right_cut right.side h) (right.nonport a as_)
  have high := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
    (diameter_le_five hc (fun v => by simpa only [Nat.add_comm] using cap v))
  have not5 : G.dist x y≠5 := by
    intro eq
    rcases five_endpoints hc cap x y eq with h|h
    · exact (not_lt_of_ge left.high) h
    · exact (not_lt_of_ge right.high) h
  rw [G.dist_comm (u:=x) (v:=a)] at l
  exact (left.unique a as_ (by omega)).trans (right.unique a as_ (by omega)).symm

/-- Two side routes starting at the same anchor join into one original path. -/
theorem join_routes (sides : Graph189CutSides.CutSides G A B S) {i : V} (is_ : i∈S)
    {a b : ℕ} (la : Route G A i a) (rb : Route G B i b) :
    ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ Fintype.card V+1≤q.support.length+S.card+a+b := by
  obtain ⟨x,y,p,hp,ix,insideA,lc⟩ := la
  obtain ⟨x',y',r,hr,ix',insideB,rc⟩ := rb
  let tail := r.cons ix'
  have missing : i∉r.support := fun h => Finset.disjoint_left.mp sides.right_cut (insideB i h) is_
  have path := (Walk.cons_isPath_iff ix' r).mpr ⟨hr,missing⟩
  have ds : List.Disjoint p.reverse.support tail.support := by
    apply List.disjoint_left.mpr
    intro c hl ht
    have ca := insideA c (by simpa using hl)
    rcases List.mem_cons.mp (show c∈i::r.support from ht) with rfl|cr
    · exact Finset.disjoint_left.mp sides.left_cut ca is_
    · exact Finset.disjoint_left.mp sides.apart ca (insideB c cr)
  obtain ⟨q,hq,qs⟩ := Graph189TwoCutSingleton.joined p.reverse hp.reverse tail path ix.symm ds
  refine ⟨_,_,q,hq,?_⟩
  have cover : univ⊆(A∪B)∪S := by
    intro v _
    rcases sides.cover v with aa|bb|ss
    · exact mem_union_left _ (mem_union_left _ aa)
    · exact mem_union_left _ (mem_union_right _ bb)
    · exact mem_union_right _ ss
  have n := (card_le_card cover).trans (card_union_le _ _)
  rw [card_univ] at n
  have ab := card_union_le A B
  rw [qs,List.length_append]
  have pl : p.reverse.support.length=p.support.length := by simp
  have tl : tail.support.length=r.support.length+1 := rfl
  omega

theorem high_route (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (two : S.card=2)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1) (large : 5≤G.secondSmallestDegree)
    (high : ∀ v∈A, G.secondSmallestDegree≤G.degree v) {y i : V} (w : Witness G B S y i) :
    Route G A i 1 := by
  classical
  let k := G.secondSmallestDegree
  obtain ⟨contacts,misses⟩ := debit hc sides.swap sc cap w
  rw [filter_eq_self.mpr high] at misses
  change (A.filter (G.Adj i)).card+S.card≤k+1 at contacts
  change (A.filter (fun v => ¬G.Adj i v)).card+S.card≤k at misses
  change 5≤k at large
  have both := card_filter_add_card_filter_not (s:=A) (p:=G.Adj i)
  have min (x : A) : k-2≤(G.induce (A:Set V)).degree x := by
    have bd := retained (G:=G) A S (fun v va u e ua => by
      rcases sides.cover u with h|h|h
      · exact (ua h).elim
      · exact (sides.no_cross v va u h e).elim
      · exact h) x
    have h := high x.val x.property
    change k≤G.degree x.val at h
    omega
  obtain ⟨x,xa,xi⟩ := (sides.contacts_of_minimum (fun T lt => Graph189CutSides.connected_after_smaller_deletion
    T (lt.trans_le sc)) w.anchor).1
  let q : A := ⟨x,xa⟩
  have up := (G.induce (A:Set V)).degree_lt_card_verts q
  change _ < Fintype.card A at up
  rw [Fintype.card_coe] at up
  have m := min q
  exact from_region A i (d:=k-2) (t:=1) (b:=0) (by omega) min (by omega) (by omega)
    (Or.inl (by omega)) ⟨x,xa,xi.symm⟩ (by omega) (by omega)

/-- With every vertex on the two sides high, singly nearest nonports
force traceability even if one separator vertex is low. -/
theorem all_high (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (two : S.card=2)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1) (large : 5≤G.secondSmallestDegree)
    (aHigh : ∀ v∈A, G.secondSmallestDegree≤G.degree v)
    (bHigh : ∀ v∈B, G.secondSmallestDegree≤G.degree v)
    {x i y j : V} (left : Witness G A S x i) (right : Witness G B S y j) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra absent
  have eq := same_anchor hc sides cap left right
  subst j
  obtain ⟨a,b,p,hp,near⟩ := join_routes sides left.anchor
    (high_route hc sides sc two cap large aHigh right) (high_route hc sides.swap sc two cap large bHigh left)
  have min (v : V) : G.secondSmallestDegree<2*G.degree v := by
    rcases sides.cover v with h|h|h
    · have := aHigh v h; omega
    · have := bHigh v h; omega
    · have debit := sides.anchor_degree (fun T lt => Graph189CutSides.connected_after_smaller_deletion T (lt.trans_le sc))
        (fun v => by simpa only [Nat.add_comm] using cap v) h
      omega
  have gap := Graph189ExteriorDegreeCycle.high_min_all_paths_gap absent large cap min a b p hp
  omega

#print axioms high_route
#print axioms all_high
end Graph189TwoSoleNearest
