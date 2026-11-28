import Graph189SoleNearestSides

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189OnePortCover
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- A single side vertex has all nearest labels of the high nonport as
neighbors. This includes a universal port or a private predecessor of
a nonport with a sole nearest anchor. -/
structure Cover (G : SimpleGraph V) [DecidableRel G.Adj] (A S : Finset V) (x p : V) : Prop where
  root : x∈A
  high : G.secondSmallestDegree≤G.degree x
  nonport : ∀j∈S, ¬G.Adj j x
  port : p∈A
  labels : ∀j∈S, G.dist j x=2 → G.Adj p j

theorem population (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {x p : V} (c : Cover G A S x p) :
    (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card+2*S.card≤
      2*G.secondSmallestDegree+(Graph189PortLabels.support G S p).card := by
  classical
  let Y := B.filter (fun v => G.secondSmallestDegree≤G.degree v)
  let E (u : V) := Y.filter (fun v => Even (G.dist u v))
  have inc : Y⊆E x∪E p := by
    intro v hv
    obtain ⟨vb,high⟩ := mem_filter.mp hv
    by_cases he : Even (G.dist x v)
    · exact mem_union_left _ (mem_filter.mpr ⟨hv,he⟩)
    have near : G.dist v x≤4 := by
      have bound := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=v) (v:=x)).trans
        (diameter_le_five hc (fun v => by simpa only [Nat.add_comm] using cap v))
      have ne : G.dist v x≠5 := by
        intro eq
        rcases five_endpoints hc cap v x eq with lt|lt
        · exact (not_lt_of_ge high) lt
        · exact (not_lt_of_ge c.high) lt
      omega
    rw [G.dist_comm (u:=x) (v:=v)] at he
    obtain ⟨j,js,vj,dist⟩ := Graph189TwofoldCover.odd_noncontact hc sides.swap vb c.root near he c.nonport
    have exactTwo := Graph189PortDifference.cross_two hc sides c.port vb (c.labels j js dist) vj.symm
    exact mem_union_right _ (mem_filter.mpr ⟨hv,by rw [exactTwo]; decide⟩)
  have smaller (T : Finset V) (h : T.card<S.card) := Graph189CutSides.connected_after_smaller_deletion
    (G:=G) T (h.trans_le sc)
  have quota {u : V} (ua : u∈A) : (E u).card+S.card≤G.secondSmallestDegree+(Graph189PortLabels.support G S u).card :=
    Graph189BoundaryDebit.even_quota hc sides smaller cap (filter_subset _ _) ua
  have empty : Graph189PortLabels.support G S x=∅ := eq_empty_iff_forall_notMem.mpr (by
    intro j hj
    obtain ⟨js,edge⟩ := mem_filter.mp hj
    exact c.nonport j js edge.symm)
  have lx := quota c.root
  rw [empty,card_empty,Nat.add_zero] at lx
  have lp := quota c.port
  have count := (card_le_card inc).trans (card_union_le _ _)
  change Y.card+2*S.card≤_
  omega

/-- At a cut of size at least four two one-port covers contradict the
true fourth-index order bound, even with the unique low vertex anywhere. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (four : 4≤S.card) (large : 11≤G.secondSmallestDegree) {x p y q : V}
    (left : Cover G A S x p) (right : Cover G B S y q) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  by_contra bad
  let k := G.secondSmallestDegree
  let high (v : V) := k≤G.degree v
  have point (v : V) : G.distEven v≤k+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have sizeA := population hc sides.swap sc point right
  have sizeB := population hc sides sc point left
  have hp : (Graph189PortLabels.support G S p).card≤S.card := card_le_card (filter_subset _ _)
  have hq : (Graph189PortLabels.support G S q).card≤S.card := card_le_card (filter_subset _ _)
  let X := A.filter high
  let Y := B.filter high
  have n := Graph189SoleNearestSides.order_of_high_sides sides
  change Fintype.card V≤S.card+X.card+Y.card+1 at n
  change X.card+2*S.card≤2*k+_ at sizeA
  change Y.card+2*S.card≤2*k+_ at sizeB
  have lo := Graph189RotationLinked.base_order bad point (l:=4) (by decide) (four.trans sc) (by omega)
  change 5*(k-4+2)≤Fintype.card V+1 at lo
  change 11≤k at large
  omega

#print axioms population
#print axioms traceable
end Graph189OnePortCover
