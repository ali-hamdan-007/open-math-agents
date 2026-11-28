import Graph189TwofoldCover
import Graph189BoundaryDebit
import Graph189MinimumCutOrder

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SoleNearestSides
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

/-- An actual high nonport with exactly one separator vertex at distance two. -/
structure Witness (G : SimpleGraph V) [DecidableRel G.Adj] (A S : Finset V) (x i : V) : Prop where
  side : x∈A
  anchor : i∈S
  high : G.secondSmallestDegree≤G.degree x
  nonport : ∀ j∈S, ¬G.Adj j x
  two : G.dist i x=2
  unique : ∀ j∈S, G.dist j x=2 → i=j

/-- The private predecessor charges every opposite contact; the nonport
charges every high opposite noncontact to its own remaining even budget. -/
theorem debit (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {x i : V} (w : Witness G A S x i) :
    (B.filter (G.Adj i)).card+S.card≤G.secondSmallestDegree+1 ∧
    ((B.filter (fun y => G.secondSmallestDegree≤G.degree y)).filter (fun y => ¬G.Adj i y)).card+S.card≤G.secondSmallestDegree := by
  classical
  let k := G.secondSmallestDegree
  let N := B.filter (G.Adj i)
  let Y := B.filter (fun y => G.secondSmallestDegree≤G.degree y)
  let R := Y.filter (fun y => ¬G.Adj i y)
  have smaller (T : Finset V) (h : T.card<S.card) := Graph189CutSides.connected_after_smaller_deletion
    (G:=G) T (h.trans_le sc)
  obtain ⟨v,va,pv⟩ := Graph189TwofoldCover.private_predecessor hc sides.swap w.side w.anchor
    w.two w.nonport w.unique
  have vp : i∈S.filter (G.Adj v) := by rw [pv]; exact mem_singleton_self i
  have vi : G.Adj v i := (mem_filter.mp vp).2
  have nsub : N⊆B := filter_subset _ _
  have nEven : N.filter (fun y => Even (G.dist v y))=N := filter_eq_self.mpr (by
    intro y hy
    obtain ⟨yb,iy⟩ := mem_filter.mp hy
    rw [Graph189PortDifference.cross_two hc sides va yb vi iy]
    decide)
  have left := Graph189BoundaryDebit.even_quota hc sides smaller cap nsub va
  rw [nEven,show Graph189PortLabels.support G S v={i} from pv,card_singleton] at left
  have empty : Graph189PortLabels.support G S x=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨js,e⟩ := mem_filter.mp hj
    exact w.nonport j js e.symm
  have rsub : R⊆B := (filter_subset _ _).trans (filter_subset _ _)
  have rEven : R.filter (fun y => Even (G.dist x y))=R := filter_eq_self.mpr (by
    intro y hy
    obtain ⟨ys,no⟩ := mem_filter.mp hy
    obtain ⟨yb,high⟩ := mem_filter.mp ys
    have near : G.dist y x≤4 := by
      have bound := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=y) (v:=x)).trans
        (diameter_le_five hc (fun v => by simpa only [Nat.add_comm] using cap v))
      have not5 : G.dist y x≠5 := by
        intro d
        rcases five_endpoints hc cap y x d with bad|bad
        · exact (not_lt_of_ge high) bad
        · exact (not_lt_of_ge w.high) bad
      omega
    rw [G.dist_comm (u:=x) (v:=y)]
    by_contra odd
    obtain ⟨j,js,e,d⟩ := Graph189TwofoldCover.odd_noncontact hc sides.swap yb w.side near odd w.nonport
    exact no (by simpa only [w.unique j js d] using e.symm))
  have right := Graph189BoundaryDebit.even_quota hc sides smaller cap rsub w.side
  rw [rEven,empty,card_empty,Nat.add_zero] at right
  exact ⟨left,right⟩

/-- The two high side populations, the separator and at most one other
vertex exhaust the original order. -/
theorem order_of_high_sides (sides : Graph189CutSides.CutSides G A B S) :
    Fintype.card V ≤ S.card+(A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card+
      (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card+1 := by
  classical
  let high (v : V) := G.secondSmallestDegree≤G.degree v
  let L := univ.filter (fun v => ¬high v)
  have few : L.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra neq
    rcases degree_pair (G:=G) u v neq with h|h
    · exact (mem_filter.mp hu).2 h
    · exact (mem_filter.mp hv).2 h
  have covered : univ ⊆ ((S∪A.filter high)∪B.filter high)∪L := by
    intro v _
    by_cases h : high v
    · rcases sides.cover v with a|b|s
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨a,h⟩)))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨b,h⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ s))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩)
  have cnt := (card_le_card covered).trans (card_union_le _ _)
  rw [card_univ] at cnt
  have p := card_union_le S (A.filter high)
  have q := card_union_le (S∪A.filter high) (B.filter high)
  change Fintype.card V ≤ S.card+(A.filter high).card+(B.filter high).card+1
  omega

#print axioms debit
end Graph189SoleNearestSides
