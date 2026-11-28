import Graph189PortDifference
import Graph189R1Metric

namespace Graph189CutClassification
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {A B S : Finset V}

/-- At an actual minimum cut, if the high opposite population exceeds its
combined even-distance quota, the anchor supports of the small-side high
vertices are either singletons outside their common core or co-singletons
within their union. The representative contacts may be of arbitrary degree. -/
theorem classify_actual (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {v : V | v ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (big : S.card*G.secondSmallestDegree <
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    (∀ i ∈ X, ((Graph189PortLabels.support G S i).filter
      (fun z => ∃ j ∈ X, ¬ G.Adj j z)).card ≤ 1) ∨
    (∀ i ∈ X, (S.filter (fun z => ¬ G.Adj i z ∧ ∃ j ∈ X, G.Adj j z)).card ≤ 1) := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  apply Graph189PortLabels.classify G X S
  intro i hi j hj
  have c' (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by simpa [Nat.add_comm] using cap v
  apply Graph189PortDifference.one_new_label (Y := Y) hc sides (filter_subset _ _)
    (mem_filter.mp hj).1 (mem_filter.mp hi).1 _ (fun a ha => (sides.contacts_of_minimum smaller ha).1)
    c' big
  intro v hv
  have d := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=j) (v:=v)).trans
    (diameter_le_five hc cap)
  have not5 : G.dist j v ≠ 5 := by
    intro eq
    rcases five_endpoints hc c' j v eq with h | h
    · exact (not_lt_of_ge (mem_filter.mp hj).2) h
    · exact (not_lt_of_ge (mem_filter.mp hv).2) h
  omega

#print axioms classify_actual
end Graph189CutClassification
