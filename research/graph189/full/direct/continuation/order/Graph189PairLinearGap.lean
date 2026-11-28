import Graph189SoleNearestData
import Graph189NearPathLinearOrder

open SimpleGraph Finset Graph189SoleNearestSides Graph189ExteriorDegreeCycle
namespace Graph189PairLinearGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The private predecessor and nonport inequalities put the two sole-nearest
sides directly in the linear-order gap range. -/
theorem order (hc : G.Connected) {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (sz : S.card=2)
    (point : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {x i y j : V} (left : Witness G A S x i) (right : Witness G B S y j) :
    Fintype.card V+3≤4*G.secondSmallestDegree := by
  classical
  let high (v : V) := G.secondSmallestDegree≤G.degree v
  have count {R : Finset V} {u : V} (ports : (R.filter (G.Adj u)).card+S.card≤G.secondSmallestDegree+1)
      (remote : ((R.filter high).filter (fun v => ¬G.Adj u v)).card+S.card≤G.secondSmallestDegree) :
      (R.filter high).card+2*S.card≤2*G.secondSmallestDegree+1 := by
    have sum := card_filter_add_card_filter_not (s:=R.filter high) (p:=G.Adj u)
    have h : ((R.filter high).filter (G.Adj u)).card≤(R.filter (G.Adj u)).card :=
      card_le_card (filter_subset_filter _ (filter_subset _ _))
    omega
  obtain ⟨pB,rB⟩ := debit hc sides sc point left
  obtain ⟨pA,rA⟩ := debit hc sides.swap sc point right
  have cA := count pA rA
  have cB := count pB rB
  have all := order_of_high_sides sides
  change Fintype.card V≤S.card+(A.filter high).card+(B.filter high).card+1 at all
  omega

#print axioms order
end Graph189PairLinearGap
