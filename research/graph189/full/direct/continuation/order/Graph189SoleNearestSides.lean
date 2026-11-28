import Graph189SoleNearestData
import Graph189RotationMinOrder

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SoleNearestSides
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

/-- Two such sides exclude nontraceability at all k≥7 and s≥3. The
exceptional low vertex can lie anywhere. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (three : 3≤S.card) (large : 7≤G.secondSmallestDegree)
    {x i y j : V} (left : Witness G A S x i) (right : Witness G B S y j) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_contra absent
  let k := G.secondSmallestDegree
  let high (v : V) := k≤G.degree v
  have point (v : V) : G.distEven v≤k+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have count {R : Finset V} {u : V} (ports : (R.filter (G.Adj u)).card+S.card≤k+1)
      (remote : ((R.filter high).filter (fun y => ¬G.Adj u y)).card+S.card≤k) :
      (R.filter high).card+2*S.card≤2*k+1 := by
    have sum := card_filter_add_card_filter_not (s:=R.filter high) (p:=G.Adj u)
    have h : ((R.filter high).filter (G.Adj u)).card≤(R.filter (G.Adj u)).card :=
      card_le_card (filter_subset_filter _ (filter_subset _ _))
    omega
  obtain ⟨pB,rB⟩ := debit hc sides sc point left
  obtain ⟨pA,rA⟩ := debit hc sides.swap sc point right
  have sizeA := count pA rA
  have sizeB := count pB rB
  have total := order_of_high_sides sides
  change Fintype.card V≤S.card+(A.filter high).card+(B.filter high).card+1 at total
  have lo := Graph189RotationLinked.base_order absent point (l:=3) (by decide)
    (three.trans sc) (by omega)
  change 4*(k-3+2)≤Fintype.card V+1 at lo
  change 7≤k at large
  omega

#print axioms traceable
end Graph189SoleNearestSides
