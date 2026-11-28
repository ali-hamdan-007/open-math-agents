import Graph189ThreeNearGraph

namespace Graph189ThreeCutSaturation24
open Graph189ThreeCutSaturationTable

def GoodStrict (k x y : ℕ) : Prop :=
  3*k<y ∧ (9*k+x<3*y+15 ∨ (x+1<2*k ∧ 12*k<2*x+3*y+12)) ∧
    (x≤k-2 → 6*k+x<2*y+2)

instance (k x y : ℕ) : Decidable (GoodStrict k x y) := by
  unfold GoodStrict
  infer_instance

private def first (x : ℕ) := max x (105-x)
private def row (x : ℕ) : Bool :=
  (List.range (73+x/2-first x)).all fun j =>
    let y := first x+j
    decide ((24<x → Charge 24 x y) → GoodStrict 24 x y ∨ (x=33 ∧ y=72))

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem checked : (List.range 73).all row=true := by decide

private theorem arithmetic {x y : ℕ} (order : 105≤x+y) (orient : x≤y)
    (base : x*(y+3)≤24*x+3*24*(24+1)) (charge : 24<x → Charge 24 x y) :
    GoodStrict 24 x y ∨ (x=33 ∧ y=72) := by
  have bound : x≤72 := by
    by_contra! h
    have m := Nat.mul_le_mul_left x (show 73≤y by omega)
    nlinarith only [base,m,h]
  by_cases large : 72+x/2<y
  · left
    unfold GoodStrict
    omega
  have hx := List.all_eq_true.mp checked x (List.mem_range.mpr (by omega))
  have lower : first x≤y := max_le orient (by omega)
  have iy : y-first x<73+x/2-first x := by omega
  have hy := List.all_eq_true.mp hx (y-first x) (List.mem_range.mpr iy)
  have e : first x+(y-first x)=y := by omega
  simp only [e,decide_eq_true_eq] at hy
  exact hy charge

open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

theorem quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v,G.distEven v≤1+G.secondSmallestDegree)
    (lo : 24≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤36)
    (order : 5*G.secondSmallestDegree≤Fintype.card V+11)
    (orient : (A.filter (fun a => G.secondSmallestDegree≤G.degree a)).card≤
      (B.filter (fun b => G.secondSmallestDegree≤G.degree b)).card) :
    let k := G.secondSmallestDegree
    let x := (A.filter (fun a => k≤G.degree a)).card
    let y := (B.filter (fun b => k≤G.degree b)).card
    GoodStrict k x y := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun a => k≤G.degree a)
  let Y := B.filter (fun a => k≤G.degree a)
  by_cases pre : 25≤G.secondSmallestDegree
  · obtain ⟨big,privateBound,residual⟩ := Graph189ThreeCutSaturationFacts.quotas hc cut minimum
      three cap pre hi order orient
    exact ⟨big,privateBound,fun small => by have h := residual small; omega⟩
  have k24 : k=24 := by change 24≤k at lo; change ¬25≤k at pre; omega
  have data := Graph189ThreeCutSaturationFacts.population_data hc cut minimum three cap orient
  change Fintype.card V≤X.card+Y.card+4 ∧ X.card*(Y.card+3)≤k*X.card+3*k*(k+1) ∧
    (k<X.card → Charge k X.card Y.card) at data
  rw [k24] at data
  change 5*k≤Fintype.card V+11 at order
  obtain ⟨sum,base,charge⟩ := data
  change GoodStrict k X.card Y.card
  rw [k24]
  rcases arithmetic (by omega) (show X.card≤Y.card from orient) base charge with yes|⟨x,y⟩
  · exact yes
  · have smaller (T : Finset V) (lt : T.card<S.card) :=
      Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
    exact False.elim (Graph189ThreeNearGraph.excludes_population hc cut smaller three cap
      (X:=X) (Y:=Y) (filter_subset _ _) (filter_subset _ _) (fun a ha => (mem_filter.mp ha).2)
      (fun b hb => (mem_filter.mp hb).2) k24 x y)

#print axioms arithmetic
#print axioms quotas
end Graph189ThreeCutSaturation24
