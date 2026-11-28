import Graph189StrictPopulation
import Graph189ThreeCutBalancedTable

open SimpleGraph Finset
namespace Graph189ThreeCutBalancedFacts
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

theorem quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (window : Graph189ThreeCutBalancedTable.Certified G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun a => G.secondSmallestDegree≤G.degree a)).card≤
      (B.filter (fun b => G.secondSmallestDegree≤G.degree b)).card) :
    let k := G.secondSmallestDegree
    let x := (A.filter (fun a => k≤G.degree a)).card
    let y := (B.filter (fun b => k≤G.degree b)).card
    4*k+4<Fintype.card V ∧ 3*k<y ∧ x+1<2*k ∧ 12*k<2*x+3*y+12 ∧
      (x≤k-2 → 6*k+x<2*y) := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun a => k≤G.degree a)
  let Y := B.filter (fun b => k≤G.degree b)
  have xs : X⊆A := filter_subset _ _
  have ys : Y⊆B := filter_subset _ _
  have smaller (T : Finset V) (lt : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have cross := Graph189CrossBoundaryProduct.high_product cut hc smaller cap
  change X.card*Y.card+X.card*S.card≤X.card*k+S.card*(k*k)+S.card*k at cross
  rw [three] at cross
  have base : X.card*(Y.card+3)≤k*X.card+3*k*(k+1) := by nlinarith only [cross]
  have strong (large : 2*k+1<X.card) : X.card*(Y.card+3)≤k*X.card+3*(k-2)*(k+1) := by
    have order' : X.card≤Y.card := orient
    have saved := Graph189StrictPopulation.balanced hc cut smaller cap (by omega) xs ys
      (fun a ha => (mem_filter.mp ha).2) (fun b hb => (mem_filter.mp hb).2) large (large.trans_le order')
    change X.card*Y.card+X.card*S.card≤X.card*k+S.card*(k-2)+S.card*(k*(k-2)) at saved
    rw [three] at saved
    nlinarith only [saved]
  have pop := Graph189MinimumQuotas.high_population_lower cut
  change (Fintype.card V:ℤ)-S.card-1≤(X.card:ℤ)+Y.card at pop
  rw [three] at pop
  exact Graph189ThreeCutBalancedTable.quotas (x:=X.card) (y:=Y.card) window orient (by omega) base strong

#print axioms quotas
end Graph189ThreeCutBalancedFacts
