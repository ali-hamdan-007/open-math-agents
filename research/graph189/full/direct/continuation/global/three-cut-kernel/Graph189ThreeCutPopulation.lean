import Graph189CommonTerminal
import Graph189GraphPopulation

open SimpleGraph Finset
namespace Graph189ThreeCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- At the high-order threshold the smaller high population differs from k by at most three. -/
theorem numerical {x y k : ℤ} (degree : 26 ≤ k) (nonnegative : 0 ≤ x) (orientation : x ≤ y)
    (total : 5*k-6 ≤ x+y) (product : x*y ≤ k*x+3*k*k) : x ≤ k+3 ∧ 4*k-9 ≤ y := by
  have yy := mul_nonneg nonnegative (sub_nonneg.mpr orientation)
  have upper : 2*x ≤ 5*k := by
    by_contra! high
    have h := mul_nonneg (show 0 ≤ 2*x-5*k by omega) (show 0 ≤ 2*x+3*k by omega)
    nlinarith only [product,yy,h,sq_nonneg (k-1),degree]
  have small : x ≤ k+3 := by
    by_contra! high
    have h := mul_nonneg (show 0 ≤ x-k-4 by omega) (show 0 ≤ 3*k-10-x by omega)
    have p := mul_nonneg nonnegative (show 0 ≤ x+y-5*k+6 by omega)
    nlinarith only [h,p,product,degree]
  exact ⟨small,by omega⟩

/-- The bound applies to either orientation of every genuine minimum three-cut. -/
theorem populations (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (degree : 26 ≤ G.secondSmallestDegree) (order : 5*G.secondSmallestDegree ≤ Fintype.card V+2)
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card) :
    (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤ G.secondSmallestDegree+3 ∧
      4*G.secondSmallestDegree ≤ (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card+9 := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  have smaller (T : Finset V) (lt : T.card<S.card) := Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have natProd := cut.high_product hc smaller cap
  change X.card*Y.card ≤ X.card*k+S.card*(k*k) at natProd
  rw [three] at natProd
  have prod : (X.card:ℤ)*Y.card ≤ (k:ℤ)*X.card+3*k*k := by
    exact_mod_cast (show X.card*Y.card ≤ k*X.card+3*k*k by simpa only [Nat.mul_comm X.card k,Nat.mul_assoc] using natProd)
  have total := Graph189MinimumQuotas.high_population_lower cut
  change (Fintype.card V:ℤ)-S.card-1 ≤ (X.card:ℤ)+Y.card at total
  rw [three] at total
  change 5*k≤Fintype.card V+2 at order
  have bound : (5:ℤ)*k≤(Fintype.card V:ℤ)+2 := by exact_mod_cast order
  have kk : (26:ℤ)≤k := by exact_mod_cast degree
  obtain ⟨small,big⟩ := numerical kk (Int.natCast_nonneg X.card) (show (X.card:ℤ)≤Y.card by exact_mod_cast orient) (by omega) prod
  constructor
  · exact_mod_cast small
  · exact_mod_cast (show (4:ℤ)*k≤(Y.card:ℤ)+9 by omega)

#print axioms populations
end Graph189ThreeCut
