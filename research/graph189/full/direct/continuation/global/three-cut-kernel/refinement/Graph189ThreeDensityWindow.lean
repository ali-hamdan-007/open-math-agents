import Graph189ThreeCutThresholds
import Graph189ThreePrivateDensity

open Finset SimpleGraph
namespace Graph189ThreeDensityWindow

/-- The population of the smaller high side and the least possible opposite
population after the lifted deletion bound. The second disjunct permits the
stronger count on a dense side whose contacts are all private. -/
private def row (k x : ℕ) : Bool :=
  let y := max x (5*k-15-x)
  decide (k*x+3*(k*k)+3*k < x*y+3*x ∨
    (3*k<y ∧
      (9*k+x<3*y+15 ∨ (x+2≤2*k ∧ 12*k<2*x+3*y+12)) ∧
      (x≤k → 6*k+x<2*y)))

private theorem table : [33,34,35,36].all (fun k =>
    (List.range (3*k+1)).all (row k))=true := by decide

private theorem numerical {k x y : ℕ} (lo : 33≤k) (hi : k≤36)
    (orient : x≤y) (sum : 5*k≤x+y+15)
    (product : x*y+3*x≤k*x+3*(k*k)+3*k) :
    3*k<y ∧ (9*k+x<3*y+15 ∨ (x+2≤2*k ∧ 12*k<2*x+3*y+12)) ∧
    (x≤k → 6*k+x<2*y) := by
  have small : x<3*k+1 := by
    by_contra! large
    have ybig : 3*k≤y := by omega
    have l := Nat.mul_le_mul_left x ybig
    have r := Nat.mul_le_mul_left k large
    nlinarith [l,r,Nat.mul_le_mul_left k (show 1≤k by omega)]
  have entry : k∈[33,34,35,36] := by
    interval_cases k <;> decide
  have valid := List.all_eq_true.mp (List.all_eq_true.mp table k entry) x (List.mem_range.mpr small)
  change decide (_ ∨ _) = true at valid
  have weak : max x (5*k-15-x)≤y := max_le orient (by omega)
  have prod := Nat.mul_le_mul_left x weak
  rcases of_decide_eq_true valid with no | ⟨many,wide,last⟩
  · omega
  · refine ⟨by omega,?_,fun xk => by have := last xk; omega⟩
    rcases wide with a | ⟨b,c⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨b,by omega⟩

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

theorem quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (sm : S.card=G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (lo : 33≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤36)
    (floor : 5*G.secondSmallestDegree≤Fintype.card V+11)
    (orient : (A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card) :
    let k : ℤ := G.secondSmallestDegree
    let x : ℤ := (A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card
    let y : ℤ := (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card
    3*k<y ∧ (9*k-15+x<3*y ∨ ((A.card:ℤ)<2*k ∧ 12*k<2*x+3*y+12)) ∧
      (x≤k → 6*k+x<2*y) := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k≤G.degree v)
  let Y := B.filter (fun v => k≤G.degree v)
  have prod := Graph189CrossBoundaryProduct.high_product cut hc
    (fun T lt => Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq sm)) cap
  change X.card*Y.card+X.card*S.card≤X.card*k+S.card*(k*k)+S.card*k at prod
  rw [three] at prod
  have total := Graph189MinimumQuotas.high_population_lower cut
  change (Fintype.card V:ℤ)-S.card-1≤(X.card:ℤ)+Y.card at total
  rw [three] at total
  have one : (A\X).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x y ne with h|h
    · exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,h⟩)
    · exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨(mem_sdiff.mp hy).1,h⟩)
  have all := card_sdiff_add_card_eq_card (show X⊆A from filter_subset _ _)
  change 5*k≤Fintype.card V+11 at floor
  have data := numerical (k:=k) (x:=X.card) (y:=Y.card) lo hi orient (by omega)
    (by simpa only [Nat.mul_comm] using prod)
  change 3*(k:ℤ)<Y.card ∧ (9*(k:ℤ)-15+X.card<3*(Y.card:ℤ) ∨
    ((A.card:ℤ)<2*k ∧ 12*(k:ℤ)<2*X.card+3*Y.card+12)) ∧
    ((X.card:ℤ)≤k → 6*(k:ℤ)+X.card<2*(Y.card:ℤ))
  obtain ⟨big,mid,last⟩ := data
  refine ⟨by omega,?_,fun small => by have := last (by omega); omega⟩
  rcases mid with s|⟨l,r⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega,by omega⟩

#print axioms quotas
end Graph189ThreeDensityWindow
