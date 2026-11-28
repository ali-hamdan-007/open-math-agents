import Graph189ThreeSaturationOriginal

open SimpleGraph Finset Graph189ThreeCutSaturationTable
namespace Graph189ThreeOrderWindows

/-- Least orders at which the displayed three-column inequalities force
all terminal quotas, for degrees nine through twenty-three. -/
def cutoff : ℕ → ℕ
  | 9 => 44 | 10 => 48 | 11 => 52 | 12 => 57 | 13 => 61 | 14 => 65
  | 15 => 70 | 16 => 74 | 17 => 78 | 18 => 83 | 19 => 87 | 20 => 92
  | 21 => 96 | 22 => 100 | 23 => 105 | _ => 0

private def start (k x : ℕ) := max x (cutoff k-4-x)
private def row (k x : ℕ) : Bool :=
  (List.range (3*k+x/2+1-start k x)).all fun j =>
    let y := start k x+j
    decide (x*(y+3)≤k*x+3*k*(k+1) → (k<x → Charge k x y) → Graph189ThreeCutSaturation24.GoodStrict k x y ∨ k=22 ∧ x=30 ∧ y=66)
private def valid (k : ℕ) := (List.range (3*k+1)).all (row k)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
private theorem table : (List.range 15).all (fun j => valid (9+j))=true := by decide

private theorem quotas {k x y : ℕ} (lo : 9≤k) (hi : k≤23) (xy : x≤y)
    (floor : cutoff k≤x+y+4) (base : x*(y+3)≤k*x+3*k*(k+1))
    (charge : k<x → Charge k x y) : Graph189ThreeCutSaturation24.GoodStrict k x y ∨ k=22 ∧ x=30 ∧ y=66 := by
  have top : x≤3*k := by
    by_contra! high
    have m := Nat.mul_le_mul_left x (show 3*k+1≤y by omega)
    nlinarith only [base,m,high,Nat.zero_le (k*k)]
  by_cases big : 3*k+x/2<y
  · left
    unfold Graph189ThreeCutSaturation24.GoodStrict
    omega
  have v := List.all_eq_true.mp table (k-9) (List.mem_range.mpr (by omega))
  rw [show 9+(k-9)=k by omega] at v
  have hx := List.all_eq_true.mp v x (List.mem_range.mpr (by omega))
  have lower : start k x≤y := max_le xy (by omega)
  have idx : y-start k x<3*k+x/2+1-start k x := by omega
  have hy := List.all_eq_true.mp hx (y-start k x) (List.mem_range.mpr idx)
  simp only [show start k x+(y-start k x)=y by omega,decide_eq_true_eq] at hy
  exact hy base charge

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : G.vertexConnectivity=3) (lo : 9≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤23)
    (order : cutoff G.secondSmallestDegree≤Fintype.card V) : ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have fit : 4*k+4<cutoff k := by
    change 9≤k at lo
    change k≤23 at hi
    interval_cases k <;> decide
  exfalso
  apply Graph189ThreeCut.excludes_from_quotas hc cap conn (fit.trans_le order)
  intro A B S cut sm orient
  let X := A.filter (fun a => k≤G.degree a)
  let Y := B.filter (fun b => k≤G.degree b)
  have three := sm.trans conn
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨pop,base,charge⟩ := Graph189ThreeCutSaturationFacts.population_data hc cut sm three point orient
  have good : Graph189ThreeCutSaturation24.GoodStrict k X.card Y.card := by
    rcases quotas lo hi orient (order.trans pop) base charge with h|⟨kk,xx,yy⟩
    · exact h
    exact False.elim (Graph189ThreeNearGraph.excludes_boundary (g:=20) (Or.inl rfl) hc cut
      (fun T lt => Graph189CutSides.connected_after_smaller_deletion T (lt.trans_eq sm)) three point
      (X:=X) (Y:=Y) (filter_subset _ _) (filter_subset _ _) (fun a ha => (mem_filter.mp ha).2)
      (fun a ha => (mem_filter.mp ha).2) kk xx yy)
  obtain ⟨big,privateBound,last⟩ := good
  change 3*k<Y.card at big
  change 9*k+X.card<3*Y.card+15 ∨ X.card+1<2*k ∧ 12*k<2*X.card+3*Y.card+12 at privateBound
  change X.card≤k-2 → 6*k+X.card<2*Y.card+2 at last
  have one : (A \ X).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x y ne with h|h
    · exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,h⟩)
    · exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨(mem_sdiff.mp hy).1,h⟩)
  have count := card_sdiff_add_card_eq_card (show X⊆A from filter_subset _ _)
  change 3*(k:ℤ)<Y.card ∧ (9*(k:ℤ)-15+X.card<3*(Y.card:ℤ) ∨
    ((A.card:ℤ)<2*k ∧ 12*(k:ℤ)<2*X.card+3*Y.card+12)) ∧
    ∀i∈S,(∀a∈A,k≤G.degree a → G.Adj a i) → 6*(k:ℤ)+X.card<2*(Y.card:ℤ)+2
  refine ⟨by omega,?_,?_⟩
  · rcases privateBound with h|⟨h,j⟩
    · exact Or.inl (by omega)
    exact Or.inr ⟨by omega,by omega⟩
  · intro i si common
    have limited := Graph189CutColumnCaps.common_below_threshold hc cut
      (fun T lt => Graph189CutSides.connected_after_smaller_deletion T (lt.trans_eq sm))
      (fun v => by simpa only [Nat.add_comm 1] using point v) (X:=X) (Y:=Y) (filter_subset _ _) (filter_subset _ _)
      (t:=1) (by omega) (by change 2*G.secondSmallestDegree+1<Y.card; dsimp only [k] at big; omega) si
      (fun a ha => common a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
    change X.card+1<k at limited
    have h := last (by omega)
    omega

end Graph189ThreeOrderWindows
#print axioms Graph189ThreeOrderWindows.traceable
