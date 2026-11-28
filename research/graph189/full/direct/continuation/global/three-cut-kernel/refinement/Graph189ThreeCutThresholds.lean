import Graph189ThreeCutPopulation
import Graph189CrossBoundaryProduct

namespace Graph189ThreeCutThresholds

structure Window where
  k : ℕ
  n : ℕ
  cap : ℕ
  deriving DecidableEq

/-- An entry gives the least order for which this certificate works and
an upper bound on the high population of the smaller side. -/
def windows : List Window := [
  ⟨9,45,11⟩, ⟨10,50,12⟩, ⟨11,54,14⟩, ⟨12,59,15⟩, ⟨13,63,17⟩,
  ⟨14,68,18⟩, ⟨15,72,20⟩, ⟨16,77,20⟩, ⟨17,81,22⟩, ⟨18,86,23⟩,
  ⟨19,90,25⟩, ⟨20,95,26⟩, ⟨21,100,27⟩, ⟨22,104,29⟩, ⟨23,109,30⟩,
  ⟨24,114,31⟩, ⟨25,119,31⟩, ⟨26,123,33⟩, ⟨27,128,34⟩, ⟨28,132,36⟩,
  ⟨29,137,37⟩, ⟨30,142,38⟩, ⟨31,146,40⟩, ⟨32,151,41⟩, ⟨33,156,42⟩,
  ⟨34,160,44⟩, ⟨35,165,45⟩, ⟨36,170,45⟩, ⟨37,174,47⟩]

private def valid (w : Window) : Bool :=
  let k : ℤ := w.k
  let h := (w.n:ℤ)-4
  let c : ℤ := w.cap
  let a := c+1
  let b := h-(k-3)-a
  let q := 3*k*(k+1)
  let m := min k c
  decide (4*w.k+4<w.n ∧ k-3≤b ∧ q<a*b ∧ q<b*(b-(k-3)) ∧
    3*k<h-c ∧ 9*k-15+c<3*(h-c) ∧ 6*k+m<2*(h-m))

private theorem checked : windows.all valid = true := by decide

def Certified (k n : ℕ) : Prop := ∃ w∈windows, w.k=k ∧ w.n≤n

theorem order_room {k n : ℕ} (region : Certified k n) : 4*k+4<n := by
  obtain ⟨w,hw,rfl,order⟩ := region
  have h := List.all_eq_true.mp checked w hw
  simp only [valid,decide_eq_true_eq] at h
  exact h.1.trans_le order

private theorem numerical {x y : ℤ} {k n : ℕ} (region : Certified k n)
    (hx : 0≤x) (orientation : x≤y) (total : (n:ℤ)-4≤x+y)
    (product : x*y+3*x≤(k:ℤ)*x+3*k*(k+1)) :
    3*(k:ℤ)<y ∧ 9*(k:ℤ)-15+x<3*y ∧ (x≤k → 6*(k:ℤ)+x<2*y) := by
  obtain ⟨w,hw,rfl,order⟩ := region
  let k : ℤ := w.k
  let h := (w.n:ℤ)-4
  let c : ℤ := w.cap
  let b := h-(k-3)-(c+1)
  have cert := List.all_eq_true.mp checked w hw
  simp only [valid,decide_eq_true_eq] at cert
  change _ ∧ k-3≤b ∧ 3*k*(k+1)<(c+1)*b ∧ 3*k*(k+1)<b*(b-(k-3)) ∧
    3*k<h-c ∧ 9*k-15+c<3*(h-c) ∧ 6*k+min k c<2*(h-min k c) at cert
  obtain ⟨_,bk,left,right,big,single,residual⟩ := cert
  have sum : h≤x+y := by dsimp [h]; omega
  change x*y+3*x≤k*x+3*k*(k+1) at product
  have xx := mul_le_mul_of_nonneg_left orientation hx
  have xb : x≤b := by
    by_contra! high
    have h1 := mul_nonneg (sub_nonneg.mpr high.le) (sub_nonneg.mpr bk)
    have h2 := mul_nonneg hx (sub_nonneg.mpr high.le)
    nlinarith only [h1,h2,right,xx,product]
  have small : x≤c := by
    by_contra! high
    have h1 := mul_nonneg (show 0≤x-(c+1) by omega) (sub_nonneg.mpr xb)
    have h2 := mul_nonneg hx (sub_nonneg.mpr sum)
    dsimp only [b] at h1 left
    nlinarith only [h1,h2,left,product]
  change 3*k<y ∧ 9*k-15+x<3*y ∧ (x≤k → 6*k+x<2*y)
  refine ⟨by omega,by omega,?_⟩
  intro low
  have bound := le_min low small
  omega

open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

theorem quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (three : S.card=3)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (region : Certified G.secondSmallestDegree (Fintype.card V))
    (orient : (A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card) :
    let k : ℤ := G.secondSmallestDegree
    let x : ℤ := (A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card
    let y : ℤ := (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card
    3*k<y ∧ 9*k-15+x<3*y ∧ (x≤k → 6*k+x<2*y) := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k≤G.degree v)
  let Y := B.filter (fun v => k≤G.degree v)
  have prod := Graph189CrossBoundaryProduct.high_product cut hc
    (fun T short => Graph189CutSides.connected_after_smaller_deletion (G:=G) T (short.trans_eq minimum)) cap
  change X.card*Y.card+X.card*S.card≤X.card*k+S.card*(k*k)+S.card*k at prod
  rw [three] at prod
  have prodI : (X.card:ℤ)*Y.card+(X.card:ℤ)*3≤(X.card:ℤ)*k+3*((k:ℤ)*k)+3*k := by exact_mod_cast prod
  have total := Graph189MinimumQuotas.high_population_lower cut
  change (Fintype.card V:ℤ)-S.card-1≤(X.card:ℤ)+Y.card at total
  rw [three] at total
  exact numerical (x:=(X.card:ℤ)) (y:=(Y.card:ℤ)) region (Int.natCast_nonneg X.card)
    (show (X.card:ℤ)≤Y.card by exact_mod_cast orient) (by omega) (by
      change (X.card:ℤ)*Y.card+3*X.card ≤ (k:ℤ)*X.card+3*k*(k+1)
      nlinarith only [prodI])

#print axioms quotas
end Graph189ThreeCutThresholds
