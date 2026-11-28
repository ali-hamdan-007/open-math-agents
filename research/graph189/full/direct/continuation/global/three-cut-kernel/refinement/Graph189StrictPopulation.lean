import Graph189CutColumnCaps
import Graph189DebitedCutProduct

open Finset SimpleGraph
namespace Graph189StrictPopulation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S X Y : Finset V}

/-- Exact even/odd charges with a uniform allowance q for the two
first-distance columns at every anchor. -/
theorem with_bound (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (ys : Y⊆B)
    (xh : ∀ x∈X,G.secondSmallestDegree≤G.degree x)
    (yh : ∀ y∈Y,G.secondSmallestDegree≤G.degree y) {q : ℕ}
    (ca : ∀ i∈S,(X.filter (G.Adj i)).card≤q)
    (cb : ∀ i∈S,(Y.filter (G.Adj i)).card≤q) :
    X.card*Y.card+X.card*S.card≤X.card*G.secondSmallestDegree+
      S.card*q+S.card*(G.secondSmallestDegree*q) := by
  classical
  let k := G.secondSmallestDegree
  let A1 (i : V) := X.filter (fun a => G.dist a i=1)
  let A2 (i : V) := X.filter (fun a => G.dist a i=2)
  let B1 (i : V) := Y.filter (fun b => G.dist i b=1)
  let B2 (i : V) := Y.filter (fun b => G.dist i b=2)
  have base := Graph189DebitedCutProduct.with_columns hc cut xs ys smaller cap xh yh
  change X.card*Y.card+X.card*S.card≤X.card*k+(∑ i∈S,(A1 i).card)+
    ∑ i∈S,((A1 i).card*(B2 i).card+(A2 i).card*(B1 i).card) at base
  have a1 (i : V) (hi : i∈S) : (A1 i).card≤q := by
    simpa only [A1,dist_comm (v:=i),dist_eq_one_iff_adj] using ca i hi
  have b1 (i : V) (hi : i∈S) : (B1 i).card≤q := by
    simpa only [B1,dist_eq_one_iff_adj] using cb i hi
  have first : (∑ i∈S,(A1 i).card)≤S.card*q := by
    simpa using (Finset.sum_le_sum fun i hi => a1 i hi)
  have row (i : V) (hi : i∈S) : (A1 i).card*(B2 i).card+(A2 i).card*(B1 i).card≤k*q := by
    have both := Graph189PrivateQuota.two_layer_budget G
      (show G.distEven i≤k+1 by simpa only [k,Nat.add_comm 1] using cap i) (A2 i) (B2 i)
      (cut.apart.mono ((filter_subset _ _).trans xs) ((filter_subset _ _).trans ys))
      (fun a ha => dist_comm.trans (mem_filter.mp ha).2) (fun b hb => (mem_filter.mp hb).2)
    have left := Nat.mul_le_mul_right (B2 i).card (a1 i hi)
    have right := Nat.mul_le_mul_left (A2 i).card (b1 i hi)
    calc
      _ ≤ q*(B2 i).card+(A2 i).card*q := Nat.add_le_add left right
      _ = ((A2 i).card+(B2 i).card)*q := by rw [Nat.add_mul,Nat.mul_comm q,Nat.add_comm]
      _ ≤ k*q := Nat.mul_le_mul_right q both
  have odd : (∑ i∈S,((A1 i).card*(B2 i).card+(A2 i).card*(B1 i).card)) ≤ S.card*(k*q) := by
    simpa using Finset.sum_le_sum row
  change _≤X.card*k+S.card*q+S.card*(k*q)
  omega

/-- When both high populations exceed 2k+1, all the first-distance
columns are short by at least two. -/
theorem balanced (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree) (room : 2<S.card)
    (xs : X⊆A) (ys : Y⊆B) (xh : ∀ x∈X,G.secondSmallestDegree≤G.degree x)
    (yh : ∀ y∈Y,G.secondSmallestDegree≤G.degree y)
    (bigX : 2*G.secondSmallestDegree+1<X.card)
    (bigY : 2*G.secondSmallestDegree+1<Y.card) :
    let q := G.secondSmallestDegree-2
    X.card*Y.card+X.card*S.card≤X.card*G.secondSmallestDegree+
      S.card*q+S.card*(G.secondSmallestDegree*q) := by
  have cp (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by have h := cap v; omega
  apply with_bound hc cut smaller cap xs ys xh yh
  · intro i hi
    have h := Graph189CutColumnCaps.below_threshold hc cut smaller cp xs ys (t:=1) (by omega) bigY hi
    omega
  · intro i hi
    have h := Graph189CutColumnCaps.below_threshold hc cut.swap smaller cp ys xs (t:=1) (by omega) bigX hi
    omega

#print axioms with_bound
#print axioms balanced
end Graph189StrictPopulation
