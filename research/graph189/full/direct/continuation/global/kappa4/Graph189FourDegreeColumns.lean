import Graph189FourCutSaturationFacts
import Graph189SoleNearestData
import Graph189ActualScalarWidth
import Graph189ThirdLayerDegreeCeiling

open Finset SimpleGraph
namespace Graph189FourDegreeColumns
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S X Y : Finset V}

theorem first_sum (cut : Graph189CutSides.CutSides G A B S) (xs : X⊆A) (ys : Y⊆B) (i : V) :
    (X.filter (G.Adj i)).card+(Y.filter (G.Adj i)).card≤G.maxDegree := by
  have d := cut.apart.mono ((filter_subset (G.Adj i) X).trans xs) ((filter_subset (G.Adj i) Y).trans ys)
  have inc : X.filter (G.Adj i) ∪ Y.filter (G.Adj i)⊆G.neighborFinset i := by
    intro x hx
    rcases mem_union.mp hx with h|h <;> exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp h).2
  have h := card_le_card inc
  rw [card_union_of_disjoint d,G.card_neighborFinset_eq_degree] at h
  exact h.trans (G.degree_le_maxDegree i)

/-- Above maximum degree plus two on the far side, an anchor cannot have
k−1 first neighbors on the near side of a minimum four-cut. -/
theorem first_bound (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀T : Finset V,T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (four : S.card=4) (cp : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (xs : X⊆A) (ys : Y⊆B) (big : G.maxDegree+2<Y.card) {i : V} (hi : i∈S) :
    (X.filter (G.Adj i)).card+2≤G.secondSmallestDegree := by
  by_contra! fail
  have h := Graph189AlmostFullColumn.opposite_population hc cut smaller cp xs ys hi
    (t:=1) (by omega) (by omega)
  have degree := first_sum cut xs ys i
  omega

/-- Each high target costs either a port incidence, two second-layer
incidences, or a unique second-layer label whose opposite column is small. -/
theorem weighted_cover (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card≤G.vertexConnectivity) (cap : ∀v,G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (ys : Y⊆B) (xh : ∀a∈X,G.secondSmallestDegree≤G.degree a)
    (yh : ∀b∈Y,G.secondSmallestDegree≤G.degree b) (many : G.secondSmallestDegree<X.card) :
    2*Y.card≤∑ i∈S,(2*(Y.filter (G.Adj i)).card+
      (if (X.filter (G.Adj i)).card+S.card≤G.secondSmallestDegree+1 then 2 else 1)*
        (Y.filter (fun b => G.dist i b=2)).card) := by
  classical
  let w (i : V) : ℕ := if (X.filter (G.Adj i)).card+S.card≤G.secondSmallestDegree+1 then 2 else 1
  let fee (i b : V) : ℕ := (if G.Adj i b then 2 else 0)+(if G.dist i b=2 then w i else 0)
  have positive (i : V) : 1≤w i := by simp only [w]; split <;> decide
  have row (b : V) (hb : b∈Y) : 2≤∑ i∈S,fee i b := by
    have unit (i : V) (hi : i∈S) := single_le_sum (fun j (_ : j∈S) => Nat.zero_le (fee j b)) hi
    by_cases port : ∃i∈S,G.Adj i b
    · obtain ⟨i,si,ib⟩ := port
      apply le_trans _ (unit i si)
      simp only [fee,if_pos ib]
      omega
    have np (i : V) (si : i∈S) (ib : G.Adj i b) := port ⟨i,si,ib⟩
    obtain ⟨i,si,di⟩ := Graph189ThreeColumns.nonport_second hc cut cap xs xh many (ys hb) (yh b hb) np
    by_cases unique : ∀ j∈S,G.dist j b=2 → i=j
    · have wit : Graph189SoleNearestSides.Witness G B S b i := ⟨ys hb,si,yh b hb,np,di,unique⟩
      have debit := (Graph189SoleNearestSides.debit hc cut.swap minimum
        (fun x => by simpa only [Nat.add_comm] using cap x) wit).1
      have sub := card_le_card (filter_subset_filter (G.Adj i) xs)
      have wi : w i=2 := if_pos (by omega)
      apply le_trans _ (unit i si)
      simp only [fee,if_pos di,wi]
      omega
    push Not at unique
    obtain ⟨j,sj,dj,diff⟩ := unique
    have sub : ({i,j}:Finset V)⊆S := insert_subset si (singleton_subset_iff.mpr sj)
    have h := sum_le_sum_of_subset_of_nonneg sub (fun a _ _ => Nat.zero_le (fee a b))
    apply le_trans _ h
    simp [diff,fee,di,dj]
    have pi := positive i
    have pj := positive j
    omega
  have total := sum_le_sum row
  simp only [sum_const,smul_eq_mul] at total
  rw [Finset.sum_comm] at total
  have col (i : V) : (∑ b∈Y,fee i b)=2*(Y.filter (G.Adj i)).card+
        w i*(Y.filter (fun b => G.dist i b=2)).card := by
    simp only [fee,sum_add_distrib,←sum_filter,sum_const,smul_eq_mul,Nat.mul_comm]
  simp_rw [col] at total
  simpa only [Nat.mul_comm Y.card 2] using total

#print axioms weighted_cover
end Graph189FourDegreeColumns
