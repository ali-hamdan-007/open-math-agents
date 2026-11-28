import Graph189AsymmetricCharge
import Graph189SaturatedOpposite
import Graph189CutColumnCaps
import Graph189FourCutSaturationTable

open SimpleGraph Finset Graph189FourCutSaturationTable
namespace Graph189FourCutSaturationFacts
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S X Y : Finset V}

theorem first_column (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (four : S.card=4) (cap : ∀ v,G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (ys : Y⊆B) (xh : ∀ a∈X,G.secondSmallestDegree≤G.degree a)
    (yh : ∀ b∈Y,G.secondSmallestDegree≤G.degree b) {i : V} (hi : i∈S) :
    (X.filter (G.Adj i)).card≤level G.secondSmallestDegree X.card Y.card := by
  classical
  let k := G.secondSmallestDegree
  have cp (v : V) : G.distEven v≤k+1 := by simpa only [k,Nat.add_comm] using cap v
  change _≤level k X.card Y.card
  unfold level
  split
  next high =>
    have h := Graph189CutColumnCaps.below_threshold hc cut smaller cp xs ys
      (t:=1) (by omega) high hi
    omega
  next low =>
    split
    next middle =>
      rcases middle with large|⟨many,over⟩
      · have h := Graph189CutColumnCaps.below_threshold hc cut smaller cp xs ys
          (t:=0) (by omega) (by omega) hi
        omega
      · by_contra! full
        have h := Graph189SaturatedOpposite.population hc cut.swap smaller cap ys xs yh xh many hi
          (show G.secondSmallestDegree≤(X.filter (G.Adj i)).card by change k≤_; omega)
        change X.card+S.card*Y.card≤k+S.card*(2*k) at h
        rw [four] at h
        omega
    next other =>
      obtain ⟨b,bb,bi⟩ := (cut.contacts_of_minimum smaller hi).2
      exact Graph189PortDifference.common_label_capacity hc cut
        (X:=(X.filter (G.Adj i))) ((filter_subset _ _).trans xs)
        (fun v hv => (mem_filter.mp hv).2.symm) bb bi cp

theorem population_data (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (four : S.card=4)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (orient : (A.filter (fun a => G.secondSmallestDegree≤G.degree a)).card≤
      (B.filter (fun b => G.secondSmallestDegree≤G.degree b)).card) :
    let k := G.secondSmallestDegree
    let x := (A.filter (fun a => k≤G.degree a)).card
    let y := (B.filter (fun b => k≤G.degree b)).card
    (Fintype.card V≤x+y+5) ∧ x*(y+4)≤k*x+4*k*(k+1) ∧
      (k<x → Charge k x y) := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun a => k≤G.degree a)
  let Y := B.filter (fun b => k≤G.degree b)
  have xs : X⊆A := filter_subset _ _
  have ys : Y⊆B := filter_subset _ _
  have xh (a : V) (ha : a∈X) : k≤G.degree a := (mem_filter.mp ha).2
  have yh (b : V) (hb : b∈Y) : k≤G.degree b := (mem_filter.mp hb).2
  have smaller (T : Finset V) (lt : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have cross := Graph189CrossBoundaryProduct.high_product cut hc smaller cap
  change X.card*Y.card+X.card*S.card≤X.card*k+S.card*(k*k)+S.card*k at cross
  rw [four] at cross
  have base : X.card*(Y.card+4)≤k*X.card+4*k*(k+1) := by nlinarith only [cross]
  have pop := Graph189MinimumQuotas.high_population_lower cut
  change (Fintype.card V:ℤ)-S.card-1≤(X.card:ℤ)+Y.card at pop
  rw [four] at pop
  have sa (i : V) (iS : i∈S) := first_column hc cut smaller four cap xs ys xh yh iS
  have sb (i : V) (iS : i∈S) := first_column hc cut.swap smaller four cap ys xs yh xh iS
  have lower : Fintype.card V≤X.card+Y.card+5 := by omega
  refine ⟨lower,base,fun many => ?_⟩
  have h := Graph189AsymmetricCharge.alternatives_general hc cut smaller cap xs ys xh yh many
    (level_order (k:=k) orient) sa sb
  simpa [four,Charge,k] using h

theorem quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (four : S.card=4)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (lo : 33≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤35)
    (order : 6*G.secondSmallestDegree≤Fintype.card V+19)
    (orient : (A.filter (fun a => G.secondSmallestDegree≤G.degree a)).card≤
      (B.filter (fun b => G.secondSmallestDegree≤G.degree b)).card) :
    let k := G.secondSmallestDegree
    let x := (A.filter (fun a => k≤G.degree a)).card
    let y := (B.filter (fun b => k≤G.degree b)).card
    Good k x y := by
  obtain ⟨pop,base,charge⟩ := population_data hc cut minimum four cap orient
  exact Graph189FourCutSaturationTable.quotas lo hi orient (by omega) base charge

#print axioms first_column
#print axioms population_data
#print axioms quotas
end Graph189FourCutSaturationFacts
