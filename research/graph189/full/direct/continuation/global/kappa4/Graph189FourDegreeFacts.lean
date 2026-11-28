import Graph189FourDegreeColumns
import Graph189FourDegreeTable

open Finset SimpleGraph Graph189FourDegreeTable
namespace Graph189FourDegreeFacts
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

theorem quotas (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (four : S.card=4)
    (cap : ∀v,G.distEven v≤1+G.secondSmallestDegree)
    (lo : 31≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤32)
    (mx : G.maxDegree≤maxDeg G.secondSmallestDegree)
    (order : 6*G.secondSmallestDegree≤Fintype.card V+19)
    (orient : (A.filter (fun a => G.secondSmallestDegree≤G.degree a)).card≤
      (B.filter (fun b => G.secondSmallestDegree≤G.degree b)).card) :
    let k := G.secondSmallestDegree
    let x := (A.filter (fun a => k≤G.degree a)).card
    let y := (B.filter (fun b => k≤G.degree b)).card
    Graph189FourCutSaturationTable.Good k x y := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun a => k≤G.degree a)
  let Y := B.filter (fun b => k≤G.degree b)
  have xs : X⊆A := filter_subset _ _
  have ys : Y⊆B := filter_subset _ _
  have xh (a : V) (ha : a∈X) : k≤G.degree a := (mem_filter.mp ha).2
  have yh (b : V) (hb : b∈Y) : k≤G.degree b := (mem_filter.mp hb).2
  obtain ⟨pop,base,charge⟩ := Graph189FourCutSaturationFacts.population_data hc cut minimum four cap orient
  change Fintype.card V≤X.card+Y.card+5 at pop
  change X.card≤Y.card at orient
  apply Graph189FourDegreeTable.quotas lo hi orient (by change 6*G.secondSmallestDegree≤X.card+Y.card+24; omega) base charge
  intro many
  change maxDeg k+2<X.card at many
  change G.maxDegree≤maxDeg k at mx
  have cp (v : V) : G.distEven v≤k+1 := by simpa only [k,Nat.add_comm] using cap v
  have smaller (T : Finset V) (lt : T.card<S.card) := Graph189CutSides.connected_after_smaller_deletion
    (G:=G) T (lt.trans_eq minimum)
  have kx : k<X.card := by dsimp [maxDeg] at many; change k≤32 at hi; split_ifs at many <;> omega
  let a (i : V) := (X.filter (G.Adj i)).card
  let b (i : V) := (Y.filter (G.Adj i)).card
  let u (i : V) := (X.filter (fun x => G.dist i x=2)).card
  let v (i : V) := (Y.filter (fun y => G.dist i y=2)).card
  let f (i : V) := a i+(a i*v i+u i*b i)+(2*b i+(if a i+4≤k+1 then 2 else 1)*v i)
  have combined (i : V) (si : i∈S) : f i≤rowCap k :=
    single lo hi
      (Graph189FourDegreeColumns.first_bound hc cut smaller four cp xs ys (by omega) si)
      (Graph189FourDegreeColumns.first_bound hc cut.swap smaller four cp ys xs (by omega) si)
      ((Graph189FourDegreeColumns.first_sum cut xs ys i).trans mx)
      (Graph189PrivateQuota.two_layer_budget G (cp i) _ _
        (cut.apart.mono ((filter_subset _ _).trans xs) ((filter_subset _ _).trans ys))
        (fun _ h => (mem_filter.mp h).2) (fun _ h => (mem_filter.mp h).2))
  have sum := sum_le_sum combined
  simp only [f,sum_add_distrib,sum_const,smul_eq_mul,four] at sum
  have coverage := Graph189FourDegreeColumns.weighted_cover hc cut minimum.le cap xs ys xh yh kx
  rw [four] at coverage
  have raw := Graph189DebitedCutProduct.with_columns hc cut xs ys smaller cap xh yh
  have aeq (i : V) : (X.filter fun x => G.dist x i=1).card=a i := by simp [a,dist_eq_one_iff_adj,G.adj_comm]
  have ueq (i : V) : (X.filter fun x => G.dist x i=2).card=u i := by simp [u,G.dist_comm]
  have beq (i : V) : (Y.filter fun y => G.dist i y=1).card=b i := by simp [b,dist_eq_one_iff_adj]
  simp only [aeq,ueq,beq,four] at raw
  change X.card*Y.card+X.card*4≤X.card*k+(∑ i∈S,a i)+∑ i∈S,(a i*v i+u i*b i) at raw
  change 2*Y.card≤∑ i∈S,(2*b i+(if a i+4≤k+1 then 2 else 1)*v i) at coverage
  simp only [sum_add_distrib] at raw coverage
  change X.card*(Y.card+4)+2*Y.card≤k*X.card+4*rowCap k
  rw [Nat.mul_add,Nat.mul_comm k X.card]
  omega

#print axioms quotas
end Graph189FourDegreeFacts
