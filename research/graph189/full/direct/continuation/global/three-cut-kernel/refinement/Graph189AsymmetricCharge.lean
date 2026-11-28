import Graph189ThreeColumns
import Graph189ResidualWindows

open SimpleGraph Finset
namespace Graph189AsymmetricCharge
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S X Y : Finset V}

/-- Distinct first-layer allowances u≤v save v−u at every target
second-layer entry, unless the source contacts were already private. -/
theorem alternatives (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (cap : ∀ v,G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (ys : Y⊆B) (xh : ∀ a∈X,G.secondSmallestDegree≤G.degree a)
    (yh : ∀ b∈Y,G.secondSmallestDegree≤G.degree b) (many : G.secondSmallestDegree<X.card)
    (three : S.card=3) {u v : ℕ} (rank : u≤v)
    (sa : ∀ i∈S,(X.filter (G.Adj i)).card≤u)
    (sb : ∀ i∈S,(Y.filter (G.Adj i)).card≤v) :
    let k := G.secondSmallestDegree
    X.card*Y.card+3*X.card≤k*X.card+X.card+3*k*v ∨
      X.card*Y.card+3*X.card+(v-u)*(Y.card-k-v)≤k*X.card+3*u+3*k*v := by
  classical
  let k := G.secondSmallestDegree
  let A1 (i : V) := X.filter (G.Adj i)
  let A2 (i : V) := X.filter (fun a => G.dist i a=2)
  let B1 (i : V) := Y.filter (G.Adj i)
  let B2 (i : V) := Y.filter (fun b => G.dist i b=2)
  let odd (i : V) := (A1 i).card*(B2 i).card+(A2 i).card*(B1 i).card
  have firstA (i : V) : X.filter (fun a => G.dist a i=1)=A1 i := by
    ext a
    simp only [A1,mem_filter,dist_comm (u:=a) (v:=i),dist_eq_one_iff_adj]
  have secondA (i : V) : X.filter (fun a => G.dist a i=2)=A2 i := by
    ext a
    simp only [A2,mem_filter,dist_comm (u:=a) (v:=i)]
  have firstB (i : V) : Y.filter (fun b => G.dist i b=1)=B1 i := by
    simp only [B1,dist_eq_one_iff_adj]
  have raw := Graph189DebitedCutProduct.with_columns hc cut xs ys smaller cap xh yh
  simp only [three,firstA,secondA,firstB] at raw
  change X.card*Y.card+X.card*3≤X.card*k+(∑ i∈S,(A1 i).card)+∑ i∈S,odd i at raw
  have base : X.card*Y.card+3*X.card≤k*X.card+(∑ i∈S,(A1 i).card)+∑ i∈S,odd i := by
    simpa only [Nat.mul_comm X.card 3,Nat.mul_comm X.card k] using raw
  have row (i : V) (hi : i∈S) : odd i+(v-u)*(B2 i).card≤k*v := by
    have both := Graph189PrivateQuota.two_layer_budget G
      (show G.distEven i≤k+1 by have h := cap i; change _≤1+k at h; omega) (A2 i) (B2 i)
      (cut.apart.mono ((filter_subset _ _).trans xs) ((filter_subset _ _).trans ys))
      (fun a ha => (mem_filter.mp ha).2) (fun b hb => (mem_filter.mp hb).2)
    have l := Nat.mul_le_mul_right (B2 i).card (sa i hi)
    have r := Nat.mul_le_mul_left (A2 i).card (sb i hi)
    have t := Nat.mul_le_mul_right v both
    have e : (v-u)+u=v := Nat.sub_add_cancel rank
    have ee := congrArg (fun z => z*(B2 i).card) e
    change (A1 i).card*(B2 i).card+(A2 i).card*(B1 i).card+(v-u)*(B2 i).card≤k*v
    change (A1 i).card*(B2 i).card≤u*(B2 i).card at l
    change (A2 i).card*(B1 i).card≤(A2 i).card*v at r
    nlinarith only [l,r,t,ee]
  have pack := Finset.sum_le_sum row
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,smul_eq_mul,three] at pack
  have leftCap : (∑ i∈S,(A1 i).card)≤3*u := by simpa [three,A1] using Finset.sum_le_sum sa
  have split := Graph189ThreeColumns.concentration hc cut cap xs ys xh yh many three sb
  change (∑ i∈S,(A1 i).card)≤X.card ∨ Y.card≤k+v+(∑ i∈S,(B2 i).card) at split
  change X.card*Y.card+3*X.card≤k*X.card+X.card+3*k*v ∨
      X.card*Y.card+3*X.card+(v-u)*(Y.card-k-v)≤k*X.card+3*u+3*k*v
  have e : 3*(k*v)=3*k*v := by ring
  rw [e] at pack
  rcases split with privatePorts | layer
  · left
    omega
  · right
    have count : Y.card-k-v≤∑ i∈S,(B2 i).card := by omega
    have extra := Nat.mul_le_mul_left (v-u) count
    omega

#print axioms alternatives
end Graph189AsymmetricCharge
