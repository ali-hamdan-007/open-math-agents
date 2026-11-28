import Graph189StrictLowWedge
import Graph189MinimumCutOrder

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189CutSides.CutSides
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- The order and degree-deficit bound at a low separator vertex is strict.
The extra common neighbor supplied by the deficit has strictly higher degree. -/
theorem strict_low_cut (sides : Graph189CutSides.CutSides G A B S) (hc : G.Connected)
    (smaller : ∀T : Finset V,T.card<S.card → (G.induce {u : V | u∉T}).Connected)
    (cap : ∀v,G.distEven v≤1+G.secondSmallestDegree) {z : V} (zin : z∈S)
    (low : G.degree z<G.secondSmallestDegree) :
    ∃r≤S.card, G.secondSmallestDegree-G.degree z+1≤r ∧
      Fintype.card V+G.secondSmallestDegree*(G.secondSmallestDegree-G.degree z)<
        2*G.secondSmallestDegree+(G.secondSmallestDegree+1)*r := by
  classical
  obtain ⟨a,aa,b,bb,az,bz,r,eq,_,rs,deficit,_⟩ := sides.low_cut_deficit hc smaller cap zin low
  let k := G.secondSmallestDegree
  let R := G.neighborFinset a∩G.neighborFinset b
  let U := G.neighborFinset a∪G.neighborFinset b
  let W := G.neighborFinset z∪U
  change r=R.card at eq
  obtain ⟨i,inR,other⟩ := exists_mem_ne (show 1<R.card by omega) z
  have high {v : V} (ne : v≠z) := (degree_pair (G:=G) v z ne).resolve_right (not_le.mpr low)
  have non := sides.no_cross _ aa _ bb
  have wedge := Graph189WedgeOrder.strict_order (k:=G.secondSmallestDegree) hc az.symm bz.symm non
    ((G.mem_neighborFinset _ _).mp (mem_inter.mp inR).1)
    ((G.mem_neighborFinset _ _).mp (mem_inter.mp inR).2) (low.trans_le (high other))
    (fun v => by simpa only [Nat.add_comm] using cap v)
  change Fintype.card V+(k+1)*W.card<3*k+2+k*(G.degree z+G.distEven z)+G.degree a+G.degree b at wedge
  have neq : a≠b := fun e => disjoint_left.mp sides.apart (e ▸ aa) bb
  have aabs : a∉U := by
    intro h
    rcases mem_union.mp h with h|h
    · exact G.irrefl ((G.mem_neighborFinset _ _).mp h)
    · exact non ((G.mem_neighborFinset _ _).mp h).symm
  have babs : b∉U := by simp [U,G.mem_neighborFinset,non]
  have inc : insert a (insert b U)⊆W := by
    intro v hv
    rcases mem_insert.mp hv with rfl|hv
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr az.symm)
    rcases mem_insert.mp hv with rfl|hv
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr bz.symm)
    exact mem_union_right _ hv
  have count := card_le_card inc
  rw [card_insert_of_notMem (by simp [neq,aabs]),card_insert_of_notMem babs] at count
  have union := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  rw [G.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree] at union
  change U.card+R.card=G.degree a+G.degree b at union
  have mult := Nat.mul_le_mul_left (k+1) (show G.degree a+G.degree b+2≤W.card+r by omega)
  have eps := Nat.mul_le_mul_left k (show G.distEven z≤k+1 by simpa [k,Nat.add_comm] using cap z)
  have deg := Nat.mul_le_mul_left k (Nat.add_le_add (high az.ne) (high bz.ne))
  change k*(k+k)≤k*(G.degree a+G.degree b) at deg
  have diff := congrArg (fun t : ℕ => k*t) (show G.degree z+(k-G.degree z)=k by dsimp [k]; omega)
  refine ⟨r,rs,deficit,?_⟩
  change Fintype.card V+k*(k-G.degree z)<2*k+(k+1)*r
  nlinarith only [wedge,mult,eps,deg,diff]

#print axioms strict_low_cut
end Graph189CutSides.CutSides
