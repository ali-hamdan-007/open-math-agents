import Graph189WidthSectors

open Finset SimpleGraph
namespace Graph189LastCliqueOrders

/-- At the first order of the paper's terminal clique, the maximum-degree
root inequalities and the matching obstruction are incompatible. -/
private def possible (k e : ℕ) : Bool :=
  let b := 5*k-4
  let w := Graph189RootWidth.width b k (k+e)
  let L := b-(k+e)-k-2
  let t := (b-2*k+k)/(k+1)
  let m := min e (w+1-t)
  decide (Graph189MatchedFloor.Fits b k e ∧ (w-k)*L≤k*(2*k-e-1) ∧
    (m+t≤w+1 → 2*k+(k+1)*(t-1)<b → (k*w+m*t)*L≤k*(k*(k+e))))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem table : (List.range 15).all (fun j =>
    let k := 7+j
    (List.range (2*k+1)).all (fun e => !possible k e))=true := by decide

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (lo : 7≤G.secondSmallestDegree) (hi : G.secondSmallestDegree≤21)
    (floor : 5*G.secondSmallestDegree-4≤Fintype.card V) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  by_contra bad
  let k := G.secondSmallestDegree
  let d := G.maxDegree
  let e := d-k
  let b := 5*k-4
  have dk : k≤d := by
    obtain ⟨v,z,vz⟩ := exists_pair_ne V
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) v z vz with h|h
    · exact h.trans (G.degree_le_maxDegree _)
    · exact h.trans (G.degree_le_maxDegree _)
  have ke : k+e=d := by dsimp [e]; omega
  have lim := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc
    (fun v => (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap)
  change d≤3*k at lim
  change 7≤k at lo
  change k≤21 at hi
  have row := List.all_eq_true.mp table (k-7) (List.mem_range.mpr (by omega))
  rw [show 7+(k-7)=k by omega] at row
  have no := List.all_eq_true.mp row e (List.mem_range.mpr (by dsimp [e]; omega))
  have fit := Graph189MatchedFloor.necessary hc cap bad floor (by omega : 3≤k)
  have col := Graph189MatchedFloor.column hc cap floor
  let w := Graph189RootWidth.width b k (k+e)
  let t := (b-2*k+k)/(k+1)
  let m := min e (w+1-t)
  have paid (size : m+t≤w+1) (count : 2*k+(k+1)*(t-1)<b) :
      (k*w+m*t)*(b-(k+e)-k-2)≤k*(k*(k+e)) := by
    have h := Graph189PaidRootWidth.bound hc cap floor (w:=w) (by dsimp [w]; rw [ke])
      size (min_le_left e _) count
    rw [ke]
    exact h
  have column : (w-k)*(b-(k+e)-k-2)≤k*(2*k-e-1) := by
    dsimp only [w]; rw [ke]; exact col
  have yes : possible k e=true := decide_eq_true ⟨fit,column,paid⟩
  simp [yes] at no

end Graph189LastCliqueOrders
#print axioms Graph189LastCliqueOrders.traceable
