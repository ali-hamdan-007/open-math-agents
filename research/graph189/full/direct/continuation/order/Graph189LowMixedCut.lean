import Graph189MixedDebit
import Graph189MaximumDegree
import Graph189NineCutDebit

namespace Graph189CutSides
namespace CutSides
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {A B S : Finset V}

/-- A low vertex in the separator gives one pair of contacts witnessing all
three deficit inequalities, including the mixed debit for the same pair. -/
theorem low_cut_three_bounds (sides : CutSides G A B S) (hc : G.Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    {z : V} (hz : z ∈ S) (low : G.degree z < G.secondSmallestDegree) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a z ∧ G.Adj b z ∧ ∃ r : ℕ,
      r = (G.neighborFinset a ∩ G.neighborFinset b).card ∧ 1 ≤ r ∧ r ≤ S.card ∧
      G.secondSmallestDegree - G.degree z + 1 ≤ r ∧
      Fintype.card V + G.secondSmallestDegree * (G.secondSmallestDegree - G.degree z) ≤
        2 * G.secondSmallestDegree + (G.secondSmallestDegree + 1)*r ∧
      Fintype.card V + (r-1)*(G.secondSmallestDegree+1-S.card) ≤
        (S.card+1)*G.secondSmallestDegree+A.card+S.card+
        r*(G.maxDegree-G.secondSmallestDegree+S.card-1) := by
  obtain ⟨a,ha,b,hb,az,bz,r,eq,hr,hs,deficit,debit⟩ :=
    sides.low_cut_deficit hc smaller cap hz low
  have ah := (degree_pair (G := G) a z az.ne).resolve_right (not_le.mpr low)
  have highB (y : V) (hy : y ∈ B) : G.secondSmallestDegree ≤ G.degree y :=
    (degree_pair (G := G) y z (fun e => disjoint_left.mp sides.right_cut (e ▸ hy) hz)).resolve_right
      (not_le.mpr low)
  have mixed := Graph189MixedDebit.mixed_cut_pair sides hc smaller cap ha hb az bz ah highB
  rw [← eq] at mixed
  have order := (sides.low_cut_product hc smaller cap hz low).1
  exact ⟨a,ha,b,hb,az,bz,r,eq,hr,hs,deficit,debit,by omega⟩

#print axioms low_cut_three_bounds

/-- The rational nine-cut test consumes the signed witnesses without
relaxing the integrality of their common-neighbor count. -/
theorem no_low_at_nine_of_width (sides : CutSides G A B S) (hc : G.Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) (nine : S.card = 9)
    (hk : 163 ≤ G.secondSmallestDegree) (base : 10*G.secondSmallestDegree ≤ Fintype.card V+71)
    (w : ℚ) :
    let k : ℚ := G.secondSmallestDegree
    let n : ℚ := Fintype.card V
    let e : ℚ := (G.maxDegree-G.secondSmallestDegree : ℕ)
    2*(n-2*k)+k*e ≤ (k+1)*w → w*(n-2*k-e-2) ≤ k*(k+e) →
    ∀ z ∈ S, G.secondSmallestDegree ≤ G.degree z := by
  dsimp only
  intro width budget z hz
  by_contra! low
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let e := G.maxDegree-k
  let d := k-G.degree z
  change 163 ≤ k at hk
  change 10*k ≤ n+71 at base
  change G.degree z < k at low
  have em : e ≤ 2*k := by
    have mx := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc cap
    change G.maxDegree ≤ 3*k at mx
    dsimp [e]; omega
  have forbidden {U W : Finset V} (cut : CutSides G U W S) (ord : U.card ≤ W.card) : False := by
    obtain ⟨_,_,_,_,_,_,r,_,rp,rs,_,debit,mixed⟩ := cut.low_cut_three_bounds hc smaller cap hz low
    obtain ⟨_,prod⟩ := cut.low_cut_product hc smaller cap hz low
    rw [nine] at rs mixed prod
    change n+k*d ≤ 2*k+(k+1)*r at debit
    change n+(r-1)*(k+1-9) ≤ 10*k+U.card+9+r*(e+9-1) at mixed
    change U.card*W.card ≤ U.card*k+9*(k*k) at prod
    have kk : (163:ℚ) ≤ k := by exact_mod_cast hk
    have nb : 10*(k:ℚ) ≤ (n:ℚ)+71 := by exact_mod_cast base
    have product : (U.card:ℚ)*W.card ≤ U.card*(k:ℚ)+9*(k*k:ℚ) := by exact_mod_cast prod
    have lo : (n:ℚ)+(k:ℚ)*d ≤ 2*k+((k:ℚ)+1)*r := by exact_mod_cast debit
    have mx : (n:ℚ)+((r-1 : ℕ):ℚ)*((k+1-9 : ℕ):ℚ) ≤
        10*(k:ℚ)+U.card+9+(r:ℚ)*((e+9-1 : ℕ):ℚ) := by exact_mod_cast mixed
    rw [Nat.cast_sub rp, Nat.cast_sub (by omega : 9≤k+1), show e+9-1=e+8 by omega] at mx
    push_cast at mx
    have hd : 1 ≤ d := by dsimp [d]; omega
    have finit : r=9 ∨ r≤8 := by omega
    exact Graph189NineCutDebit.no_low_at_nine (k:=k) (n:=n) (e:=e) (w:=w)
      (x:=U.card) (y:=W.card) (r:=r) (d:=d) kk (by linarith only [nb])
      (by positivity) (by exact_mod_cast em) width budget (by positivity)
      (by exact_mod_cast ord) (by nlinarith only [product]) (by exact_mod_cast hd)
      (finit.elim (fun h => Or.inl (by exact_mod_cast h)) (fun h => Or.inr (by exact_mod_cast h)))
      (by linarith only [lo]) (by linarith only [mx])
  rcases le_total A.card B.card with h | h
  · exact forbidden sides h
  · exact forbidden sides.swap h

#print axioms no_low_at_nine_of_width
end CutSides
end Graph189CutSides
