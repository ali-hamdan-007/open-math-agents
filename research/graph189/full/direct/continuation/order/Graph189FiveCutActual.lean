import Graph189LowMixedCut
import Graph189ActualRootWidthBounds
import Graph189FiveCutDebit

namespace Graph189CutSides
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Within the finite five-cut band the original metric condition and the
order lower bound exclude a low vertex on any minimum five-cut. -/
theorem no_low_on_minimum_five_cut (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree) (S : Finset V)
    (disc : ¬(G.induce {u : V | u ∉ S}).Connected)
    (minimum : S.card = G.vertexConnectivity) (five : S.card = 5)
    (hk : 46 ≤ G.secondSmallestDegree) (ku : G.secondSmallestDegree ≤ 58)
    (base : 7*G.secondSmallestDegree ≤ Fintype.card V+57) :
    ∀ z ∈ S, G.secondSmallestDegree ≤ G.degree z := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let e := G.maxDegree-k
  change 46 ≤ k at hk
  change k ≤ 58 at ku
  change 7*k ≤ n+57 at base
  have order : 4*k+2 ≤ n := by omega
  have width := Graph189RootWidth.continuous_at_actual_degree hc cap order
  have mx := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc cap
  change G.maxDegree ≤ 3*k at mx
  have emax : e ≤ 2*k := by dsimp [e]; omega
  have survive : ∃ u, u ∉ S := by
    by_contra! full
    have hall := Finset.eq_univ_iff_forall.mpr full
    rw [hall,card_univ] at five
    change n=5 at five
    omega
  obtain ⟨A,B,sides⟩ := exists_cutSides_of_disconnected S survive disc
  have smaller (T : Finset V) (hT : T.card < S.card) :=
    connected_after_smaller_deletion (G := G) T (minimum ▸ hT)
  intro z hz
  by_contra! hzlow
  let d := k-G.degree z
  have forbidden {A' B' : Finset V} (ss : CutSides G A' B' S) (small : A'.card ≤ B'.card) : False := by
    obtain ⟨_,_,_,_,_,_,r,_,rmin,rmax,_,debit,mixed⟩ := ss.low_cut_three_bounds hc smaller cap hz hzlow
    rw [five] at rmax mixed
    obtain ⟨total,cross⟩ := ss.low_cut_product hc smaller cap hz hzlow
    rw [five] at total cross
    change n=5+A'.card+B'.card at total
    change A'.card*B'.card ≤ A'.card*k+5*(k*k) at cross
    change n+k*d ≤ 2*k+(k+1)*r at debit
    change n+(r-1)*(k+1-5) ≤ 6*k+A'.card+5+r*(e+5-1) at mixed
    have positive : 1 ≤ d := by dsimp [d,k]; omega
    have nb : 7*(k:ℤ) ≤ (n:ℤ)+57 := by exact_mod_cast base
    have full : (n:ℤ)=5+A'.card+B'.card := by exact_mod_cast total
    have prod : (A'.card:ℤ)*B'.card ≤ (A'.card:ℤ)*k+5*((k:ℤ)*k) := by exact_mod_cast cross
    have last : (n:ℤ)+((r-1 : ℕ):ℤ)*((k+1-5 : ℕ):ℤ) ≤
      6*(k:ℤ)+A'.card+5+(r:ℤ)*((e+5-1 : ℕ):ℤ) := by exact_mod_cast mixed
    have hkl : 5 ≤ k+1 := by omega
    have el : e+5-1=e+4 := by omega
    rw [Nat.cast_sub rmin,Nat.cast_sub hkl,el] at last
    push_cast at last
    exact Graph189FiveCutDebit.no_low (k := k) (n := n) (e := e) (x := A'.card) (y := B'.card)
      (d := d) (r := r) (by exact_mod_cast hk) (by exact_mod_cast ku) (by omega)
      (by positivity) (by exact_mod_cast emax) width (by positivity) (by exact_mod_cast small)
      (by omega) (by nlinarith only [prod]) (by exact_mod_cast positive) (by exact_mod_cast rmax)
      (by exact_mod_cast debit) (by linarith only [last])
  rcases le_total A.card B.card with h | h
  · exact forbidden sides h
  · exact forbidden sides.swap h

#print axioms no_low_on_minimum_five_cut
end Graph189CutSides
