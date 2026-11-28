import Graph189MinimumCut
import Graph189DistanceLayers

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189PositiveEvenCut
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Positive even-distance witnesses at a vertex, counted in the original graph. -/
noncomputable def evenOthers (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact (univ.filter (fun y => Even (G.dist x y))).erase x

theorem mem_even_others {x y : V} (ne : y≠x) (parity : Even (G.dist x y)) :
    y∈evenOthers G x := by
  classical
  exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,parity⟩⟩

theorem even_others_card {x : V} {k : ℕ} (cap : G.distEven x≤k+1) : (evenOthers G x).card≤k := by
  classical
  have self : x∈univ.filter (fun y => Even (G.dist x y)) := by simp
  change ((univ.filter (fun y => Even (G.dist x y))).erase x).card≤k
  rw [card_erase_of_mem self]
  change (univ.filter (fun y => Even (G.dist x y))).card≤k+1 at cap
  omega

theorem high_distance_four [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (cap : ∀v,G.distEven v≤1+G.secondSmallestDegree) {x y : V}
    (hx : G.secondSmallestDegree≤G.degree x) (hy : G.secondSmallestDegree≤G.degree y) :
    G.dist x y≤4 := by
  have bd := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
    (diameter_le_five hc cap)
  by_contra! far
  have eq : G.dist x y=5 := by omega
  rcases five_endpoints hc (fun v => by simpa only [Nat.add_comm 1] using cap v) x y eq with l|l <;> omega

omit [Fintype V] in
theorem separator_distance (hc : G.Connected) {A B S : Finset V}
    (sides : Graph189CutSides.CutSides G A B S) {x y : V} (xa : x∈A) (yb : y∈B) :
    ∃i∈S,G.dist x y=G.dist x i+G.dist i y := by
  obtain ⟨w,len⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨i,si,hit⟩ := sides.meets xa yb w
  have both := congrArg Walk.length (Walk.take_spec w hit)
  rw [Walk.length_append,len] at both
  have l := G.dist_le (w.takeUntil i hit)
  have r := G.dist_le (w.dropUntil i hit)
  have h := hc.dist_triangle (u:=x) (v:=i) (w:=y)
  exact ⟨i,si,by omega⟩

end Graph189PositiveEvenCut
#print axioms Graph189PositiveEvenCut.high_distance_four
#print axioms Graph189PositiveEvenCut.separator_distance
