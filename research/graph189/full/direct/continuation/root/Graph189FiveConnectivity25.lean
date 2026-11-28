import Graph189HighConnectivityQuarter
import Graph189OnePortThreeCut
import Graph189ThirdLayerDegreeCeiling
import Graph189LargeDegreeTrace

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189FiveConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem low_width {n e w : ℤ} (lower : 139≤n) (ep : 0≤e) (em : e≤47)
    (ore : n≤76+25*e) (width : 2*(n-50)+25*e≤26*w)
    (budget : w*(n-50-e-2)≤25*(25+e)) : False := by
  have wp : 0≤w := by omega
  have cap := (mul_le_mul_of_nonneg_left (by omega : 139-50-e-2≤n-50-e-2) wp).trans budget
  have wit : 2*(139-50)+25*e≤26*w := by omega
  interval_cases e <;> omega

/-- In a hypothetical nontraceable graph at k=25 and connectivity five,
a minimum cut containing the low vertex would force degree 24 there.
The minimum-degree order bound then violates the maximum-degree width. -/
theorem traceable_low (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (k25 : G.secondSmallestDegree=25) (five : G.vertexConnectivity=5)
    (S : Finset V) (size : S.card=G.vertexConnectivity)
    (cut : ¬(G.induce {u : V | u∉S}).Connected)
    {z : V} (inside : z∈S) (low : G.degree z<G.secondSmallestDegree) :
    ∃a b, ∃p : G.Walk a b,p.IsHamiltonian := by
  classical
  by_contra bad
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using upper v
  have base := Graph189RotationLinked.base_order bad point (l:=5) (by decide) five.ge (by omega)
  rw [k25] at base
  have remain : ∃v,v∉S := by
    by_contra! full
    rw [eq_univ_iff_forall.mpr full,card_univ] at size
    omega
  obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected S remain cut
  have smaller (T : Finset V) (ht : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (ht.trans_eq size)
  obtain ⟨_,_,_,_,_,_,r,_,_,rs,_,debit⟩ := sides.low_cut_deficit hc smaller upper inside low
  rw [k25] at debit
  have degree : G.degree z=24 := by omega
  have minimum : G.minDegree=24 := by
    obtain ⟨w,hw⟩ := G.exists_minimal_degree_vertex
    by_cases same : z=w
    · rwa [←same,degree] at hw
    rcases degree_pair (G:=G) z w same with h|h
    · omega
    have := G.minDegree_le_degree z
    omega
  have lower := Graph189ArbitraryHalfExterior.critical_bondy_order bad point
    (by omega) (by omega) (by omega) (by omega)
  rw [five,minimum] at lower
  have ceiling := Graph189ThirdLayerDegreeCeiling.max_degree hc cap (by omega)
  rw [k25] at ceiling
  obtain ⟨ep,_,ore,wide,budget⟩ := Graph189ActualScalarWidth.bounds hc cap bad (by omega)
  rw [k25] at ep ore wide budget
  apply low_width (n:=(Fintype.card V : ℤ)) (e:=((G.maxDegree-25 : ℕ):ℤ))
    (w:=(Graph189RootWidth.width (Fintype.card V) 25 G.maxDegree : ℤ))
    (by omega) ep (by omega)
  · norm_num at ore ⊢; exact ore
  · norm_num at wide ⊢; exact wide
  · norm_num at budget ⊢; exact budget

/-- The original conjecture at every order for connectivity at least five
and second-smallest degree at least 25. -/
theorem traceable_ge25 (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 25≤G.secondSmallestDegree) (conn : 5≤G.vertexConnectivity) :
    ∃a b, ∃p : G.Walk a b,p.IsHamiltonian := by
  by_cases big : 26≤G.secondSmallestDegree
  · exact Graph189LargeDegree.traceable hc cap big conn
  have k25 : G.secondSmallestDegree=25 := by omega
  by_cases six : 6≤G.vertexConnectivity
  · exact Graph189HighConnectivityQuarter.traceable_six hc cap (by omega) (by omega) six
  have five : G.vertexConnectivity=5 := by omega
  by_contra bad
  have lifted := Graph189OnePortCover.additional_index_of_exclusion hc cap (by omega) (by omega)
    (fun S size cut z zin low => traceable_low hc cap k25 five S size cut zin low) bad
  rw [five,k25] at lifted
  obtain ⟨ep,em,_,width,budget⟩ := Graph189ActualScalarWidth.bounds hc cap bad (by omega)
  rw [k25] at ep em width budget
  exact Graph189SixIndexOrder.impossible (k:=25) (by decide) (by decide)
    (by omega : 7*((25:ℤ)-4)-1≤(Fintype.card V:ℤ)) ep em width budget

#print axioms traceable_ge25
end Graph189FiveConnectivity
