import Graph189SoleNearestData

open SimpleGraph Finset Graph189SoleNearestSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189DeepCommonPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

def Deep (G : SimpleGraph V) [DecidableRel G.Adj] (A S : Finset V) (x : V) : Prop :=
  x∈A ∧ G.secondSmallestDegree≤G.degree x ∧ ∀i∈S, ¬G.Adj i x

/-- Opposite high nonports attain distance exactly two at a common separator
vertex along their four-edge geodesic. -/
theorem nearest (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1) {x y : V} (left : Deep G A S x) (right : Deep G B S y) :
    ∃a∈S,G.dist a x=2 ∧ G.dist a y=2 ∧ G.dist x y=4 := by
  have bound := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=x) (v:=y)).trans
    (diameter_le_five hc (fun v => by simpa only [Nat.add_comm] using cap v))
  have five : G.dist x y≠5 := by
    intro eq
    rcases five_endpoints hc cap x y eq with h|h
    · exact (not_lt_of_ge left.2.1) h
    · exact (not_lt_of_ge right.2.1) h
  obtain ⟨p,len⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨a,sa,hit⟩ := sides.meets left.1 right.1 p
  have wt := congrArg Walk.length (Walk.take_spec p hit)
  rw [Walk.length_append] at wt
  have l := G.dist_le (p.takeUntil a hit)
  have r := G.dist_le (p.dropUntil a hit)
  rw [G.dist_comm (u:=x) (v:=a)] at l
  have left0 : G.dist a x≠0 := fun h => Finset.disjoint_left.mp sides.left_cut left.1 ((hc.dist_eq_zero_iff.mp h) ▸ sa)
  have right0 : G.dist a y≠0 := fun h => Finset.disjoint_left.mp sides.right_cut right.1 ((hc.dist_eq_zero_iff.mp h) ▸ sa)
  have left1 : G.dist a x≠1 := fun h => left.2.2 a sa (dist_eq_one_iff_adj.mp h)
  have right1 : G.dist a y≠1 := fun h => right.2.2 a sa (dist_eq_one_iff_adj.mp h)
  exact ⟨a,sa,by omega,by omega,by omega⟩

/-- A common port sees every opposite port at distance two. -/
theorem port_bound (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1) {p : V}
    (pa : p∈A) (hit : ∀i∈S,G.Adj p i) :
    (B.filter (fun v => ∃i∈S,G.Adj i v)).card≤G.secondSmallestDegree := by
  classical
  let T := B.filter (fun v => ∃i∈S,G.Adj i v)
  have out : p∉T := fun h => Finset.disjoint_left.mp sides.apart pa (mem_filter.mp h).1
  have bound := Graph189TwofoldCover.outside_quota cap T out
  rwa [filter_eq_self.mpr (by
    intro v hv
    obtain ⟨vb,i,si,iv⟩ := mem_filter.mp hv
    rw [Graph189PortDifference.cross_two hc sides pa vb (hit i si) iv]
    decide)] at bound

#print axioms nearest
#print axioms port_bound
end Graph189DeepCommonPair
