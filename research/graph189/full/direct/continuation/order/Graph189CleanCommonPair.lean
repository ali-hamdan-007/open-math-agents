import Graph189CommonContactDebit
import Graph189CleanPairOrder
import Graph189PrivateContactProfile
import Graph189OnePortThreeCut

open Finset SimpleGraph
namespace Graph189CleanCommonPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- In the mixed case of the separating-pair paper a common contact on B
sees every A-port at distance two. Combined with both clean counts, this
already places the graph below the graph-facing order floor when k≥11. -/
theorem of_eleven (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 11≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (clean : Graph189CleanSideCounts.Clean G A p q)
    {x : V} (xb : x∈B) (xp : G.Adj x p) (xq : G.Adj x q) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have size : S.card=2 := by simp [pair,ne]
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  apply Graph189OnePortCover.below_four hc cap (size ▸ sc) (by omega)
  by_cases big : 3*G.secondSmallestDegree+2<Fintype.card V
  swap
  · omega
  let R (W : Finset V) := (W.filter (fun y => G.dist p y≠1 ∧ G.dist q y≠1)).card
  let T := B.filter (fun y => G.dist p y=1 ∧ G.dist q y=1)
  let P := A.filter (fun y => G.Adj p y ∨ G.Adj q y)
  have combined := Graph189CleanPairOrder.nonport_order hc point sides pair ne sc big clean
  change Fintype.card V+R A+R B+T.card≤4*k+2 at combined
  have marked : 1≤T.card := card_pos.mpr ⟨x,mem_filter.mpr
    ⟨xb,dist_eq_one_iff_adj.mpr xp.symm,dist_eq_one_iff_adj.mpr xq.symm⟩⟩
  have ev : P.filter (fun y => Even (G.dist x y))=P := filter_eq_self.mpr (by
    intro y yes
    obtain ⟨ya,py|qy⟩ := mem_filter.mp yes
    · rw [Graph189PortDifference.cross_two hc sides.swap xb ya xp py]; decide
    · rw [Graph189PortDifference.cross_two hc sides.swap xb ya xq qy]; decide)
  have limit := Graph189TwofoldCover.outside_quota point P (u:=x) (fun m =>
    Finset.disjoint_left.mp sides.apart (mem_filter.mp m).1 xb)
  rw [ev] at limit
  have pop := card_filter_add_card_filter_not (s:=A) (p:=fun y => G.Adj p y ∨ G.Adj q y)
  have eq : A.filter (fun y => ¬(G.Adj p y ∨ G.Adj q y))=
      A.filter (fun y => G.dist p y≠1 ∧ G.dist q y≠1) := by
    ext y
    simp only [mem_filter,ne_eq,dist_eq_one_iff_adj,not_or]
  change P.card+_=A.card at pop
  rw [eq] at pop
  change P.card+R A=A.card at pop
  have opp := Graph189PrivateContactProfile.order_of_common hc sides.swap pair ne sc point clean.private_ports
    ⟨x,xb,fun i hi => by
      rcases (show i=p ∨ i=q by simpa [pair] using hi) with rfl|rfl
      · exact xp
      · exact xq⟩
  change B.card+3≤2*k+R B at opp
  have all : (univ : Finset V)⊆(A∪B)∪S := by
    intro y _
    rcases sides.cover y with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
  have total := (card_le_card all).trans (card_union_le _ _)
  rw [card_univ,size] at total
  have ab := card_union_le A B
  change P.card≤k at limit
  change 11≤k at large
  change Fintype.card V+5<4*k
  omega

theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (clean : Graph189CleanSideCounts.Clean G A p q)
    {x : V} (xb : x∈B) (xp : G.Adj x p) (xq : G.Adj x q) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian :=
  of_eleven hc cap (by omega) sides pair ne sc clean xb xp xq

#print axioms of_eleven
#print axioms traceable
end Graph189CleanCommonPair
