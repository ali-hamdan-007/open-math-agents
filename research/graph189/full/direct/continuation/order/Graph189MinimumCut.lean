import Graph189CutSides
import Graph189CrossOrder
import Graph189HighPredecessor
import Graph189R1Metric

namespace Graph189CutSides
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- Deleting S, when at least one vertex survives, gives genuine anticomplete
sides whenever the surviving induced graph is disconnected. -/
theorem exists_cutSides_of_disconnected (S : Finset V) (survives : ∃ u, u ∉ S)
    (disc : ¬(G.induce {u : V | u ∉ S}).Connected) :
    ∃ A B, CutSides G A B S := by
  classical
  let T : Set V := {u : V | u ∉ S}
  let H := G.induce T
  obtain ⟨x,hx⟩ := survives
  let a : T := ⟨x,hx⟩
  have disconnected : ¬ H.Connected := disc
  obtain ⟨b,hb⟩ : ∃ b : T, ¬H.Reachable a b := by
    by_contra! hh
    exact disconnected ((H.connected_iff_exists_forall_reachable).mpr ⟨a,hh⟩)
  let P (v : V) := ∃ hv : v ∈ T, H.Reachable a ⟨v,hv⟩
  let A := univ.filter P
  let B := univ.filter (fun v => v ∈ T ∧ ¬P v)
  refine ⟨A,B,?_⟩
  refine ⟨⟨x,mem_filter.mpr ⟨mem_univ _,hx,Reachable.refl a⟩⟩,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨b.val,mem_filter.mpr ⟨mem_univ _,b.property,fun ⟨_,h⟩ => hb h⟩⟩
  · exact disjoint_left.mpr fun _ ha h => (mem_filter.mp h).2.2 (mem_filter.mp ha).2
  ·
    apply Finset.disjoint_left.mpr
    intro v hv hs
    exact ((mem_filter.mp hv).2.choose : v ∈ T) hs
  · exact disjoint_left.mpr fun _ hv hs => (mem_filter.mp hv).2.1 hs
  · intro v
    by_cases hs : v ∈ S
    · exact Or.inr (Or.inr hs)
    by_cases hp : P v
    · exact Or.inl (mem_filter.mpr ⟨mem_univ _,hp⟩)
    · exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ _,hs,hp⟩))
  · intro u hu v hv edge
    obtain ⟨hut,reach⟩ := (mem_filter.mp hu).2
    obtain ⟨hvt,notP⟩ := (mem_filter.mp hv).2
    have e : H.Adj ⟨u,hut⟩ ⟨v,hvt⟩ := edge
    exact notP ⟨hvt,reach.trans e.reachable⟩

namespace CutSides
variable {A B S : Finset V} (sides : CutSides G A B S)
include sides
variable [Nontrivial V] [DecidableRel G.Adj]

/-- High-population product bound for a genuine minimum separator under
the original Graph 189 hypothesis. -/
theorem high_product (hc : G.Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) :
    (A.filter (fun x => G.secondSmallestDegree ≤ G.degree x)).card *
      (B.filter (fun x => G.secondSmallestDegree ≤ G.degree x)).card ≤
    (A.filter (fun x => G.secondSmallestDegree ≤ G.degree x)).card * G.secondSmallestDegree +
      S.card * (G.secondSmallestDegree * G.secondSmallestDegree) := by
  classical
  let H (v : V) := G.secondSmallestDegree ≤ G.degree v
  let X := A.filter H
  let Y := B.filter H
  have left : X ⊆ A := filter_subset _ _
  have right : Y ⊆ B := filter_subset _ _
  have cap' (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm 1] using cap v
  apply Graph189CrossPort.cut_product hc X Y S (sides.apart.mono left right)
    (sides.left_cut.mono_left left) (sides.right_cut.mono_left right) _ _ _ _ _ cap'
  · intro x hx y hy
    have upper := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := x) (v := y)).trans
      (diameter_le_five hc cap)
    have notfive : G.dist x y ≠ 5 := by
      intro d
      rcases five_endpoints hc cap' x y d with h | h
      · exact (not_lt_of_ge (mem_filter.mp hx).2) h
      · exact (not_lt_of_ge (mem_filter.mp hy).2) h
    omega
  · exact fun _ hx _ hy p => sides.meets (left hx) (right hy) p
  · intro i hi
    obtain ⟨b,hb,e⟩ := (sides.contacts_of_minimum smaller hi).2
    exact ⟨b,e,fun h => disjoint_left.mp sides.apart (left h) hb,
      fun x hx ex => sides.no_cross x (left hx) b hb ex.symm⟩
  · intro i hi
    obtain ⟨a,ha,e⟩ := (sides.contacts_of_minimum smaller hi).1
    exact ⟨a,e,fun h => disjoint_left.mp sides.apart ha (right h),
      fun y hy => sides.no_cross a ha y (right hy)⟩

/-- Even a subthreshold vertex of a minimum cut has degree at least k+1−|S|. -/
theorem anchor_degree
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) {z : V} (hz : z ∈ S) :
    G.secondSmallestDegree + 1 ≤ G.degree z + S.card := by
  classical
  have spos : 0 < S.card := card_pos.mpr ⟨z,hz⟩
  by_cases high : G.secondSmallestDegree ≤ G.degree z
  · omega
  obtain ⟨⟨a,ha,az⟩,⟨b,hb,bz⟩⟩ := sides.contacts_of_minimum smaller hz
  have ah := (degree_pair (G := G) a z az.ne).resolve_right high
  have bh := (degree_pair (G := G) b z bz.ne).resolve_right high
  have neq : a ≠ b := fun e => disjoint_left.mp sides.apart (e ▸ ha) hb
  have cap' : G.distEven z ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm 1] using cap z
  have width := Graph189HighPredecessor.common_lower neq (sides.no_cross _ ha _ hb) az.symm bz.symm cap'
  have overlap : G.neighborFinset a ∩ G.neighborFinset b ⊆ S := by
    intro v hv
    obtain ⟨av,bv⟩ := mem_inter.mp hv
    rcases sides.cover v with h | h | hs
    · exact (sides.no_cross v h b hb ((G.mem_neighborFinset _ _).mp bv).symm).elim
    · exact (sides.no_cross a ha v h ((G.mem_neighborFinset _ _).mp av)).elim
    · exact hs
  have bound := card_le_card overlap
  omega

end CutSides
#print axioms exists_cutSides_of_disconnected
#print axioms CutSides.high_product
#print axioms CutSides.anchor_degree
end Graph189CutSides
