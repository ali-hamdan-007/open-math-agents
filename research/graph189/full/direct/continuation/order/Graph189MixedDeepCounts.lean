import Graph189DeepPairData
import Graph189DirtySideOrder

open Finset SimpleGraph Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189MixedDeepCounts
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

private def ports (G : SimpleGraph V) [DecidableRel G.Adj] (X S : Finset V) :=
  X.filter (fun y => ∃i∈S,G.Adj i y)

private theorem nonports (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    {x : V} (deep : Deep G A S x) : (B\ports G B S).card+S.card≤G.secondSmallestDegree+1 := by
  classical
  let R := B\ports G B S
  let H := R.filter (fun v => G.secondSmallestDegree≤G.degree v)
  have support : Graph189PortLabels.support G S x=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨si,xi⟩ := mem_filter.mp hi
    exact deep.2.2 i si xi.symm
  have cover : H.filter (fun y => Even (G.dist x y))=H := filter_eq_self.mpr (by
    intro y hh
    obtain ⟨yr,hy⟩ := mem_filter.mp hh
    have low : Deep G B S y := ⟨(mem_sdiff.mp yr).1,hy,fun i si iy =>
      (mem_sdiff.mp yr).2 (mem_filter.mpr ⟨(mem_sdiff.mp yr).1,i,si,iy⟩)⟩
    obtain ⟨_,_,_,_,four⟩ := nearest hc sides cap deep low
    rw [four]; decide)
  have bd := Graph189BoundaryDebit.even_quota hc sides (fun T h =>
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (h.trans_le sc)) cap
    (show H⊆B from (filter_subset _ _).trans sdiff_subset) deep.1
  rw [cover,support,card_empty,Nat.add_zero] at bd
  have few : (R\H).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra diff
    exact (degree_pair (G:=G) u v diff).elim
      (fun high => (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,high⟩))
      (fun high => (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,high⟩))
  have pop := card_sdiff_add_card_eq_card (show H⊆R from filter_subset _ _)
  change R.card+S.card≤G.secondSmallestDegree+1
  omega

/-- A common port and a high nonport on the same side bound the whole
opposite component, including its possible exceptional vertex. -/
theorem opposite (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (sz : S.card=2) {y z : V} (deep : Deep G B S y) (zb : z∈B) (common : ∀i∈S,G.Adj z i) :
    A.card+1≤2*G.secondSmallestDegree := by
  classical
  have debit := nonports hc cap sides.swap sc deep
  rw [sz] at debit
  have quota := port_bound hc sides.swap cap zb common
  change (ports G A S).card≤G.secondSmallestDegree at quota
  have total := card_sdiff_add_card_eq_card (show ports G A S⊆A from filter_subset _ _)
  omega

/-- A common port and a high nonport in B, opposite a nonclean private
side A with a high nonport, force both sides into the marked path range.
The marked population is counted in the original graph at both sides. -/
theorem sizes (hc : G.Connected) (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (sides : Graph189CutSides.CutSides G A B S) (pair : S={p,q}) (ne : p≠q)
    (sc : S.card≤G.vertexConnectivity) (con : (G.induce (A:Set V)).Connected)
    (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) (dirty : ¬Graph189CleanSideCounts.Clean G A p q)
    {x y z : V} (deepA : Deep G A S x) (deepB : Deep G B S y)
    (zb : z∈B) (common : ∀i∈S,G.Adj z i)
    (long : 4*G.secondSmallestDegree≤Fintype.card V+5) :
    A.card+1≤2*G.secondSmallestDegree ∧ B.card+1≤2*G.secondSmallestDegree ∧
    G.secondSmallestDegree≤(A.filter (fun v => ∃i∈S,G.Adj i v)).card+5 ∧
    G.secondSmallestDegree≤(B.filter (fun v => ∃i∈S,G.Adj i v)).card+5 := by
  classical
  let k := G.secondSmallestDegree
  have sz : S.card=2 := by simp [pair,ne]
  have nA := nonports hc cap sides.swap sc deepB
  have nB := nonports hc cap sides sc deepA
  rw [sz] at nA nB
  have capA := port_bound hc sides.swap cap zb common
  change (ports G A S).card≤k at capA
  have boundB := Graph189DirtySideOrder.order hc cap sides pair ne sc con free dirty
  change B.card+1≤2*k at boundB
  have a := card_sdiff_add_card_eq_card (show ports G A S⊆A from filter_subset _ _)
  have b := card_sdiff_add_card_eq_card (show ports G B S⊆B from filter_subset _ _)
  have all : (univ : Finset V)⊆(A∪B)∪S := by
    intro v _
    rcases sides.cover v with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
  have total := (card_le_card all).trans (card_union_le _ _)
  rw [card_univ,sz] at total
  have ab := card_union_le A B
  change (A\ports G A S).card+2≤k+1 at nA
  change (B\ports G B S).card+2≤k+1 at nB
  change 4*k≤Fintype.card V+5 at long
  change A.card+1≤2*k ∧ B.card+1≤2*k ∧ k≤(ports G A S).card+5 ∧ k≤(ports G B S).card+5
  omega

#print axioms sizes
end Graph189MixedDeepCounts
