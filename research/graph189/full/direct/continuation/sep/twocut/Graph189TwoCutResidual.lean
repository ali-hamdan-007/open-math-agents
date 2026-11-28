import Graph189TwoCutSelectJoint
import Graph189TwoCutOnePrivateFinal
import Graph189AllIndexThree
import Graph189EdgeOrder
import Graph189TwoAnchorSeparation

namespace Graph189TwoCutResidual
open Finset SimpleGraph Graph189CutSides Graph189PositiveEvenCut
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem triangles (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (large : 3*G.secondSmallestDegree+2<Fintype.card V) :
    ∀ x y, G.Adj x y → ∃ t, G.Adj x t ∧ G.Adj y t := by
  classical
  have cap' (v : V) : G.distEven v≤G.secondSmallestDegree+1 :=
    by simpa only [Nat.add_comm 1] using cap v
  have oriented (x y : V) (xy : G.Adj x y) (high : G.secondSmallestDegree≤G.degree y) :
      ∃ t, G.Adj x t ∧ G.Adj y t := by
    by_contra! none
    have empty : G.neighborFinset x∩G.neighborFinset y=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨xw,yw⟩ := mem_inter.mp hw
      exact none w ((G.mem_neighborFinset _ _).mp xw) ((G.mem_neighborFinset _ _).mp yw)
    have bound := Graph189EdgeOrder.edge_order hc xy cap'
    rw [empty,card_empty] at bound
    have h := Nat.mul_le_mul_left G.secondSmallestDegree
      (show G.secondSmallestDegree+1+0-G.degree y≤1 by omega)
    omega
  intro x y xy
  obtain h|h := degree_pair (G:=G) x y xy.ne
  · obtain ⟨t,yt,xt⟩ := oriented y x xy.symm h
    exact ⟨t,xt,yt⟩
  · exact oriented x y xy h

/-- At k≥9, every genuine connectivity-two counterexample has a minimum
cut in one of the three routing cases. The missing-private case is discharged
by the recut theorem through its early contact-count branches. -/
theorem routing_cases (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (large : 9≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (connectivity : G.vertexConnectivity=2)
    (notTrace : ¬∃ a b, ∃ P : G.Walk a b,P.IsHamiltonian) :
    ∃ A B : Finset V, ∃ p q : V, p≠q ∧ CutSides G A B {p,q} ∧
      (G.induce (A:Set V)).Connected ∧ (G.induce (B:Set V)).Connected ∧
      2≤A.card ∧ 2≤B.card ∧ A.card≤B.card ∧
      (∀ C D T, CutSides G C D T → T.card=2 → A.card≤C.card) ∧
      (B.card<2*G.secondSmallestDegree ∨
        (2*G.secondSmallestDegree≤B.card ∧
          ((¬∃ x∈A, G.Adj x p ∧ G.Adj x q) ∨
            ((∃ x∈A, G.Adj x p ∧ G.Adj x q) ∧
              (∀ x∈A, G.secondSmallestDegree≤G.degree x → G.Adj x p ∨ G.Adj x q) ∧
              (∃ x∈A, G.Adj x p ∧ ¬G.Adj x q) ∧
              (∃ x∈A, G.Adj x q ∧ ¬G.Adj x p))))) := by
  classical
  have cap' (v : V) : G.distEven v≤G.secondSmallestDegree+1 :=
    by simpa only [Nat.add_comm 1] using cap v
  have order := Graph189TightTwoCut.index_three hc (by omega) cap' notTrace (by omega) minimum
  have triangle := triangles hc cap (by omega)
  obtain ⟨A,B,p,q,dpq,sides,connA,connB,aSize,bSize,least⟩ :=
    Graph189TwoCutSelect.exists_connected_least_cut (G:=G) connectivity (by omega) minimum (by omega) cap'
  have small (T : Finset V) (lt : T.card<2) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq connectivity.symm)
  have ab := least B A {p,q} sides.swap (by simp [dpq])
  refine ⟨A,B,p,q,dpq,sides,connA,connB,aSize,bSize,ab,least,?_⟩
  by_cases balanced : B.card<2*G.secondSmallestDegree
  · exact Or.inl balanced
  have big : 2*G.secondSmallestDegree≤B.card := by omega
  apply Or.inr
  refine ⟨big,?_⟩
  by_cases common : ∃ x∈A, G.Adj x p ∧ G.Adj x q
  · apply Or.inr
    have shallow (x : V) (xa : x∈A) (high : G.secondSmallestDegree≤G.degree x) :
        G.Adj x p ∨ G.Adj x q := by
      by_contra! no
      have deep : ∀ i∈({p,q}:Finset V), ¬G.Adj x i := by
        intro i hi
        rcases (show i=p ∨ i=q by simpa using hi) with rfl|rfl
        · exact no.1
        · exact no.2
      exact (large_pair_nonport hc cap dpq sides small (by omega) big xa high deep).2 common
    refine ⟨common,shallow,?_,?_⟩
    · by_contra! missing
      have swapped : CutSides G A B {q,p} := by simpa only [Finset.pair_comm] using sides
      exact Graph189TwoCutOnePrivate.excluded hc cap swapped dpq.symm small connB triangle
        large minimum aSize order (fun x hx high => (shallow x hx high).symm) missing least
    · by_contra! missing
      exact Graph189TwoCutOnePrivate.excluded hc cap sides dpq small connB triangle
        large minimum aSize order shallow missing least
  · exact Or.inl common

#print axioms routing_cases
end Graph189TwoCutResidual
