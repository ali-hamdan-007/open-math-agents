import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card

namespace Graph189CutSides
open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The first edge of a walk that leaves a specified set. -/
theorem walk_exits (P : V → Prop) {x y : V} (p : G.Walk x y) (hx : P x) (hy : ¬ P y) :
    ∃ u v, P u ∧ ¬ P v ∧ G.Adj u v ∧ v ∈ p.support := by
  classical
  induction p with
  | nil => exact (hy hx).elim
  | @cons x t y e p ih =>
    by_cases ht : P t
    · obtain ⟨u,v,hu,hv,huv,hm⟩ := ih ht hy
      exact ⟨u,v,hu,hv,huv, List.mem_cons_of_mem _ hm⟩
    · exact ⟨x,t,hx,ht,e, List.mem_cons_of_mem _ p.start_mem_support⟩

/-- Two nonempty, anticomplete sides of a vertex separator. Each side can be
a union of components of the graph after deletion. -/
structure CutSides (G : SimpleGraph V) (A B S : Finset V) : Prop where
  left_nonempty : A.Nonempty
  right_nonempty : B.Nonempty
  apart : Disjoint A B
  left_cut : Disjoint A S
  right_cut : Disjoint B S
  cover : ∀ u, u ∈ A ∨ u ∈ B ∨ u ∈ S
  no_cross : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v

namespace CutSides
variable {A B S : Finset V} (sides : CutSides G A B S)
include sides

theorem swap : CutSides G B A S where
  left_nonempty := sides.right_nonempty
  right_nonempty := sides.left_nonempty
  apart := sides.apart.symm
  left_cut := sides.right_cut
  right_cut := sides.left_cut
  cover u := by rcases sides.cover u with h | h | h <;> tauto
  no_cross v hv u hu h := sides.no_cross u hu v hv h.symm

/-- Every walk between the sides has a separator vertex on its support. -/
theorem meets {x y : V} (hx : x ∈ A) (hy : y ∈ B) (p : G.Walk x y) :
    ∃ i ∈ S, i ∈ p.support := by
  obtain ⟨u,v,hu,hv,huv,hm⟩ :=
    walk_exits (· ∈ A) p hx (fun ha => disjoint_left.mp sides.apart ha hy)
  rcases sides.cover v with h | h | h
  · exact (hv h).elim
  · exact (sides.no_cross u hu v h huv).elim
  · exact ⟨v,h,hm⟩

variable [DecidableEq V]

/-- Restoring one separator vertex reconnects the two sides only when that
vertex has a genuine neighbor in the left side. -/
theorem contact {i : V}
    (restore : (G.induce {u : V | u ∉ S.erase i}).Connected) :
    ∃ a ∈ A, G.Adj a i := by
  classical
  obtain ⟨x,hx⟩ := sides.left_nonempty
  obtain ⟨y,hy⟩ := sides.right_nonempty
  let T : Set V := {u : V | u ∉ S.erase i}
  have hxt : x ∈ T := fun h => disjoint_left.mp sides.left_cut hx (mem_erase.mp h).2
  have hyt : y ∈ T := fun h => disjoint_left.mp sides.right_cut hy (mem_erase.mp h).2
  obtain ⟨p⟩ := restore (⟨x,hxt⟩ : T) (⟨y,hyt⟩ : T)
  obtain ⟨u,v,hu,hv,edge,_⟩ := walk_exits (G := G.induce T) (fun t : T => t.val ∈ A)
    p hx (fun h => disjoint_left.mp sides.apart h hy)
  have adj : G.Adj u.val v.val := edge
  rcases sides.cover v.val with h | h | h
  · exact (hv h).elim
  · exact (sides.no_cross u.val hu v.val h adj).elim
  · have eq : v.val = i := by
      by_contra ne
      exact v.property (mem_erase.mpr ⟨ne,h⟩)
    exact ⟨u.val,hu,eq ▸ adj⟩

/-- Minimum-cardinality vertex deletion gives genuine contacts on both sides
at every member of the separator. -/
theorem contacts_of_minimum
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    {i : V} (hi : i ∈ S) :
    (∃ a ∈ A, G.Adj a i) ∧ (∃ b ∈ B, G.Adj b i) := by
  have h := smaller (S.erase i) (card_erase_lt_of_mem hi)
  exact ⟨sides.contact h, sides.swap.contact h⟩

end CutSides
#print axioms CutSides.meets
#print axioms CutSides.contacts_of_minimum
end Graph189CutSides
