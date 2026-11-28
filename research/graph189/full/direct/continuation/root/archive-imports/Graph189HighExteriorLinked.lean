import Graph189NativeCycleLinked
import Graph189ExteriorPopulation

namespace Graph189HighExteriorLinked
open SimpleGraph Finset Graph189ExteriorDegreeCycle

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

/-- Dropping the at most one low vertex from the exterior costs at most one
neighbor. A high-high edge and the remaining degree give the linked cycle. -/
theorem high_cycle (p : G.Walk u v) (high : V → Prop)
    (pair : ∀ a b, a≠b → high a ∨ high b)
    (edge : ∃ a ∉ p.support, ∃ b ∉ p.support, high a ∧ high b ∧ G.Adj a b)
    {l : ℕ} (three : 3≤l)
    (large : ∀ a∉p.support, high a → ∀ b∉p.support, G.Adj a b →
        2*l-2 ≤ (G.neighborFinset a \ p.support.toFinset).card) :
    Graph189LinkedExterior.Linked (G.induce {a | a∉p.support.toFinset}) l := by
  classical
  let F := {a : V | a∉p.support.toFinset ∧ high a}
  let J := G.induce F
  obtain ⟨a,ao,b,bo,ha,hb,adj⟩ := edge
  have aF : a∈F := ⟨fun m => ao (List.mem_toFinset.mp m),ha⟩
  have bF : b∈F := ⟨fun m => bo (List.mem_toFinset.mp m),hb⟩
  have inside : ∃ x y, J.Adj x y := ⟨⟨a,aF⟩,⟨b,bF⟩,adj⟩
  have degree (x y : F) (xy : J.Adj x y) : 2*l-3 ≤ J.degree x := by
    let A := G.neighborFinset x.val \ p.support.toFinset
    let lost := A.filter (fun z => ¬high z)
    have bound : lost.card≤1 := Finset.card_le_one.mpr (by
      intro i hi j hj
      by_contra different
      exact (pair i j different).elim (mem_filter.mp hi).2 (mem_filter.mp hj).2)
    have ini := large x.val (fun m => x.property.1 (List.mem_toFinset.mpr m)) x.property.2
      y.val (fun m => y.property.1 (List.mem_toFinset.mpr m)) xy
    change 2*l-2≤A.card at ini
    have clean : (G.neighborFinset x.val).filter (fun z => z∈F) = A.filter high := by
      ext z
      simp [A,F,and_assoc]
    have d := degree_induce_filter (G:=G) F x
    change J.degree x = _ at d
    rw [clean] at d
    have parts := card_filter_add_card_filter_not (s:=A) (p:=high)
    change (A.filter high).card+lost.card=A.card at parts
    omega
  obtain ⟨x,C,hC,len⟩ := cycle_of_nonisolated_degree (G:=J) (d:=2*l-3) (by omega) inside degree
  have linked := Graph189NativeCycleLinked.of_cycle C hC (l:=l) (by omega) (by omega)
  let f : J →g G.induce {a | a∉p.support.toFinset} := {
    toFun := fun z => ⟨z.val,z.property.1⟩
    map_rel' := fun h => h }
  apply Graph189LinkedExterior.map f _ linked
  intro x y eq
  exact Subtype.ext (congrArg (fun z : {a : V | a∉p.support.toFinset} => z.val) eq)

/-- Two off-path neighbors guarantee that a high one can be chosen, because
globally at most one vertex fails the high-degree predicate. -/
theorem high_neighbor (p : G.Walk u v) (high : V→Prop)
    (pair : ∀ a b, a≠b → high a ∨ high b) (x : V)
    (two : 2≤(G.neighborFinset x \ p.support.toFinset).card) :
    ∃ y ∉ p.support, high y ∧ G.Adj x y := by
  classical
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1<(G.neighborFinset x \ p.support.toFinset).card by omega)
  have use (y : V) (h : y∈G.neighborFinset x \ p.support.toFinset) (good : high y) :
      ∃ y ∉ p.support, high y ∧ G.Adj x y := by
    obtain ⟨adj,off⟩ := mem_sdiff.mp h
    exact ⟨y,fun hh => off (List.mem_toFinset.mpr hh),good,(G.mem_neighborFinset _ _).mp adj⟩
  exact (pair a b ne).elim (use a ha) (use b hb)

#print axioms high_cycle
#print axioms high_neighbor
end Graph189HighExteriorLinked
