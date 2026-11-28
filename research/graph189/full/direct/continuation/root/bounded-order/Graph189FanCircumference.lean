import Graph189FanCases
import Graph189FanInduce
import Graph189FanSeparated

open SimpleGraph Finset
namespace Graph189FanCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A two-connected simple graph has a cycle of order at least `min(n,2q)`
if all vertices except possibly `z` have degree at least `q`. -/
theorem one_exception_cycle (two : G.IsKConnected 2) (z : V) (q : ℕ)
    (degree : ∀ v, v≠z → q≤G.degree v) :
    ∃ a, ∃ C : G.Walk a a, C.IsCycle ∧ min (Fintype.card V) (2*q) ≤ C.length := by
  classical
  let d := max 2 q
  have dq : q≤d := le_max_right _ _
  have dt : 2≤d := le_max_left _ _
  have every (v : V) := degree_two_of_connected two v
  have high (v : V) (vz : v≠z) : d≤G.degree v := max_le (every v) (degree v vz)
  have connected : G.Connected := by
    apply G.induceUnivIso.connected_iff.mp
    have h := two.2 (∅ : Finset V) (by simp)
    change (G.induce ((↑(∅ : Finset V) : Set V)ᶜ)).Connected at h
    rwa [coe_empty,Set.compl_empty] at h
  rcases cycle_or_regions z dt (every z) connected.preconnected high with ⟨a,C,hC,len⟩|⟨x,y,dx,dy,⟨D⟩⟩
  · exact ⟨a,C,hC,(min_le_min_left _ (Nat.mul_le_mul_left 2 dq)).trans len⟩
  obtain ⟨a,C,hC,len⟩ := separated_routes two D.L D.R D.M D.leftNodup D.leftChain D.leftHead D.leftLast
    D.leftEdge D.leftNeighbors D.rightNodup D.rightChain D.rightHead D.rightLast D.rightEdge
    D.rightNeighbors D.middle D.middleHead D.middleLast D.meet (by omega)
  exact ⟨a,C,hC,(min_le_right _ _).trans (by omega)⟩

/-- The exact strictly-larger induced-subgraph circumference input of the
three-connected Graph 189 assembly, including thresholds zero and one. -/
theorem induced_long_cycles (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (z : V)
    (zs : z∈S) (q : ℕ) (three : 3≤S.card) (large : 2*q<S.card)
    (noncut : ∀ u∈S, (G.induce (S.erase u : Set V)).Preconnected)
    (deg : ∀ u∈S, u≠z → q≤(G.neighborFinset u∩S).card) :
    ∃ a, ∃ C : G.Walk a a, C.IsCycle ∧ (∀ v∈C.support, v∈S) ∧ 2*q≤C.length := by
  classical
  let H := G.induce (S : Set V)
  let Z : S := ⟨z,zs⟩
  have high (v : S) (vz : v≠Z) : q≤H.degree v := by
    rw [internal_degree S v]; exact deg v.val v.property (fun eq => vz (Subtype.ext eq))
  obtain ⟨a,C,hC,len⟩ := one_exception_cycle (induced_two_connected S three noncut) Z q high
  change min (Fintype.card S) (2*q) ≤ C.length at len
  rw [Fintype.card_coe,min_eq_right large.le] at len
  let f := (Embedding.induce (G:=G) (S:Set V)).toHom
  refine ⟨f a,C.map f,hC.map Subtype.val_injective,?_,len.trans_eq (Walk.length_map f C).symm⟩
  intro v hv
  rw [Walk.support_map f C] at hv
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
  exact u.property

end Graph189FanCycle
#print axioms Graph189FanCycle.one_exception_cycle
#print axioms Graph189FanCycle.induced_long_cycles
