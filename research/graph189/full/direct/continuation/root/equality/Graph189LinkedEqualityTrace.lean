import Graph189OpenEqualityPath
import Graph189MinimumCutOrder

open SimpleGraph Finset Graph189UniversalCycle OMA.BondyK
namespace Graph189BondyEquality
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At equality in the linked-set order bound for a universal completion, its
longest cycle and linked exterior give a Hamiltonian path in the original
graph at any admissible index. -/
theorem traceable_of_linked_equality (w : V) {k d : ℕ} (two : 2≤k) (kd : k≤d)
    (high : ∀ v, v≠w → d≤G.degree v) (min : d≤(completeAt G w).minDegree)
    (conn : k≤(completeAt G w).vertexConnectivity)
    (order : Fintype.card V=(k+1)*(d-k+2)-1)
    {a : V} (C : (completeAt G w).Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (Q : (completeAt G w).Walk b b), Q.IsCycle → Q.length≤C.length)
    (linked : Graph189LinkedExterior.Linked ((completeAt G w).induce (offWalk C)) k) :
    ∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  obtain ⟨H,s,data⟩ := equality_layout_of_linked (by omega) kd min order
    (fun S small => Graph189CutSides.connected_after_smaller_deletion S (small.trans_le conn))
    C hC longest linked
  let L : Set ℕ := {m | ∃ u, ∃ q : (completeAt G w).Walk u u, q.IsCycle ∧ q.length=m}
  have mem : C.length∈L := ⟨a,C,hC,rfl⟩
  have upper : ∀ m∈L, m≤C.length := by rintro _ ⟨u,q,hq,rfl⟩; exact longest u q hq
  have circ : C.length=(completeAt G w).circumference :=
    (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  have hD := cy_of C hC circ
  have census := cycle_covers_with_exterior hD data two kd order
  have room : d+2≤Fintype.card V := by
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le kd
    rw [he,Nat.add_sub_cancel_left] at order
    rw [he]
    have positive : 1≤(k+1)*(e+2) := Nat.mul_pos (by omega) (by omega)
    have n : Fintype.card V+1=(k+1)*(e+2) := by omega
    nlinarith
  exact traceable_of_equality_census w hD data high kd room census

#print axioms traceable_of_linked_equality
end Graph189BondyEquality
