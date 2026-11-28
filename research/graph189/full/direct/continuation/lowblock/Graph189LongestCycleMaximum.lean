import Graph189UniversalCycle

namespace Graph189ExteriorDegreeCycle
open SimpleGraph

theorem exists_longest_cycle {V : Type*} [Fintype V] (K : SimpleGraph V)
    (has : ∃ a, ∃ C : K.Walk a a, C.IsCycle) :
    ∃ a, ∃ C : K.Walk a a, C.IsCycle ∧ ∀ b (Q : K.Walk b b), Q.IsCycle → Q.length ≤ C.length := by
  classical
  have bounded {b} (Q : K.Walk b b) (hQ : Q.IsCycle) : Q.length ≤ Fintype.card V := by
    have h := hQ.support_nodup.length_le_card
    rw [List.length_tail,Q.length_support] at h
    omega
  let Good (m : ℕ) := ∃ a, ∃ C : K.Walk a a, C.IsCycle ∧ C.length=m
  obtain ⟨b,Q,hQ⟩ := has
  have init : Good Q.length := ⟨b,Q,hQ,rfl⟩
  obtain ⟨a,C,hC,sz⟩ := Nat.findGreatest_spec (bounded Q hQ) init
  refine ⟨a,C,hC,?_⟩
  intro u p hp
  rw [sz]
  exact Nat.le_findGreatest (bounded p hp) (show Good p.length from ⟨u,p,hp,rfl⟩)

#print axioms exists_longest_cycle
end Graph189ExteriorDegreeCycle
