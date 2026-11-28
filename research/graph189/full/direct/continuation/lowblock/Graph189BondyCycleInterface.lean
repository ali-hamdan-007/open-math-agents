import Graph189MinimumOrderViaCycles
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Graph189ExteriorDegreeCycle
open SimpleGraph

/-- The graph-specific specialization of the large-order Bondy theorem supplies
the cycle-exclusion interface consumed by both checked order reductions. The
displayed supremum is the pinned definition of circumference, unfolded so no
placeholder-bearing conjecture file is imported. -/
theorem cycle_exclusion_of_large_bondy {V : Type*} [Fintype V] [Nontrivial V]
    [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] {l : ℕ} (positive : 1≤l)
    (large : 5*l^2+7*l ≤ Fintype.card V) (min : l≤K.minDegree)
    (bondy : 5*l^2+7*l ≤ Fintype.card V → IsKConnected K l →
      ((Fintype.card V : ℝ)+(l:ℝ)*(l-1))/(l+1) ≤ K.minDegree →
      ∀ a, ∀ C : K.Walk a a, C.IsCycle →
        C.length = sSup {m : ℕ | ∃ b, ∃ q : K.Walk b b, q.IsCycle ∧ q.length=m} →
        ∀ x y, ∀ p : (K.induce {v : V | v ∉ C.support}).Walk x y, p.IsPath →
          p.support.length+1≤l) :
    exteriorCycleExclusion K l := by
  intro connectivity order a C hC longest
  have connected : IsKConnected K l := by
    refine ⟨by nlinarith,?_⟩
    intro T small
    exact Graph189CutSides.connected_after_smaller_deletion T (small.trans_le connectivity)
  have degreeNat : Fintype.card V+l*(l-1)≤(l+1)*K.minDegree := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le min
    rw [hd,Nat.add_sub_cancel_left] at order
    rw [hd]
    obtain ⟨h,hl⟩ := Nat.exists_eq_add_of_le positive
    rw [hl,Nat.add_sub_cancel_left]
    rw [hl] at order
    nlinarith
  have degreeReal : ((Fintype.card V : ℝ)+(l:ℝ)*(l-1))/(l+1) ≤ K.minDegree := by
    apply (div_le_iff₀ (by positivity)).mpr
    have realBound : ((Fintype.card V+l*(l-1) : ℕ) : ℝ) ≤ (((l+1)*K.minDegree : ℕ) : ℝ) := by
      exact_mod_cast degreeNat
    push_cast [Nat.cast_sub positive] at realBound
    nlinarith
  let L : Set ℕ := {m | ∃ b, ∃ q : K.Walk b b, q.IsCycle ∧ q.length=m}
  have mem : C.length∈L := ⟨a,C,hC,rfl⟩
  have upper : ∀ m∈L, m≤C.length := by
    rintro m ⟨b,q,hq,rfl⟩
    exact longest b q hq
  have max : C.length=sSup L := (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  intro b Q hQ
  obtain ⟨path,sz⟩ := path_of_exterior_cycle Q hQ
  have small := bondy large connected degreeReal a C hC max _ _ Q.dropLast path
  omega

#print axioms cycle_exclusion_of_large_bondy
end Graph189ExteriorDegreeCycle
