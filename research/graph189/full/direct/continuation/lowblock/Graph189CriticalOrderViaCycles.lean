import Graph189CriticalExterior
import Graph189LongestCycleMaximum
import Graph189CriticalConnectivity

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Graph189UniversalCycle

/-- The standard longest-cycle exclusion invoked at the cone. Its graph
argument is explicit so either independent paper theorem can supply it. -/
def exteriorCycleExclusion {V : Type*} [Fintype V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (l : ℕ) : Prop :=
  l ≤ K.vertexConnectivity → Fintype.card V+2 ≤ (l+1)*(K.minDegree-l+2) →
  ∀ a, ∀ C : K.Walk a a, C.IsCycle → (∀ b (Q : K.Walk b b), Q.IsCycle → Q.length ≤ C.length) →
  ∀ b, ∀ Q : (K.induce {v : V | v ∉ C.support}).Walk b b, Q.IsCycle → Q.length < l

/-- For the unrestricted critical removal, the only remaining input to the
lower order bound is the cited cycle-exclusion theorem, stated at genuine
graphs. The minimum separator and low vertex are unrestricted. -/
theorem critical_order_of_cycle_exclusion {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (s2 : 2 ≤ G.vertexConnectivity) (room : G.vertexConnectivity < Fintype.card V-1)
    (critical : 3*G.vertexConnectivity < 2*(G.minDegree+1))
    (enough : G.secondSmallestDegree+2*G.vertexConnectivity+2 ≤ 2*G.minDegree)
    (cycle : ∀ w, exteriorCycleExclusion (completeAt G w) (G.vertexConnectivity+1)) :
    (G.vertexConnectivity+2)*(G.minDegree-(G.vertexConnectivity+1)+2)-1 ≤ Fintype.card V := by
  classical
  obtain ⟨w,conn⟩ := Graph189CriticalConnectivity.exists_completion room critical
  let K := completeAt G w
  have minimum := minDegree_le_completeAt (G:=G) w
  have two (v : V) : 2 ≤ K.degree v := by
    have := K.minDegree_le_degree v
    change G.minDegree ≤ K.minDegree at minimum
    omega
  obtain ⟨z,C,hC,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,P,hP,longest⟩ := exists_longest_cycle K ⟨z,C,hC⟩
  obtain ⟨b,Q,hQ,len⟩ := arbitrary_completion_exterior w P hP longest notTrace k5 cap s2 enough
  by_contra! fail
  have upper : Fintype.card V + 2 ≤ (G.vertexConnectivity+1+1)*(K.minDegree-(G.vertexConnectivity+1)+2) := by
    have step : G.minDegree-(G.vertexConnectivity+1)+2 ≤ K.minDegree-(G.vertexConnectivity+1)+2 := by
      change G.minDegree ≤ K.minDegree at minimum
      omega
    have prod := Nat.mul_le_mul_left (G.vertexConnectivity+2) step
    change _ ≤ (G.vertexConnectivity+2)*_
    omega
  have tooShort := cycle w conn upper a P hP longest b Q hQ
  omega

#print axioms exists_longest_cycle
#print axioms critical_order_of_cycle_exclusion
end Graph189ExteriorDegreeCycle
