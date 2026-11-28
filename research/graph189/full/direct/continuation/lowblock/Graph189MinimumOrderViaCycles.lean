import Graph189CriticalOrderViaCycles
import Graph189MinimumDeletionSharp

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- If H=G−w is nontraceable and w is a minimum vertex, every longest cycle
of the universal completion leaves an actual cycle of order at least ceil(k/2).
The theorem also allows original minimum degree one or two. -/
theorem minimum_completion_half_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (minw : G.degree w=G.minDegree)
    {v : V} (C : (completeAt G w).Walk v v) (hc : C.IsCycle)
    (longest : ∀ a (R : (completeAt G w).Walk a a), R.IsCycle → R.length ≤ C.length)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : 5 ≤ G.secondSmallestDegree) :
    ∃ a, ∃ Q : ((completeAt G w).induce {t : V | t ∉ C.support}).Walk a a,
      Q.IsCycle ∧ (G.secondSmallestDegree+1)/2 ≤ Q.length := by
  classical
  let H := G.induce {u : V | u ≠ w}
  obtain ⟨u,v,p,hp,_,support,maxp⟩ := longest_in_deletion G w C hc longest
  obtain ⟨a,Q,hQ,len⟩ := minimum_deletion_half_cycle w minw p hp (fun r => maxp _ _ r) notTrace notH cap k5
  let U := {t : {v : V | v ≠ w} | t ∉ p.support.toFinset}
  let W := {t : V | t ∉ C.support}
  let f : H.induce U →g (completeAt G w).induce W := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := by
    intro i j h
    have values : i.val.val=j.val.val := congrArg (fun z : W => z.val) h
    exact Subtype.ext (Subtype.ext values)
  exact ⟨f a,Q.map f,hQ.map inj,len.trans_eq (Walk.length_map f Q).symm⟩

/-- Both the original connectivity and its optional one-unit lift at a minimum
vertex fit the same order theorem. The only remaining geometric hypothesis is
the cited longest-cycle exclusion, once nontraceability of the deletion is known. -/
theorem minimum_order_of_cycle_exclusion {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (minw : G.degree w=G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : 5 ≤ G.secondSmallestDegree)
    {l : ℕ} (conn : l ≤ (completeAt G w).vertexConnectivity) (length : l ≤ (G.secondSmallestDegree+1)/2)
    (cycle : exteriorCycleExclusion (completeAt G w) l) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V := by
  classical
  let K := completeAt G w
  have minimum := secondDegree_le_completeAt_minDegree (G:=G) w minw
  change G.secondSmallestDegree ≤ K.minDegree at minimum
  have two (v : V) : 2 ≤ K.degree v := by
    have := K.minDegree_le_degree v
    omega
  obtain ⟨z,C,hC,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,P,hP,maximal⟩ := exists_longest_cycle K ⟨z,C,hC⟩
  obtain ⟨b,Q,hQ,sz⟩ := minimum_completion_half_cycle w minw P hP maximal notTrace notH cap k5
  by_contra! fail
  have upper : Fintype.card V+2 ≤ (l+1)*(K.minDegree-l+2) := by
    have step : G.secondSmallestDegree-l+2 ≤ K.minDegree-l+2 := by omega
    have := Nat.mul_le_mul_left (l+1) step
    omega
  have small := cycle conn upper a P hP maximal b Q hQ
  omega

#print axioms minimum_completion_half_cycle
#print axioms minimum_order_of_cycle_exclusion
end Graph189ExteriorDegreeCycle
