import Graph189IndependentExterior
import Graph189ConeNontrivial

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- The literal exterior of any longest path in a single-vertex deletion has a
cycle as soon as it omits at least three vertices and the half-degree budget
permits the requested length. All degree and parity data have ambient meaning. -/
theorem deletion_exterior_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (missing : 3 ≤ (univ.filter (fun v => v ∉ p.support)).card)
    (pos : 2 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {D d : ℕ} (deg : ∀ v : {u : V | u ≠ w}, D+1 ≤ G.degree v.val)
    (two : 2 ≤ d) (room : G.secondSmallestDegree + 2*d ≤ 2*D) :
    ∃ a, ∃ Q : ((G.induce {u : V | u ≠ w}).induce {v | v ∉ p.support.toFinset}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  classical
  let H := G.induce {u : V | u ≠ w}
  apply nontrivial_deletion_cycle w p hp longest _ cap deg two room
  by_contra! h
  have independent : ∀ a ∉ p.support, ∀ b ∉ p.support, ¬ H.Adj a b := by
    intro a ha b hb
    exact h a (fun t => ha (List.mem_toFinset.mp t)) b (fun t => hb (List.mem_toFinset.mp t))
  have small := independent_omits_at_most_two w p hp longest independent pos cap
  omega

/-- A longest cycle in the universal completion has a genuine exterior cycle.
The only geometric input outside this theorem is that every path of the
original graph omits at least four vertices. -/
theorem completeAt_exterior_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) {z : V} (c : (completeAt G w).Walk z z)
    (hc : c.IsCycle) (maximal : ∀ v (r : (completeAt G w).Walk v v), r.IsCycle → r.length ≤ c.length)
    (gap : ∀ a b, ∀ p : G.Walk a b, p.IsPath → p.support.length+3 < Fintype.card V)
    (pos : 2 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {D d : ℕ} (deg : ∀ v : {u : V | u ≠ w}, D+1 ≤ G.degree v.val)
    (two : 2 ≤ d) (room : G.secondSmallestDegree + 2*d ≤ 2*D) :
    ∃ a, ∃ Q : ((completeAt G w).induce {t : V | t ∉ c.support}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  classical
  let H := G.induce {u : V | u ≠ w}
  obtain ⟨u,v,p,hp,_,support,longest⟩ := longest_in_deletion G w c hc maximal
  obtain ⟨a,Q,hQ,len⟩ := deletion_exterior_cycle w p hp (fun r => longest _ _ r)
    (deletion_gap w p hp gap) pos cap deg two room
  let U := {t : {v : V | v ≠ w} | t ∉ p.support.toFinset}
  let W := {t : V | t ∉ c.support}
  let f : H.induce U →g (completeAt G w).induce W := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := by
    intro i j h
    have values : i.val.val=j.val.val := congrArg (fun z : W => z.val) h
    exact Subtype.ext (Subtype.ext values)
  exact ⟨f a,Q.map f,hQ.map inj,len.trans_eq (Walk.length_map f Q).symm⟩

#print axioms deletion_exterior_cycle
#print axioms deletion_gap
#print axioms completeAt_exterior_cycle
end Graph189ExteriorDegreeCycle
