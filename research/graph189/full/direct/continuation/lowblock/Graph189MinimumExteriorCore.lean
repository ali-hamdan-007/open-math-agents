import Graph189ExteriorCore
import Graph189MinimumDeletionExterior

open SimpleGraph Finset Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At a minimum deletion the entire nonisolated exterior retains the
half-degree bound before choosing a cycle. The embedding records the
original positions outside the longest completion cycle. -/
theorem minimum_completion_exterior_core (w : V) (minw : G.degree w=G.minDegree)
    {a : V} (C : (completeAt G w).Walk a a) (hC : C.IsCycle)
    (longest : ∀ v (q : (completeAt G w).Walk v v), q.IsCycle → q.length ≤ C.length)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : 5 ≤ G.secondSmallestDegree) :
    Nonempty (Graph189ExteriorCore.Core ((completeAt G w).induce {v : V | v ∉ C.support})
      ((G.secondSmallestDegree-1)/2)) := by
  classical
  let U : Set V := {v | v ≠ w}
  let H := G.induce U
  obtain ⟨u,v,p,hp,_,support,maxp⟩ := longest_in_deletion G w C hC longest
  have mx {x y} (r : H.Walk x y) (hr : r.IsPath) : r.length ≤ p.length := maxp _ _ r hr
  let T : Set U := {t | t ∉ p.support.toFinset}
  let J := H.induce T
  have edge := minimum_deletion_exterior_edge w minw p hp mx notTrace notH (by omega) cap
  have high (v : U) : G.secondSmallestDegree ≤ G.degree v.val := by
    rcases degree_pair (G:=G) v.val w v.property with h|h
    · exact h
    · rw [minw] at h
      exact h.trans (G.minDegree_le_degree _)
  have connectedEdge : ∃ x y, J.Adj x y := by
    obtain ⟨x,hx,y,hy,xy⟩ := edge
    exact ⟨⟨x,fun h => hx (List.mem_toFinset.mp h)⟩,⟨y,fun h => hy (List.mem_toFinset.mp h)⟩,xy⟩
  have degree (x y : T) (adj : J.Adj x y) : (G.secondSmallestDegree-1)/2 ≤ J.degree x := by
    let D := G.secondSmallestDegree-1
    have bound (v : U) : D+1 ≤ G.degree v.val := by dsimp [D]; have := high v; omega
    have da := deletion_exterior_local_degree w p hp mx
      (a:=x.val) (b:=y.val) (fun h => x.property (List.mem_toFinset.mpr h))
      (fun h => y.property (List.mem_toFinset.mpr h)) adj (cap x.val.val) (bound x.val) (bound y.val)
    change 2*D ≤ G.secondSmallestDegree+2*(H.neighborFinset x.val \ p.support.toFinset).card at da
    change _ ≤ (H.induce T).degree x
    rw [degree_induce_filter]
    have same : (H.neighborFinset x.val).filter (fun v => v ∈ T) = H.neighborFinset x.val \ p.support.toFinset := by
      ext v
      simp [T]
    rw [same]
    dsimp [D] at da
    omega
  obtain ⟨core⟩ := Graph189ExteriorCore.of_nonisolated connectedEdge degree
  let f : J →g (completeAt G w).induce {v : V | v ∉ C.support} := {
    toFun := fun v => ⟨v.val.val,fun h => v.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := by
    intro x y eq
    exact Subtype.ext (Subtype.ext (congrArg (fun v : {u : V | u ∉ C.support} => v.val) eq))
  exact ⟨core.map_into f inj⟩

end Graph189ExteriorDegreeCycle
#print axioms Graph189ExteriorDegreeCycle.minimum_completion_exterior_core
