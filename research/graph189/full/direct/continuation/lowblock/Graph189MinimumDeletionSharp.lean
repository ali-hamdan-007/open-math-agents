import Graph189MinimumDeletionExterior

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

/-- For both parities, every nontrivial deletion exterior has a cycle of order
at least ceil((2D-k)/2)+1 when the minimum original degree off w is D+1. -/
theorem nontrivial_deletion_cycle_rounded {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) {u v : {x : V | x ≠ w}}
    (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length≤p.length)
    (edge : ∃ a ∉ p.support, ∃ b ∉ p.support, (G.induce {x : V | x ≠ w}).Adj a b)
    {k D d : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) (degree : ∀ v : {x : V | x ≠ w}, D+1 ≤ G.degree v.val)
    (two : 2≤d) (room : k+2*d ≤ 2*D+1) :
    ∃ a, ∃ Q : ((G.induce {x : V | x ≠ w}).induce {v | v ∉ p.support.toFinset}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  classical
  let H := G.induce {x : V | x ≠ w}
  let T := {t : {x : V | x ≠ w} | t ∉ p.support.toFinset}
  apply cycle_of_nonisolated_degree two
  · obtain ⟨a,ha,b,hb,adj⟩ := edge
    exact ⟨⟨a,fun h => ha (List.mem_toFinset.mp h)⟩,⟨b,fun h => hb (List.mem_toFinset.mp h)⟩,adj⟩
  · intro a b adj
    have da := deletion_exterior_local_degree w p hp longest
      (a:=a.val) (b:=b.val) (fun h => a.property (List.mem_toFinset.mpr h))
      (fun h => b.property (List.mem_toFinset.mpr h)) adj (cap a.val.val) (degree a.val) (degree b.val)
    rw [degree_induce_filter]
    have eq : (H.neighborFinset a.val).filter (fun u => u∈T) = H.neighborFinset a.val \ p.support.toFinset := by
      ext z
      simp [T]
    rw [eq]
    change 2*D ≤ k+2*(H.neighborFinset a.val \ p.support.toFinset).card at da
    omega

/-- A longest path in a nontraceable minimum deletion leaves a cycle of order
at least ceil(k/2) in a nontraceable qualifying graph. -/
theorem minimum_deletion_half_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (minw : G.degree w=G.minDegree)
    {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length≤p.length)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ q : (G.induce {x : V | x ≠ w}).Walk a b, q.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : 5 ≤ G.secondSmallestDegree) :
    ∃ a, ∃ Q : ((G.induce {x : V | x ≠ w}).induce {v | v ∉ p.support.toFinset}).Walk a a,
      Q.IsCycle ∧ (G.secondSmallestDegree+1)/2 ≤ Q.length := by
  have edge := minimum_deletion_exterior_edge w minw p hp longest notTrace notH (by omega) cap
  have high (a : {x : V | x ≠ w}) : G.secondSmallestDegree-1+1 ≤ G.degree a.val := by
    rcases degree_pair (G:=G) a.val w a.property with h|h
    · omega
    · rw [minw] at h
      have := G.minDegree_le_degree a.val
      omega
  obtain ⟨a,Q,hQ,sz⟩ := nontrivial_deletion_cycle_rounded (D:=G.secondSmallestDegree-1)
    (d:=(G.secondSmallestDegree-1)/2) w p hp longest edge cap high (by omega) (by omega)
  exact ⟨a,Q,hQ,by omega⟩

#print axioms nontrivial_deletion_cycle_rounded
#print axioms minimum_deletion_half_cycle
end Graph189ExteriorDegreeCycle
