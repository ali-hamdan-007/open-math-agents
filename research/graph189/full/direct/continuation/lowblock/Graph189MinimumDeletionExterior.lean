import Graph189SingletonDeletion
import Graph189ConeNontrivial

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If neither G nor the minimum-vertex deletion admits a Hamiltonian path,
every longest path in that deletion has an actual exterior edge. -/
theorem minimum_deletion_exterior_edge (w : V) (minw : G.degree w=G.minDegree)
    {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length≤p.length)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ q : (G.induce {x : V | x ≠ w}).Walk a b, q.IsHamiltonian)
    (large : 3 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    ∃ a ∉ p.support, ∃ b ∉ p.support, (G.induce {x : V | x ≠ w}).Adj a b := by
  classical
  by_contra! independent
  obtain ⟨a,ha⟩ : ∃ a, a ∉ p.support := by
    by_contra! all
    exact notH ⟨u,v,p,hp.isHamiltonian_of_mem all⟩
  have high (a : {x : V | x ≠ w}) : G.secondSmallestDegree ≤ G.degree a.val := by
    rcases degree_pair (G:=G) a.val w a.property with h|h
    · exact h
    · rw [minw] at h
      exact h.trans (G.minDegree_le_degree a.val)
  have sole (b : {x : V | x ≠ w}) (ne : b≠a) : b∈p.support := by
    by_contra hb
    exact ne (unique_high_isolated w p hp longest independent (by omega) cap hb ha (high b) (high a))
  exact notTrace (singleton_minimum_deletion_traceable w minw p hp longest a ha sole large cap)

/-- The genuine minimum-deletion nontraceable branch of the baseline order.
No original four-vertex gap, minimum-degree bound, or range on n is assumed. -/
theorem minimum_deletion_long_cycle (w : V) (minw : G.degree w=G.minDegree)
    {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length≤p.length)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ q : (G.induce {x : V | x ≠ w}).Walk a b, q.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {d : ℕ} (two : 2≤d) (room : 2*d+2 ≤ G.secondSmallestDegree) :
    ∃ a, ∃ Q : ((G.induce {x : V | x ≠ w}).induce {v | v ∉ p.support.toFinset}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  obtain ⟨a,ha,b,hb,edge⟩ := minimum_deletion_exterior_edge w minw p hp longest notTrace notH (by omega) cap
  refine nontrivial_deletion_cycle (D:=G.secondSmallestDegree-1) w p hp longest
    ⟨a,fun t => ha (List.mem_toFinset.mp t),b,fun t => hb (List.mem_toFinset.mp t),edge⟩ cap ?_ two (by omega)
  intro a
  rcases degree_pair (G:=G) a.val w a.property with h|h
  · omega
  · rw [minw] at h
    have := G.minDegree_le_degree a.val
    omega

#print axioms minimum_deletion_exterior_edge
#print axioms minimum_deletion_long_cycle
end Graph189ExteriorDegreeCycle
