import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} {s u v t : V}

/-- Joining two walks across an edge concatenates their vertex lists. -/
theorem support_append_edge (p : G.Walk s u) (q : G.Walk v t) (h : G.Adj u v) :
    (p.append (.cons h q)).support = p.support ++ q.support := by
  simp [support_append]

/-- Paths with disjoint supports can be joined across an edge between their endpoints. -/
theorem IsPath.append_edge {p : G.Walk s u} {q : G.Walk v t}
    (hp : p.IsPath) (hq : q.IsPath) (h : G.Adj u v)
    (disjoint : ∀ x ∈ p.support, x ∉ q.support) :
    (p.append (.cons h q)).IsPath := by
  apply IsPath.mk'
  rw [support_append_edge, List.nodup_append]
  exact ⟨hp.support_nodup, hq.support_nodup, fun x hx y hy eq => disjoint x hx (eq ▸ hy)⟩

/-- Joining two paths across an edge gives a Hamiltonian path when their disjoint
supports cover the graph. -/
theorem IsPath.isHamiltonian_append_edge [DecidableEq V]
    {p : G.Walk s u} {q : G.Walk v t}
    (hp : p.IsPath) (hq : q.IsPath) (h : G.Adj u v)
    (disjoint : ∀ x ∈ p.support, x ∉ q.support)
    (cover : ∀ x, x ∈ p.support ∨ x ∈ q.support) :
    (p.append (.cons h q)).IsHamiltonian := by
  apply (hp.append_edge hq h disjoint).isHamiltonian_of_mem
  simpa [support_append_edge, List.mem_append] using cover

end SimpleGraph.Walk

#print axioms SimpleGraph.Walk.support_append_edge
#print axioms SimpleGraph.Walk.IsPath.append_edge
#print axioms SimpleGraph.Walk.IsPath.isHamiltonian_append_edge
