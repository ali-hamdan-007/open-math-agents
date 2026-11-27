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

/-- A spanning walk in an induced graph has exactly its inducing set as
its ambient support. -/
theorem IsHamiltonian.mem_support_map_induce_iff [DecidableEq V] {U : Set V}
    {u v : U} {p : (G.induce U).Walk u v} (hp : p.IsHamiltonian) (x : V) :
    x ∈ (p.map (Embedding.induce U).toHom).support ↔ x ∈ U := by
  rw [support_map, List.mem_map]
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, hp.mem_support ⟨x, hx⟩, rfl⟩

/-- Hamiltonian paths of two induced parts give a Hamiltonian path of their
union if an edge joins the designated endpoints. -/
theorem IsHamiltonian.append_induce_edge [DecidableEq V] {U W : Set V}
    {s u : U} {v t : W} {p : (G.induce U).Walk s u} {q : (G.induce W).Walk v t}
    (hp : p.IsHamiltonian) (hq : q.IsHamiltonian) (h : G.Adj (u : V) (v : V))
    (hdis : Disjoint U W) (hcover : ∀ x : V, x ∈ U ∨ x ∈ W) :
    ∃ P : G.Walk (s : V) (t : V), P.IsHamiltonian := by
  let left := p.map (Embedding.induce U).toHom
  let right := q.map (Embedding.induce W).toHom
  have hleft : left.IsPath := hp.isPath.map Subtype.val_injective
  have hright : right.IsPath := hq.isPath.map Subtype.val_injective
  refine ⟨left.append (.cons h right), hleft.isHamiltonian_append_edge hright h ?_ ?_⟩
  · intro x hxl hxr
    exact (Set.disjoint_left.mp hdis ((hp.mem_support_map_induce_iff x).mp hxl))
      ((hq.mem_support_map_induce_iff x).mp hxr)
  · intro x
    exact (hcover x).imp ((hp.mem_support_map_induce_iff x).mpr)
      ((hq.mem_support_map_induce_iff x).mpr)

end SimpleGraph.Walk

#print axioms SimpleGraph.Walk.support_append_edge
#print axioms SimpleGraph.Walk.IsPath.append_edge
#print axioms SimpleGraph.Walk.IsPath.isHamiltonian_append_edge
#print axioms SimpleGraph.Walk.IsHamiltonian.append_induce_edge
