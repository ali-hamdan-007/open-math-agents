import Graph189ExteriorPopulation

open SimpleGraph Finset
universe u
namespace Graph189ExteriorCore

/-- A nonempty finite graph of a given minimum degree, embedded in a
specified graph. The ambient graph may include isolated vertices. -/
structure Core {V : Type u} (G : SimpleGraph V) (d : ℕ) where
  X : Type u
  [finite : Fintype X]
  root : X
  graph : SimpleGraph X
  [decAdj : DecidableRel graph.Adj]
  hom : graph →g G
  injective : Function.Injective hom
  degree : ∀ x, d ≤ graph.degree x

attribute [instance] Core.finite Core.decAdj

def Core.map_into {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
    (K : Core G d) (f : G →g H) (inj : Function.Injective f) : Core H d where
  X := K.X
  root := K.root
  graph := K.graph
  hom := f.comp K.hom
  injective := inj.comp K.injective
  degree := K.degree

/-- Removing all isolated vertices makes the edgewise degree bound
uniform. The resulting embedding is an actual graph homomorphism. -/
theorem of_nonisolated {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (edge : ∃ x y, G.Adj x y)
    (degree : ∀ x y, G.Adj x y → d ≤ G.degree x) : Nonempty (Core G d) := by
  classical
  let S : Set V := {v | ∃ w, G.Adj v w}
  obtain ⟨x,y,e⟩ := edge
  refine ⟨{
    X := S
    root := ⟨x,y,e⟩
    graph := G.induce S
    hom := (Embedding.induce (G:=G) S).toHom
    injective := Subtype.val_injective
    degree := ?_ }⟩
  intro a
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  have eq : (G.neighborFinset a.val).filter (fun u => u ∈ S) = G.neighborFinset a.val := by
    apply filter_eq_self.mpr
    exact fun u hu => ⟨a.val,((G.mem_neighborFinset _ _).mp hu).symm⟩
  rw [eq,G.card_neighborFinset_eq_degree]
  obtain ⟨b,adj⟩ := a.property
  exact degree a.val b adj

#print axioms of_nonisolated
end Graph189ExteriorCore
