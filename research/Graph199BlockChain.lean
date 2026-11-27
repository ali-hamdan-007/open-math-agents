import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain

namespace Graph199
open SimpleGraph

/-- Nonempty path segments can be linked in any order for which consecutive
endpoints are adjacent. The pieces are allowed to consist of a single vertex. -/
theorem flatten_block_chain {V : Type*} {G : SimpleGraph V} (blocks : List (List V))
    (nonempty : ∀ l ∈ blocks, l ≠ [])
    (internal : ∀ l ∈ blocks, l.IsChain G.Adj)
    (links : blocks.IsChain (fun l r =>
      ∀ a ∈ l.getLast?, ∀ b ∈ r.head?, G.Adj a b)) :
    blocks.flatten.IsChain G.Adj := by
  induction blocks with
  | nil => simp
  | cons l rest ih =>
    cases rest with
    | nil => simpa using internal l (by simp)
    | cons r tail =>
      obtain ⟨first, later⟩ := List.isChain_cons_cons.mp links
      apply (internal l (by simp)).append
        (ih (fun s hs => nonempty s (List.mem_cons_of_mem _ hs))
          (fun s hs => internal s (List.mem_cons_of_mem _ hs)) later)
      intro x hx y hy
      rw [List.flatten_cons, List.head?_append_of_ne_nil _ (nonempty r (by simp))] at hy
      exact first x hx y hy

/-- A partition of the vertex set into ordered spanning-path segments gives
a Hamiltonian path as soon as consecutive endpoints have connecting edges. -/
theorem hamiltonian_of_ordered_blocks {V : Type*} [Nonempty V] [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (blocks : List (List V))
    (parts : ∀ l ∈ blocks, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj)
    (disjoint : blocks.Pairwise List.Disjoint)
    (cover : ∀ x : V, ∃ l ∈ blocks, x ∈ l)
    (links : blocks.IsChain (fun l r =>
      ∀ a ∈ l.getLast?, ∀ b ∈ r.head?, G.Adj a b)) :
    ∃ s t : V, ∃ p : G.Walk s t, p.IsHamiltonian := by
  classical
  have chain := flatten_block_chain blocks (fun l h => (parts l h).1)
    (fun l h => (parts l h).2.2) links
  have distinct := List.nodup_flatten.mpr ⟨fun l h => (parts l h).2.1,disjoint⟩
  have all_mem (x : V) : x ∈ blocks.flatten := List.mem_flatten.mpr (cover x)
  have ne := List.ne_nil_of_mem (all_mem (Classical.arbitrary V))
  let p := Walk.ofSupport blocks.flatten ne chain
  have support : p.support = blocks.flatten := Walk.support_ofSupport ne chain
  have path : p.IsPath := Walk.IsPath.mk' (by rwa [support])
  exact ⟨_, _, p, path.isHamiltonian_of_mem (fun x => by rw [support]; exact all_mem x)⟩

#print axioms hamiltonian_of_ordered_blocks
end Graph199
