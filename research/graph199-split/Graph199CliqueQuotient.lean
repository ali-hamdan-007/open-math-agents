import Graph199BlockChain

namespace Graph199

open Finset SimpleGraph

/-- A Hamiltonian path lifts through a partition into nonempty cliques if
each edge of the quotient corresponds to a complete join of the fibers. -/
theorem hamiltonian_of_clique_quotient {V W : Type*} [Fintype V] [Nonempty V] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : V → W)
    (hf : Function.Surjective f)
    (hfibers : ∀ x y : V, f x = f y → x ≠ y → G.Adj x y)
    (hjoins : ∀ x y : V, K.Adj (f x) (f y) → G.Adj x y)
    {a b : W} (p : K.Walk a b) (hp : p.IsHamiltonian) :
    ∃ s t : V, ∃ q : G.Walk s t, q.IsHamiltonian := by
  let fiber (w : W) : List V := (univ.filter (fun v => f v = w)).toList
  have hmem (w : W) (v : V) : v ∈ fiber w ↔ f v = w := by simp [fiber]
  apply hamiltonian_of_ordered_blocks (p.support.map fiber)
  · intro l hl
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hl
    obtain ⟨x,hx⟩ := hf w
    have hn : (fiber w).Nodup := Finset.nodup_toList _
    refine ⟨List.ne_nil_of_mem ((hmem w x).mpr hx), hn, ?_⟩
    apply List.Pairwise.isChain
    apply hn.imp_of_mem
    intro u v hu hv huv
    exact hfibers u v (((hmem w u).mp hu).trans ((hmem w v).mp hv).symm) huv
  · apply List.pairwise_map.mpr
    apply hp.isPath.support_nodup.imp
    intro u v huv x hxu hxv
    exact huv (((hmem u x).mp hxu).symm.trans ((hmem v x).mp hxv))
  · intro x
    exact ⟨fiber (f x), List.mem_map.mpr ⟨f x,hp.mem_support _,rfl⟩,
      (hmem _ _).mpr rfl⟩
  · apply (List.isChain_map fiber).mpr
    apply p.isChain_adj_support.imp
    intro u v huv x hx y hy
    have hfx := (hmem u x).mp (List.mem_of_mem_getLast? hx)
    have hfy := (hmem v y).mp (List.mem_of_mem_head? hy)
    exact hjoins x y (hfx.symm ▸ hfy.symm ▸ huv)

#print axioms hamiltonian_of_clique_quotient

end Graph199
