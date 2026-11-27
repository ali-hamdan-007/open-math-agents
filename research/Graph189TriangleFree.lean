import Graph189CyclicGeometry
import Graph189BipartiteFull

namespace Graph189TriangleFree
open SimpleGraph
open scoped Fin.CommRing Fin.NatCast

private theorem cyclic_gap {m : ℕ} [NeZero m] {r : ℕ} (hr : r < m)
    {i j : Fin m} (hij : i < j)
    (hgap : j.val - i.val = r ∨ j.val - i.val = m-r) :
    j = i + (r : Fin m) ∨ i = j + (r : Fin m) := by
  have hi := i.isLt
  have hj := j.isLt
  change i.val < j.val at hij
  rcases hgap with hl | hl
  · left
    apply Fin.ext
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : i.val + r < m)]
    omega
  · right
    apply Fin.ext
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hr,
      Nat.mod_eq_sub_mod (by omega : m ≤ j.val+r), Nat.mod_eq_of_lt (by omega : j.val + r - m < m)]
    omega

private theorem traceable_nonbipartite {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.Connected) (hb : ¬ G.IsBipartite)
    (ht : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a,p,hp,hmin⟩ := Graph189ShortestOdd.exists_shortest h hb
  have hm := Graph189ShortestOdd.odd_ge_five p hp ht
  have : NeZero p.length := ⟨by omega⟩
  let f : Fin p.length ↪ V :=
    ⟨fun i => p.getVert i.val, Graph189ShortestOdd.shortest_index_injective p hp hmin⟩
  have hcyc (i : Fin p.length) : G.Adj (f i) (f (i+1)) := by
    have hi := i.isLt
    have hstep := p.adj_getVert_succ (i := i.val) hi
    change G.Adj (p.getVert i.val) (p.getVert (i+1).val)
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < p.length)]
    by_cases he : i.val+1 < p.length
    · rw [Nat.mod_eq_of_lt he]
      exact hstep
    · have hn : i.val + 1 = p.length := by omega
      rw [hn, Nat.mod_self, Walk.getVert_zero]
      rw [hn, Walk.getVert_length] at hstep
      exact hstep
  have h1 (i j : Fin p.length) (hh : G.Adj (f i) (f j)) : j = i+1 ∨ i = j+1 := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact cyclic_gap (by omega : 1 < p.length) hij
        ((Graph189ShortestOdd.short_detours p hp hmin hij j.isLt).1 hh)
    · exact (G.irrefl hh).elim
    · exact (cyclic_gap (by omega : 1 < p.length) hji
        ((Graph189ShortestOdd.short_detours p hp hmin hji i.isLt).1 hh.symm)).symm
  have h2 (i j : Fin p.length) (hne : i ≠ j)
      (hh : ∃ x, G.Adj (f i) x ∧ G.Adj x (f j)) : j = i+2 ∨ i = j+2 := by
    rcases lt_trichotomy i j with hij | he | hji
    · exact cyclic_gap (by omega : 2 < p.length) hij
        ((Graph189ShortestOdd.short_detours p hp hmin hij j.isLt).2 hh)
    · exact (hne he).elim
    · obtain ⟨x,ha,hb⟩ := hh
      exact (cyclic_gap (by omega : 2 < p.length) hji
        ((Graph189ShortestOdd.short_detours p hp hmin hji i.isLt).2 ⟨x,hb.symm,ha.symm⟩)).symm
  exact Graph189CyclicGeometry.traceable_of_geometry h ht hσ hm hp f hcyc h1 h2

/-- The full triangle-free case of DeLaViña's Written on the Wall II conjecture 189,
including nonbipartite graphs with four-cycles. -/
theorem hamiltonian {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.Connected)
    (ht : ∀ {a b c}, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases hb : G.IsBipartite
  · exact Graph189Bipartite.hamiltonian_bipartite G h hb hσ
  · apply traceable_nonbipartite h hb ht
    intro x
    exact (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)).trans hσ

#print axioms hamiltonian
end Graph189TriangleFree
