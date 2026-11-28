import Graph189TerminalLeafClosure

open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem neighbor_of_leaf {y : V ⊕ Bool} {l : Bool}
    (h : (terminalLeaves G u v).Adj y (.inr l)) :
    y = .inl (if l then v else u) := by
  cases y with
  | inl y => exact congrArg Sum.inl h
  | inr y => exact False.elim h

theorem leaf_not_interior {a b : V ⊕ Bool} (p : (terminalLeaves G u v).Walk a b)
    (hp : p.IsPath) {i : ℕ} (hpos : 0 < i) (hbefore : i < p.length)
    {l : Bool} (atLeaf : p.getVert i = .inr l) : False := by
  have hi : i-1+1=i := by omega
  have left := p.adj_getVert_succ (i := i-1) (by omega)
  rw [hi,atLeaf] at left
  have right := (p.adj_getVert_succ hbefore).symm
  rw [atLeaf] at right
  have same : p.getVert (i-1) = p.getVert (i+1) :=
    (neighbor_of_leaf left).trans (neighbor_of_leaf right).symm
  have bad : i-1=i+1 := hp.getVert_injOn
      (show i-1≤p.length by omega) (show i+1≤p.length by omega) same
  omega

theorem hamiltonian_leaf_at_end [DecidableEq V] {a b : V ⊕ Bool}
    (p : (terminalLeaves G u v).Walk a b) (hp : p.IsHamiltonian) (l : Bool) :
    a = .inr l ∨ b = .inr l := by
  obtain ⟨i,hi⟩ := hp.getVert_surjective (Sum.inr l)
  by_cases hz : i=0
  · left
    simpa [hz] using hi
  by_cases small : i<p.length
  · exact False.elim (leaf_not_interior p hp.isPath (i := i) (Nat.pos_of_ne_zero hz) small hi)
  · right
    rwa [p.getVert_of_length_le (by omega)] at hi

#print axioms hamiltonian_leaf_at_end
end Graph189TerminalLeafClosure
