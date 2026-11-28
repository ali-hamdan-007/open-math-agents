import Graph189NearHCBlock

open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every distinct prescribed pair spans a graph of minimum degree at least (n+1)/2. -/
theorem prescribed_of_half_degree {G : SimpleGraph V} [DecidableRel G.Adj]
    (u v : V) (distinct : u≠v)
    (degree : ∀ a, Fintype.card V+1≤2*G.degree a) : ∃ p : G.Walk u v, p.IsHamiltonian := by
  apply prescribed_of_supergraph (le_top : G≤⊤) _ (complete_prescribed u v distinct)
  intro a b _ _
  have := degree a
  have := degree b
  omega

/-- Neighbors of a degree-two vertex are the sole exceptional prescribed pair.
Dropping that vertex from a spanning path starting there retains every other vertex. -/
theorem prescribed_between_low_neighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    (z u v : V) (distinct : u≠v) (two : G.degree z=2)
    (high : ∀ a, a≠z → Fintype.card V+1 ≤ 2*G.degree a)
    (zu : G.Adj z u) (zv : G.Adj z v) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.support.length+1=Fintype.card V ∧
      ∀ a, a∈q.support ↔ a≠z := by
  classical
  obtain ⟨p,hp⟩ := prescribed_avoiding_low_neighbors z z v zv.ne (by omega) high
    (fun h => h.1.ne rfl)
  have nn := Walk.not_nil_of_ne (p:=p) zv.ne
  have pair : ({u,v} : Finset V)=G.neighborFinset z := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact (G.mem_neighborFinset _ _).mpr zu
      · exact (G.mem_neighborFinset _ _).mpr zv
    · simp [G.card_neighborFinset_eq_degree,two,distinct]
  have firstAdj := (G.mem_neighborFinset _ _).mpr (p.adj_snd nn)
  rw [←pair] at firstAdj
  have full := hp.length_support
  have parts := Walk.cons_support_tail nn
  have len : p.tail.support.length+1=Fintype.card V := by
    rw [←parts] at full
    exact full
  have ends : p.snd=u := by
    rcases Finset.mem_insert.mp firstAdj with hu | hv
    · exact hu
    · have hv' := Finset.mem_singleton.mp hv
      have nilLen := (hp.isPath.tail.nil_iff_eq.mpr hv').length_eq_zero
      have sz := p.tail.length_support
      have large := G.degree_lt_card_verts z
      omega
  refine ⟨p.tail.copy ends rfl,(Walk.isPath_copy _ _ _).mpr hp.isPath.tail,?_,?_⟩
  · simpa only [Walk.support_copy] using len
  · intro a
    rw [Walk.support_copy]
    have nd := hp.isPath.support_nodup
    rw [←parts] at nd
    constructor
    · intro mem eq
      exact (List.nodup_cons.mp nd).1 (eq ▸ mem)
    · intro diff
      have coverage := hp.mem_support a
      rw [←parts] at coverage
      exact (List.mem_cons.mp coverage).resolve_left diff

#print axioms prescribed_between_low_neighbors
end Graph189TerminalLeafClosure
