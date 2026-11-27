import BipartiteClosure
import BipartiteComplete

namespace BalancedBipartite

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem card_of_equal_parts {r : ℕ} {col : V → Bool}
    (hfalse : (univ.filter fun v => col v = false).card = r)
    (htrue : (univ.filter fun v => col v = true).card = r) :
    Fintype.card V = 2*r := by
  classical
  let A : Finset V := univ.filter fun v => col v = false
  let B : Finset V := univ.filter fun v => col v = true
  have hu : A ∪ B = univ := by
    ext x
    cases h : col x <;> simp [A,B,h]
  have hd : Disjoint A B := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    have ha := (mem_filter.mp hx).2
    have hb := (mem_filter.mp hy).2
    rw [ha] at hb
    contradiction
  have h := card_union_of_disjoint hd
  change (A ∪ B).card = _ at h
  rw [hu,card_univ] at h
  change _ = (univ.filter (fun v => col v = false)).card +
    (univ.filter (fun v => col v = true)).card at h
  omega

/-- The balanced bipartite Ore closure criterion. A cross nonedge whose
endpoint degrees sum to at least the size of a part plus one can be filled,
and the resulting cycle can be lifted back through every such addition. -/
theorem cycle_of_cross_degree_sum [DecidableRel G.Adj] {r : ℕ} (hr : 2 ≤ r)
    {col : V → Bool} (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hfalse : (univ.filter fun v => col v = false).card = r)
    (htrue : (univ.filter fun v => col v = true).card = r)
    (hdeg : ∀ ⦃x y⦄, col x ≠ col y → ¬ G.Adj x y → r+1 ≤ G.degree x + G.degree y) :
    HasSpanningCycle G := by
  classical
  by_contra hno
  let arcs (H : SimpleGraph V) : Finset (V × V) := by
    classical
    exact univ.filter fun v => H.Adj v.1 v.2
  let edgeCount (H : SimpleGraph V) : ℕ := (arcs H).card
  have arc_mem (H : SimpleGraph V) (v : V × V) :
      v ∈ arcs H ↔ H.Adj v.1 v.2 := by simp [arcs]
  let C : Set ℕ := {n | ∃ H : SimpleGraph V, G ≤ H ∧
    (∀ ⦃x y⦄, H.Adj x y → col x ≠ col y) ∧
    ¬ HasSpanningCycle H ∧ edgeCount H = n}
  have hfinite : C.Finite := (Set.finite_le_nat (Fintype.card (V × V))).subset (by
    rintro _ ⟨H,_,_,_,rfl⟩
    exact card_le_univ (arcs H))
  have hCne : C.Nonempty := ⟨edgeCount G,G,le_rfl,hcol,hno,rfl⟩
  obtain ⟨n,⟨H,hGH,hHcol,hHno,hHn⟩,hmax⟩ := hfinite.exists_maximal hCne
  by_cases hex : ∃ x y, col x ≠ col y ∧ ¬ H.Adj x y
  · obtain ⟨x,y,hxy,hHxy⟩ := hex
    have hne : x ≠ y := fun h => hxy (congrArg col h)
    have hdG := hdeg hxy (fun h => hHxy (hGH h))
    have hdH : r+1 ≤ H.degree x + H.degree y :=
      hdG.trans (Nat.add_le_add (degree_le_of_le hGH) (degree_le_of_le hGH))
    let J := H ⊔ edge x y
    have hHJ : H ≤ J := le_sup_left
    have hJxy : J.Adj x y := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)
    have hJcol : ∀ ⦃u v⦄, J.Adj u v → col u ≠ col v := by
      intro u v hadd
      rcases hadd with hadd | hadd
      · exact hHcol hadd
      · rcases ((edge_adj x y u v).mp hadd).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hxy
        · exact hxy.symm
    have hJno : ¬ HasSpanningCycle J := fun h =>
      hHno (cycle_of_sup_edge hr (card_of_equal_parts hfalse htrue) hHcol hxy hdH h)
    have hJmem : edgeCount J ∈ C := ⟨J,hGH.trans hHJ,hJcol,hJno,rfl⟩
    have hinc : edgeCount H < edgeCount J := by
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
      · intro z hz
        exact (arc_mem J z).mpr (hHJ ((arc_mem H z).mp hz))
      · intro he
        have hmem := (arc_mem J (x,y)).mpr hJxy
        rw [← he] at hmem
        exact hHxy ((arc_mem H (x,y)).mp hmem)
    have hle : edgeCount J ≤ n := hmax hJmem (by omega)
    omega
  · exact hHno (complete_spanning_cycle hr hfalse htrue (by
      intro x y hxy
      by_contra hn
      exact hex ⟨x,y,hxy,hn⟩))

theorem HasSpanningCycle.isHamiltonian_of_card {G : SimpleGraph V}
    (h : HasSpanningCycle G) (hcard : 3 ≤ Fintype.card V) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  classical
  obtain ⟨l,a,b,hn,hall,hc,ha,hb,hab⟩ := h
  have hne : l ≠ [] := fun he => by simp [he] at ha
  have hhead : l.head hne = a := List.head_of_head?_eq_some ha
  have hlast : l.getLast hne = b := List.getLast_of_getLast?_eq_some hb
  have hclose : G.Adj (l.getLast hne) (l.head hne) := by rwa [hhead,hlast]
  let p := Walk.ofSupport l hne hc
  let q := Walk.cons hclose p
  have hs : p.support = l := Walk.support_ofSupport hne hc
  have hp : p.IsHamiltonian :=
    (Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun z => by rw [hs]; exact hall z)
  have hlen := hp.length_eq
  have hlarge : 3 ≤ q.length := by
    change 3 ≤ p.length+1
    omega
  have hpath : q.tail.IsHamiltonian := by
    intro z
    have he : q.tail.support = p.support := by simp [q,Walk.tail_cons]
    rw [he]
    exact hp z
  have hcyc := Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨hpath.isPath,hlarge⟩
  exact ⟨_,q,⟨hcyc,hpath⟩⟩

theorem hamiltonian_cycle_of_cross_degree_sum [DecidableRel G.Adj]
    {r : ℕ} (hr : 2 ≤ r) {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hfalse : (univ.filter fun v => col v = false).card = r)
    (htrue : (univ.filter fun v => col v = true).card = r)
    (hdeg : ∀ ⦃x y⦄, col x ≠ col y → ¬ G.Adj x y → r+1 ≤ G.degree x + G.degree y) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  have hn := card_of_equal_parts hfalse htrue
  exact (cycle_of_cross_degree_sum hr hcol hfalse htrue hdeg).isHamiltonian_of_card (by omega)

#print axioms cycle_of_cross_degree_sum
#print axioms hamiltonian_cycle_of_cross_degree_sum

end BalancedBipartite
