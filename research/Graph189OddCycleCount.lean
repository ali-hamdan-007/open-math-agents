import Graph189GirthFive

namespace Graph189OddCycleCount
open SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nontrivial V] in
/-- Double counting a relation between two finite sets. -/
private theorem sum_fibers (A B : Finset V) (R : V → V → Prop) [DecidableRel R] :
    ∑ a ∈ A, (B.filter (R a)).card = ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- The incidence count in the shortest-odd-cycle argument. Its hypotheses
are the three local bounds supplied by the cycle geometry. -/
theorem odd_cycle_core_spans (h : G.Connected) (C : Finset V) (hm : 5 ≤ C.card)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hAdj : ∀ v ∈ C, (C.filter (G.Adj v)).card ≤ 2)
    (hEven : ∀ v ∈ C, 3 ≤ (C.filter (fun x => Even (G.dist v x))).card)
    (hOutside : ∀ x ∉ C, 3 * (C.filter (fun v => G.Adj v x)).card ≤
      2 * (C.filter (fun v => G.dist v x = 2)).card) :
    C = Finset.univ := by
  classical
  let O := Finset.univ \ C
  let s := G.secondSmallestDegree
  let A (v : V) := (O.filter (G.Adj v)).card
  let D (v : V) := (O.filter (fun x => G.dist v x = 2)).card
  have subset_adj (v : V) : C.filter (G.Adj v) ∪ O.filter (G.Adj v) = G.neighborFinset v := by
    ext x
    simp [O, G.mem_neighborFinset v x]
    by_cases hx : x ∈ C <;> simp [hx]
  have hdisj (p : V → Prop) (q : V → Prop) [DecidablePred p] [DecidablePred q] :
      Disjoint (C.filter p) (O.filter q) := by
    apply Finset.disjoint_left.mpr
    intro x hxc hxo
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxo).1).2 (Finset.mem_filter.mp hxc).1
  have even_upper (v : V) (hv : v ∈ C) : D v ≤ s - 2 := by
    have hs : C.filter (fun x => Even (G.dist v x)) ∪
        O.filter (fun x => G.dist v x = 2) ⊆ Finset.univ.filter (fun x => Even (G.dist v x)) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
      · have he := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ (by decide : Even 2)⟩
    have hu := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint (hdisj _ _)] at hu
    change (C.filter (fun x => Even (G.dist v x))).card + D v ≤ G.distEven v at hu
    have hev := hEven v hv
    have hbound := hσ v
    dsimp [s]
    omega
  obtain ⟨v₀,hv₀⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z,hzz⟩ : ∃ z : V, ∀ x, x ≠ z → s ≤ G.degree x := by
    by_cases hex : ∃ z, G.degree z < s
    · obtain ⟨z,hz⟩ := hex
      exact ⟨z,fun x hx => (Graph189Bipartite.degree_pair (G := G) x z hx).resolve_right
        (Nat.not_le.mpr hz)⟩
    · exact ⟨v₀,fun x _ => by by_contra! hx; exact hex ⟨x,hx⟩⟩
  have adj_lower (v : V) (hv : v ∈ C.erase z) : s - 2 ≤ A v := by
    have hd := hzz v (Finset.ne_of_mem_erase hv)
    have hi := hAdj v (Finset.mem_of_mem_erase hv)
    have hcard := congrArg Finset.card (subset_adj v)
    rw [Finset.card_union_of_disjoint (hdisj _ _)] at hcard
    change (C.filter (G.Adj v)).card + A v = G.degree v at hcard
    omega
  have AS : (C.card - 1) * (s - 2) ≤ ∑ v ∈ C, A v := by
    have hsize : C.card - 1 ≤ (C.erase z).card := by
      by_cases hz : z ∈ C
      · exact le_of_eq (Finset.card_erase_of_mem hz).symm
      · rw [Finset.erase_eq_of_notMem hz]; omega
    have hpoint : ∑ v ∈ C.erase z, (s - 2) ≤ ∑ v ∈ C.erase z, A v :=
      Finset.sum_le_sum adj_lower
    have hconst : (C.erase z).card * (s - 2) ≤ ∑ v ∈ C.erase z, A v := by simpa using hpoint
    exact ((Nat.mul_le_mul_right _ hsize).trans hconst).trans
      (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  have DS : (∑ v ∈ C, D v) ≤ C.card * (s - 2) := by
    simpa using (Finset.sum_le_sum even_upper : ∑ v ∈ C, D v ≤ ∑ _v ∈ C, (s - 2))
  have incidence : 3 * (∑ v ∈ C, A v) ≤ 2 * (∑ v ∈ C, D v) := by
    dsimp only [A,D]
    rw [sum_fibers C O G.Adj, sum_fibers C O (fun v x => G.dist v x = 2)]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun x hx => hOutside x (Finset.mem_sdiff.mp hx).2)
  have hcoeff : 2 * C.card < 3 * (C.card - 1) := by omega
  have hszero : s - 2 = 0 := by
    by_contra hn
    have hbad : 3 * ((C.card - 1) * (s - 2)) ≤ 2 * (C.card * (s - 2)) :=
      ((Nat.mul_le_mul_left _ AS).trans incidence).trans (Nat.mul_le_mul_left _ DS)
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at hbad
    exact (Nat.not_lt_of_ge hbad) (Nat.mul_lt_mul_of_pos_right hcoeff (Nat.pos_of_ne_zero hn))
  have hclosed {v x : V} (hv : v ∈ C) (hx : G.Adj v x) : x ∈ C := by
    by_contra hn
    have hpos : 0 < A v := Finset.card_pos.mpr
      ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩,hx⟩⟩
    have hsum := Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _) hv
    have hzero : (∑ v ∈ C, D v) = 0 := by rw [hszero, Nat.mul_zero] at DS; omega
    omega
  have stays {a b : V} (p : G.Walk a b) (ha : a ∈ C) : b ∈ C := by
    induction p with
    | nil => exact ha
    | cons hab p ih => exact ih (hclosed ha hab)
  apply Finset.eq_univ_of_forall
  intro v
  obtain ⟨p⟩ := h.preconnected v₀ v
  exact stays p hv₀

#print axioms odd_cycle_core_spans
end Graph189OddCycleCount
