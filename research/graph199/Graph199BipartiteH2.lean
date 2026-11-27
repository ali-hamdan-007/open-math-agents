import Graph199BipartiteOrder
import BipartitePadding

namespace Graph199BipartiteOrder

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1

theorem bipartite_traceable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {col : V → Bool}
    (hcol : ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y)
    (hc : G.Connected) (hk : 3 ≤ vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (hsep : ∀ U : Finset V,
      Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let _ : Nonempty V := hc.nonempty
  let n (b : Bool) := (univ.filter fun v => col v = b).card
  have hupper (b : Bool) : n b ≤ 2 * vertexConnectivity G - 1 :=
    bipartition_size_le hcol hc hk ht b
  have hbalance (b : Bool) : n b ≤ n (!b) + 1 :=
    bipartition_balance_of_separator hcol hsep b
  have hmin (v : V) : vertexConnectivity G ≤ G.degree v := vertexConnectivity_le_degree v
  have hsize (v : V) : G.degree v ≤ n (!col v) := by
    apply card_le_card
    intro w hw
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have h := Ne.symm (hcol ((G.mem_neighborFinset v w).mp hw))
    cases hv : col v <;> cases hw : col w <;> simp_all
  have hlarge : 2 ≤ max (n false) (n true) := by
    let v : V := Classical.choice hc.nonempty
    have hv := hsize v
    have hm := hmin v
    cases h : col v
    · simp only [h, Bool.not_false] at hv
      exact (show 2 ≤ n true by omega).trans (le_max_right _ _)
    · simp only [h, Bool.not_true] at hv
      exact (show 2 ≤ n false by omega).trans (le_max_left _ _)
  have hdeg (b : Bool) (x y : V) : n b + 1 ≤ G.degree x + G.degree y := by
    have hx := hmin x
    have hy := hmin y
    have hu := hupper b
    omega
  by_cases he : n false = n true
  · have hr : 2 ≤ n false := by simpa [← he] using hlarge
    exact (BalancedBipartite.cycle_of_cross_degree_sum hr hcol rfl he.symm
      (fun {x y} _ _ => hdeg false x y)).traceable
  have hn (c : Bool) : (univ.filter fun v => col v ≠ c).card = n (!c) := by
    congr 1
    ext v
    cases c <;> cases h : col v <;> simp [h]
  have hpad (c : Bool) (hr : 2 ≤ n (!c)) (hs : n c + 1 = n (!c)) :
      ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian :=
    BalancedBipartite.traceable_of_padded_cross_degree_sum hr c hcol hs (hn c)
      (fun {x y} _ _ => (Nat.le_succ _).trans (hdeg (!c) x y))
  rcases lt_or_gt_of_ne he with hlt | hgt
  · have hb : n true ≤ n false + 1 := hbalance true
    exact hpad false (by simpa [max_eq_right hlt.le] using hlarge) (by change n false + 1 = n true; omega)
  · have hb : n false ≤ n true + 1 := hbalance false
    exact hpad true (by simpa [max_eq_left hgt.le] using hlarge) (by change n true + 1 = n false; omega)

theorem h2_of_no_bipartition
    (hrest : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (¬ ∃ col : V → Bool, ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y) →
      G.Connected → Gᶜ.Connected → 3 ≤ vertexConnectivity G →
      vertexConnectivity G + 2 ≤ G.indepNum →
      largestInducedTreeSize G - 2 ≤ vertexConnectivity G →
      (∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) →
      ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) : OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1.H2 := by
  intro V _ _ G hc hco hk ha ht hsep
  classical
  by_cases h : ∃ col : V → Bool, ∀ ⦃x y⦄, G.Adj x y → col x ≠ col y
  · obtain ⟨col, hcol⟩ := h
    exact bipartite_traceable hcol hc hk ht hsep
  · exact hrest G h hc hco hk ha ht hsep

#print axioms bipartite_traceable
#print axioms h2_of_no_bipartition

end Graph199BipartiteOrder
