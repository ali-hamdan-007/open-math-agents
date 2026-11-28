import Graph189ColumnCancel

namespace Graph189SecondLayerBudget
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem layer_two_card (v : V) (T : Finset V) {k : ℕ}
    (two : ∀ t ∈ T, G.dist v t = 2) (cap : G.distEven v ≤ k+1) : T.card ≤ k := by
  classical
  let E := univ.filter (fun u => Even (G.dist v u))
  have self : v ∈ E := by simp [E]
  have sub : T ⊆ E.erase v := by
    intro t ht
    have h := two t ht
    have ne : t ≠ v := by rintro rfl; simp at h
    exact mem_erase.mpr ⟨ne, mem_filter.mpr ⟨mem_univ _, by rw [h]; decide⟩⟩
  change E.card ≤ k+1 at cap
  have := card_le_card sub
  rw [card_erase_of_mem self] at this
  omega

/-- Each third-layer target pays any width above k through the second layer.
Each of its at most k columns can receive at most k such incidences. -/
theorem bound (hc : G.Connected) (x : V) (B C : Finset V) {k w : ℕ}
    (large : k ≤ G.degree x) (hB : ∀ b ∈ B, G.dist x b = 2)
    (pred : ∀ b ∈ B, ∃ i, G.Adj x i ∧ G.Adj i b)
    (hC : ∀ y ∈ C, G.dist x y = 3) (cap : ∀ a, G.distEven a ≤ k+1)
    (width : ∀ y ∈ C, w ≤ ((G.neighborFinset x).filter (fun a => G.dist a y = 2)).card +
      (B.filter (fun b => G.Adj b y)).card) : (w-k)*C.card ≤ k*k := by
  classical
  let A := G.neighborFinset x
  have hb := layer_two_card x B hB (cap x)
  have row (y : V) (hy : y ∈ C) : w-k ≤ (B.filter (fun b => G.Adj b y)).card := by
    have h := layer_two_card y (A.filter (fun a => G.dist a y = 2)) (by
      intro a ha
      rw [dist_comm]
      exact (mem_filter.mp ha).2) (cap y)
    have := width y hy
    change w ≤ (A.filter _).card + _ at this
    omega
  have col (b : V) (bb : b ∈ B) : (C.filter (fun y => G.Adj b y)).card ≤ k := by
    obtain ⟨i,hxi,hib⟩ := pred b bb
    have h := Graph189ColumnCancel.column hc x b i C large hxi hib hC (cap i)
    have size := card_le_card (filter_subset (fun a => G.dist a b ≤ 2) (G.neighborFinset x))
    rw [G.card_neighborFinset_eq_degree] at size
    omega
  have rows := sum_le_sum row
  have cols := sum_le_sum col
  have transpose : (∑ y ∈ C, (B.filter (fun b => G.Adj b y)).card) =
      ∑ b ∈ B, (C.filter (fun y => G.Adj b y)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [transpose] at rows
  simp only [sum_const, smul_eq_mul] at rows cols
  rw [Nat.mul_comm (w-k)]
  exact (rows.trans cols).trans (Nat.mul_le_mul_right k hb)

end Graph189SecondLayerBudget
#print axioms Graph189SecondLayerBudget.bound
