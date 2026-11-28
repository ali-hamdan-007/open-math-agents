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

/-- Every active second-layer vertex must also pay for the root itself at
distance two. A third-layer neighbor sees all its first-layer predecessors. -/
theorem column_limit (hc : G.Connected) (x b : V) (C : Finset V) {k : ℕ}
    (large : k≤G.degree x) (hb : G.dist x b=2) {i : V}
    (xi : G.Adj x i) (ib : G.Adj i b) (layer : ∀y∈C,G.dist x y=3)
    (cap : ∀a,G.distEven a≤k+1) :
    (C.filter (fun y => G.Adj b y)).card≤2*k-(G.degree x-k)-1 := by
  classical
  let A := G.neighborFinset x
  let P := A.filter (G.Adj b)
  let Q := A.filter (fun a => G.dist b a=2)
  by_cases active : (C.filter (fun y => G.Adj b y)).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp active]
    simp
  obtain ⟨y,hy⟩ := active
  obtain ⟨hy,by'⟩ := mem_filter.mp hy
  have boundP := layer_two_card y P (by
    intro a ha
    obtain ⟨aa,ba⟩ := mem_filter.mp ha
    have d := layer y hy
    have low := hc.dist_triangle (u:=x) (v:=a) (w:=y)
    have up := hc.dist_triangle (u:=a) (v:=b) (w:=y)
    rw [dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp aa)] at low
    rw [dist_eq_one_iff_adj.mpr ba.symm,dist_eq_one_iff_adj.mpr by'] at up
    rw [dist_comm]; omega) (cap y)
  have root : x∉Q := by
    intro h
    exact G.irrefl ((G.mem_neighborFinset _ _).mp (mem_filter.mp h).1)
  have boundQ := layer_two_card b (insert x Q) (by
    intro a ha
    rcases mem_insert.mp ha with rfl|h
    · rwa [dist_comm]
    exact (mem_filter.mp h).2) (cap b)
  rw [card_insert_of_notMem root] at boundQ
  have inc : A.filter (fun a => G.dist a b≤2)⊆P∪Q := by
    intro a ha
    obtain ⟨aa,le⟩ := mem_filter.mp ha
    have one := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp aa)
    have neq : G.dist a b≠0 := by
      intro zero
      have eq := hc.dist_eq_zero_iff.mp zero
      rw [eq] at one
      omega
    by_cases near : G.dist a b=1
    · exact mem_union_left _ (mem_filter.mpr ⟨aa,(dist_eq_one_iff_adj.mp near).symm⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨aa,by rw [dist_comm]; omega⟩)
  have h := (card_le_card inc).trans (card_union_le P Q)
  have count := Graph189ColumnCancel.column hc x b i C large xi ib layer (cap i)
  change _+(G.degree x-k)≤(A.filter (fun a => G.dist a b≤2)).card at count
  omega

/-- Each third-layer target pays any width above k through the second layer.
Each of its at most k columns can receive at most k such incidences. -/
theorem bounds (hc : G.Connected) (x : V) (B C : Finset V) {k w : ℕ}
    (large : k ≤ G.degree x) (hB : ∀ b ∈ B, G.dist x b = 2)
    (pred : ∀ b ∈ B, ∃ i, G.Adj x i ∧ G.Adj i b)
    (hC : ∀ y ∈ C, G.dist x y = 3) (cap : ∀ a, G.distEven a ≤ k+1)
    (width : ∀ y ∈ C, w ≤ ((G.neighborFinset x).filter (fun a => G.dist a y = 2)).card +
      (B.filter (fun b => G.Adj b y)).card) : (w-k)*C.card ≤ k*k ∧
      (w-k)*C.card≤k*(2*k-(G.degree x-k)-1) := by
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
  refine ⟨(rows.trans cols).trans (Nat.mul_le_mul_right k hb),?_⟩
  have more (b : V) (bb : b∈B) : (C.filter (fun y => G.Adj b y)).card≤2*k-(G.degree x-k)-1 := by
    obtain ⟨i,xi,ib⟩ := pred b bb
    exact column_limit hc x b C large (hB b bb) xi ib hC cap
  have cols' := sum_le_sum more
  simp only [sum_const,smul_eq_mul] at cols'
  exact (rows.trans cols').trans (Nat.mul_le_mul_right _ hb)

theorem bound (hc : G.Connected) (x : V) (B C : Finset V) {k w : ℕ}
    (large : k ≤ G.degree x) (hB : ∀ b ∈ B, G.dist x b = 2)
    (pred : ∀ b ∈ B, ∃ i, G.Adj x i ∧ G.Adj i b)
    (hC : ∀ y ∈ C, G.dist x y = 3) (cap : ∀ a, G.distEven a ≤ k+1)
    (width : ∀ y ∈ C, w ≤ ((G.neighborFinset x).filter (fun a => G.dist a y = 2)).card +
      (B.filter (fun b => G.Adj b y)).card) : (w-k)*C.card ≤ k*k :=
  (bounds hc x B C large hB pred hC cap width).1

end Graph189SecondLayerBudget
#print axioms Graph189SecondLayerBudget.bound
