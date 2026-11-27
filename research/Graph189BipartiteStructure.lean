import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! For Ermelinda DeLaViña's Written on the Wall II, Graph Conjecture 189. -/
namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- The order-statistic argument from OMA's
`WrittenOnTheWallII.GraphConjecture189.conjecture189.R1` (PR #2971). -/
lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))


omit [Fintype V] [DecidableEq V] in
/-- Parity of a walk is determined by the colors of its endpoints. -/
theorem even_walk_iff {a b : V} (C : G.Coloring (Fin 2)) (p : G.Walk a b) :
    Even p.length ↔ C a = C b := by
  induction p with
  | nil => simp
  | @cons a t b e p ih =>
    have he := C.valid e
    have hac : C a = C b ↔ C t ≠ C b := by
      generalize C a = ca at he ⊢
      generalize C t = ct at he ⊢
      generalize C b = cb
      fin_cases ca <;> fin_cases ct <;> fin_cases cb <;> simp_all
    rw [Walk.length_cons, hac]
    change Even (p.length + 1) ↔ ¬ C t = C b
    rw [← ih]
    simp [Nat.even_add_one]

omit [DecidableEq V] in
/-- The even-distance vertices are precisely the color class of the starting vertex. -/
theorem distEven_eq_card (h : G.Connected) (C : G.Coloring (Fin 2)) (a : V) :
    distEven G a = (Finset.univ.filter (fun b => C b = C a)).card := by
  classical
  unfold distEven
  congr 1
  ext b
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hp, even_walk_iff C p, eq_comm]

omit [DecidableEq V] in
/-- The opposite color class contains the neighborhood, and each color class through
a vertex has size at most one plus the original conjecture's second-smallest degree. -/
theorem color_class_bounds [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (a : V) :
    G.degree a ≤ (Finset.univ.filter (fun b => C b ≠ C a)).card ∧
      (Finset.univ.filter (fun b => C b = C a)).card ≤ 1 + secondSmallestDegree G := by
  constructor
  · rw [SimpleGraph.degree]
    apply Finset.card_le_card
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (C.valid
      (G.mem_neighborFinset a b |>.mp hb)).symm⟩
  · rw [← distEven_eq_card h C a]
    exact (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).trans hσ


/-- The finite part indexed by a color. -/
def part (C : G.Coloring (Fin 2)) (c : Fin 2) : Finset V :=
  Finset.univ.filter (fun v => C v = c)

omit [DecidableEq V] in
theorem mem_part (C : G.Coloring (Fin 2)) (c : Fin 2) (v : V) :
    v ∈ part C c ↔ C v = c := by simp [part]

omit [DecidableEq V] in
theorem neighborFinset_subset_part [DecidableRel G.Adj]
    (C : G.Coloring (Fin 2)) {c d : Fin 2} (hcd : c ≠ d) {x : V}
    (hx : x ∈ part C c) : G.neighborFinset x ⊆ part C d := by
  intro y hy
  rw [mem_part] at hx ⊢
  have ne := C.valid ((G.mem_neighborFinset x y).mp hy)
  rw [hx] at ne
  generalize C y = e at ne ⊢
  fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all

omit [DecidableEq V] in
/-- The conjecture's degree condition forces the sizes of the two parts to differ by
at most one. If they differ, at most one vertex of the larger side misses any cross edge. -/
theorem unbalanced_part_complete_off_one [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hc : (part C c).Nonempty)
    (hsize : (part C c).card < (part C d).card) :
    (part C d).card = (part C c).card + 1 ∧
      ∃ z ∈ part C d, ∀ y ∈ part C d, y ≠ z → ∀ x ∈ part C c, G.Adj y x := by
  have htwo : 1 < (part C d).card := by
    have := Finset.card_pos.mpr hc
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp htwo
  have bound : (part C d).card ≤ 1 + secondSmallestDegree G := by
    have hu' := (mem_part C d u).mp hu
    simpa [part, hu'] using (color_class_bounds h C hσ u).2
  have degUpper (y : V) (hy : y ∈ part C d) : G.degree y ≤ (part C c).card :=
    Finset.card_le_card (neighborFinset_subset_part C hcd.symm hy)
  have hadj (y : V) (hy : y ∈ part C d) (hhigh : secondSmallestDegree G ≤ G.degree y)
      (x : V) (hx : x ∈ part C c) : G.Adj y x := by
    have hdeg : (part C c).card ≤ (G.neighborFinset y).card := by
      change (part C c).card ≤ G.degree y
      omega
    exact (G.mem_neighborFinset y x).mp
      ((Finset.eq_of_subset_of_card_le (neighborFinset_subset_part C hcd.symm hy) hdeg).symm ▸ hx)
  have hsmall : secondSmallestDegree G ≤ (part C c).card :=
    (degree_pair u v huv).elim (·.trans (degUpper u hu)) (·.trans (degUpper v hv))
  refine ⟨by omega, ?_⟩
  by_cases hex : ∃ z ∈ part C d, G.degree z < secondSmallestDegree G
  · obtain ⟨z,hz,hzlow⟩ := hex
    exact ⟨z,hz,fun y hy hyz => hadj y hy ((degree_pair y z hyz).resolve_right (by omega))⟩
  · exact ⟨u,hu,fun y hy _ => hadj y hy (by
      by_contra! hylow
      exact hex ⟨y,hy,hylow⟩)⟩

/-- In equal-sized parts, the cross edges missing between vertices of degree at
least the second-smallest degree form a matching. -/
theorem balanced_missing_edges [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hsize : (part C c).card = (part C d).card)
    {x : V} (hx : x ∈ part C c) (hhigh : secondSmallestDegree G ≤ G.degree x) :
    ∀ y ∈ part C d, ∀ z ∈ part C d, ¬ G.Adj x y → ¬ G.Adj x z → y = z := by
  have bound : (part C c).card ≤ 1 + secondSmallestDegree G := by
    have hx' := (mem_part C c x).mp hx
    simpa [part, hx'] using (color_class_bounds h C hσ x).2
  have card_le : ((part C d) \ G.neighborFinset x).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset (neighborFinset_subset_part C hcd hx)]
    change (part C d).card - G.degree x ≤ 1
    omega
  intro y hy z hz hxy hxz
  exact Finset.card_le_one.mp card_le y
    (Finset.mem_sdiff.mpr ⟨hy,fun hm => hxy ((G.mem_neighborFinset x y).mp hm)⟩) z
    (Finset.mem_sdiff.mpr ⟨hz,fun hm => hxz ((G.mem_neighborFinset x z).mp hm)⟩)

#print axioms unbalanced_part_complete_off_one
#print axioms balanced_missing_edges
end Graph189Bipartite
