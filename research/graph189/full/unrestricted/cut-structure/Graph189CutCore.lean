module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Multiset.Sort
public import Mathlib.SetTheory.Cardinal.Finite

/-!
The parity estimate in Easwar–Johari, §5, applied directly to arbitrary sides
of a separating vertex. The side need not have been constructed as a block.
-/

public section

namespace Graph189CutCore
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The defining expression of the upstream even-distance invariant. -/
noncomputable def evenCard (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter fun y => Even (G.dist v y)).card

/-- The defining expression of the upstream degree sequence. -/
noncomputable def sortedDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : V => G.degree v).sort (· ≤ ·)

/-- The defining expression of the upstream second-smallest degree. -/
noncomputable def secondDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (sortedDegrees G).getD 1 0

/-- All edges leaving a nonempty side pass through the gate. -/
structure Side (G : SimpleGraph V) (c : V) (S : Finset V) : Prop where
  nonempty : S.Nonempty
  outside : c ∉ S
  exit_eq : ∀ {u v}, u ∈ S → G.Adj u v → v ∉ S → v = c

omit [Fintype V] [DecidableEq V] in
theorem Side.contact {c : V} {S : Finset V} (h : Side G c S) (hc : G.Connected) :
    ∃ x ∈ S, G.Adj x c := by
  obtain ⟨w,hw⟩ := h.nonempty
  obtain ⟨P⟩ := hc w c
  obtain ⟨d, _, hin, hout⟩ := P.exists_boundary_dart (S : Set V) hw h.outside
  exact ⟨d.fst,hin,h.exit_eq hin d.adj hout ▸ d.adj⟩

omit [Fintype V] in
theorem Side.dist_add {c x y : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) (hx : x ∈ S) (hy : y ∉ S) :
    G.dist x y = G.dist x c + G.dist c y := by
  obtain ⟨P,hP⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨d, hd, hin, hout⟩ := P.exists_boundary_dart (S : Set V) hx hy
  have hm : c ∈ P.support := h.exit_eq hin d.adj hout ▸ P.dart_snd_mem_support_of_mem_darts hd
  have hsum := congrArg Walk.length (P.take_spec hm)
  rw [Walk.length_append, hP] at hsum
  exact le_antisymm hc.dist_triangle (by
    have := G.dist_le (P.takeUntil c hm)
    have := G.dist_le (P.dropUntil c hm)
    omega)

theorem Side.parity_bound {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1 + k) :
    Sᶜ.card + (S.filter (fun y => Even (G.dist c y))).card + 1 ≤ 2*k+2 := by
  classical
  obtain ⟨x,hx,hxc⟩ := h.contact hc
  let E (v : V) := univ.filter (fun y => Even (G.dist v y))
  let A := S.filter (fun y => Even (G.dist c y))
  have hxA : x ∉ A := by simp [A,dist_eq_one_iff_adj.mpr hxc.symm]
  have hdis : Disjoint (insert x A) Sᶜ := by
    apply Finset.disjoint_left.mpr
    intro y hy hys
    have h' : y ∈ S := by
      rcases mem_insert.mp hy with rfl | hh
      · exact hx
      · exact (mem_filter.mp hh).1
    exact (mem_compl.mp hys) h'
  have hin : insert x A ∪ Sᶜ ⊆ E c ∪ E x := by
    intro y hy
    rcases mem_union.mp hy with hm | hm
    · rcases mem_insert.mp hm with rfl | ha
      · exact mem_union_right _ (by simp [E])
      · exact mem_union_left _ (by simpa [E] using (mem_filter.mp ha).2)
    · have hd := h.dist_add hc hx (mem_compl.mp hm)
      rw [dist_eq_one_iff_adj.mpr hxc] at hd
      simp only [E, mem_union, mem_filter, mem_univ, true_and, Nat.even_iff]
      omega
  have hu := (card_le_card hin).trans (card_union_le (E c) (E x))
  rw [card_union_of_disjoint hdis, card_insert_of_notMem hxA] at hu
  have h1 : (E c).card ≤ 1+k := hσ c
  have h2 : (E x).card ≤ 1+k := hσ x
  change Sᶜ.card + A.card + 1 ≤ 2*k+2
  omega

/-- In a graph of order above the small-order threshold, every branch
contains two vertices, and consequently contains a vertex of high degree. -/
theorem Side.card_bounds [DecidableRel G.Adj] {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) :
    2 ≤ S.card ∧ k ≤ S.card ∧ Sᶜ.card ≤ 2*k+1 := by
  classical
  have hb := h.parity_bound hc hσ
  have hcs := card_add_card_compl S
  have h2 : 1 < S.card := by omega
  obtain ⟨x,hx,y,hy,hne⟩ := one_lt_card.mp h2
  have deg (v : V) (hv : v ∈ S) : G.degree v ≤ S.card := by
    have hin : G.neighborFinset v ⊆ insert c (S.erase v) := by
      intro w hw
      have he : G.Adj v w := by simpa using hw
      by_cases h' : w ∈ S
      · exact mem_insert_of_mem (mem_erase.mpr ⟨he.ne.symm,h'⟩)
      · exact mem_insert.mpr (Or.inl (h.exit_eq hv he h'))
    have hh := card_le_card hin
    rw [card_neighborFinset_eq_degree, card_insert_of_notMem (by
      exact fun hm => h.outside (mem_of_mem_erase hm)), card_erase_of_mem hv] at hh
    omega
  exact ⟨by omega, (hpair x y hne).elim (·.trans (deg x hx)) (·.trans (deg y hy)), by omega⟩

omit [Fintype V] [DecidableEq V] in
/-- If a branch contains a nonneighbor of its gate, it contains a vertex
at distance exactly two from the gate. -/
theorem Side.exists_distance_two {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {v : V} (hv : v ∈ S) (hn : ¬ G.Adj c v) :
    ∃ u ∈ S, G.dist c u = 2 := by
  classical
  obtain ⟨P⟩ := hc v c
  let far : Set V := {u | u ∈ S ∧ ¬ G.Adj c u}
  have hnot : c ∉ far := fun hm => h.outside hm.1
  obtain ⟨d,_,hin,hout⟩ := P.exists_boundary_dart far ⟨hv, hn⟩ hnot
  have hnear : G.Adj c d.snd := by
    by_contra hh
    have h' : d.snd ∉ S := fun hs => hout ⟨hs,hh⟩
    have heq := h.exit_eq hin.1 d.adj h'
    exact hin.2 (heq ▸ d.adj.symm)
  let Q : G.Walk c d.fst := .cons hnear (.cons d.adj.symm .nil)
  have hle : G.dist c d.fst ≤ 2 := G.dist_le Q
  have hlt := hc.one_lt_dist_of_ne_of_not_adj
    (show c ≠ d.fst from fun he => h.outside (he ▸ hin.1)) hin.2
  exact ⟨d.fst, hin.1, by omega⟩

/-- At a branching cut, two other large branches exhaust both parity budgets.
This forces every vertex in the first branch to touch the gate. -/
theorem Side.full_contact_of_two_other_sides {c : V} {S T U : Finset V}
    (hS : Side G c S) (hT : Side G c T) (hU : Side G c U)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (ht : k ≤ T.card) (hu : k ≤ U.card) :
    ∀ x ∈ S, G.Adj c x := by
  classical
  have hdis : c ∉ T ∪ U := fun hm => (mem_union.mp hm).elim hT.outside hU.outside
  have hin : insert c (T ∪ U) ⊆ Sᶜ := by
    intro v hv
    apply mem_compl.mpr
    rcases mem_insert.mp hv with rfl | hv
    · exact hS.outside
    · rcases mem_union.mp hv with ht | hu
      · exact fun hs => Finset.disjoint_left.mp hST hs ht
      · exact fun hs => Finset.disjoint_left.mp hSU hs hu
  have hcs := card_le_card hin
  rw [card_insert_of_notMem hdis,card_union_of_disjoint hTU] at hcs
  have hb := hS.parity_bound hc hσ
  intro x hx
  by_contra hn
  obtain ⟨y,hy,hy2⟩ := hS.exists_distance_two hc hx hn
  have hp : 0 < (S.filter (fun y => Even (G.dist c y))).card :=
    card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,by simp [hy2]⟩⟩
  omega

/-- Under the large-order Graph 189 hypotheses, a single cut vertex cannot
have three disjoint branches. -/
theorem no_three_sides [DecidableRel G.Adj] {c : V} {S T U : Finset V}
    (hS : Side G c S) (hT : Side G c T) (hU : Side G c U)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) : False := by
  classical
  obtain ⟨hs,hs',_⟩ := hS.card_bounds hc hσ horder hpair
  obtain ⟨ht,ht',_⟩ := hT.card_bounds hc hσ horder hpair
  obtain ⟨hu,hu',_⟩ := hU.card_bounds hc hσ horder hpair
  obtain ⟨x,hx,hxc⟩ := hS.contact hc
  have hadjT := hT.full_contact_of_two_other_sides hS hU hST.symm hTU hSU hc hσ hs' hu'
  have hadjU := hU.full_contact_of_two_other_sides hS hT hSU.symm hTU.symm hST hc hσ hs' ht'
  have hxa : x ∉ T ∪ U := fun hm => (mem_union.mp hm).elim
    (Finset.disjoint_left.mp hST hx) (Finset.disjoint_left.mp hSU hx)
  have hsub : insert x (T ∪ U) ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp
    · rcases mem_union.mp hy with h | h
      · have hd := hS.dist_add hc hx (fun hs => Finset.disjoint_left.mp hST hs h)
        simp [hd,dist_eq_one_iff_adj.mpr hxc,dist_eq_one_iff_adj.mpr (hadjT y h)]
      · have hd := hS.dist_add hc hx (fun hs => Finset.disjoint_left.mp hSU hs h)
        simp [hd,dist_eq_one_iff_adj.mpr hxc,dist_eq_one_iff_adj.mpr (hadjU y h)]
  have hb : (insert x (T ∪ U)).card ≤ 1+k := (card_le_card hsub).trans (hσ x)
  rw [card_insert_of_notMem hxa,card_union_of_disjoint hTU] at hb
  omega


/-- The ambient vertex set of one connected component after deleting the gate. -/
noncomputable def componentVertices (c : V)
    (C : (G.induce {v | v ≠ c}).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun x => ∃ h : x ≠ c, (G.induce {v | v ≠ c}).connectedComponentMk ⟨x,h⟩ = C)

private theorem mem_componentVertices {c x : V}
    {C : (G.induce {v | v ≠ c}).ConnectedComponent} :
    x ∈ componentVertices c C ↔
      ∃ h : x ≠ c, (G.induce {v | v ≠ c}).connectedComponentMk ⟨x,h⟩ = C := by
  classical
  simp [componentVertices]

private theorem componentVertices_side (c : V) (C : (G.induce {v | v ≠ c}).ConnectedComponent) :
    Side G c (componentVertices c C) := by
  classical
  constructor
  · obtain ⟨x,hx⟩ := (Quot.mk_surjective C)
    exact ⟨x.val, mem_componentVertices.mpr ⟨x.property,hx⟩⟩
  · intro h
    obtain ⟨hn,_⟩ := mem_componentVertices.mp h
    exact hn rfl
  · intro u v hu hadj hv
    by_contra hne
    obtain ⟨huc,hC⟩ := mem_componentVertices.mp hu
    have h' : (G.induce {v | v ≠ c}).Adj ⟨u,huc⟩ ⟨v,hne⟩ := hadj
    exact hv (mem_componentVertices.mpr
      ⟨hne,(ConnectedComponent.connectedComponentMk_eq_of_adj h').symm.trans hC⟩)

private theorem componentVertices_disjoint {c : V}
    {A B : (G.induce {v | v ≠ c}).ConnectedComponent} (hne : A ≠ B) :
    Disjoint (componentVertices c A) (componentVertices c B) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hA hB
  obtain ⟨_,ha⟩ := mem_componentVertices.mp hA
  obtain ⟨_,hb⟩ := mem_componentVertices.mp hB
  exact hne (ha.symm.trans hb)

/-- The local block-branching obstruction. Removing any vertex leaves at most
two connected components. The exact Graph 189 degree statistic is used through
its defining order-statistic property. -/
theorem components_after_deleting_le_two [DecidableRel G.Adj]
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) (c : V) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent ≤ 2 := by
  classical
  let _ := Fintype.ofFinite (G.induce {v | v ≠ c}).ConnectedComponent
  rw [Nat.card_eq_fintype_card]
  by_contra! h
  obtain ⟨A,B,C,hAB,hAC,hBC⟩ := Fintype.two_lt_card_iff.mp h
  exact no_three_sides (componentVertices_side c A) (componentVertices_side c B)
    (componentVertices_side c C) (componentVertices_disjoint hAB)
    (componentVertices_disjoint hAC) (componentVertices_disjoint hBC) hc hσ horder hpair


omit [DecidableEq V] in
/-- The order-statistic argument from OMA's
`WrittenOnTheWallII.GraphConjecture189.conjecture189.R1` (PR #2971). -/
private lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondDegree G ≤ G.degree x ∨ secondDegree G ≤ G.degree y := by
  classical
  let ds := sortedDegrees G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, sortedDegrees] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, sortedDegrees]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, sortedDegrees]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))


/-- The cut-vertex branch of R2 can be restricted to a deletion with exactly
two components. No assumption is made on their sizes, connectivity, or shape. -/
theorem components_after_cut_eq_two [DecidableRel G.Adj] [Nontrivial V]
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1 + (secondDegree G))
    (horder : 2 * (secondDegree G) + 3 ≤ Fintype.card V) {c : V}
    (hcut : ¬ (G.induce {v | v ≠ c}).Connected) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2 := by
  classical
  have hub := components_after_deleting_le_two hc hσ horder (degree_pair (G := G)) c
  apply le_antisymm hub
  by_contra! h
  let _ := Fintype.ofFinite (G.induce {v | v ≠ c}).ConnectedComponent
  rw [Nat.card_eq_fintype_card] at h
  have _ : Subsingleton (G.induce {v | v ≠ c}).ConnectedComponent :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨w,hw⟩ := exists_ne c
  exact hcut { preconnected := fun u v => ConnectedComponent.exact (Subsingleton.elim _ _)
               nonempty := ⟨⟨w,hw⟩⟩ }

#print axioms components_after_cut_eq_two

end Graph189CutCore
