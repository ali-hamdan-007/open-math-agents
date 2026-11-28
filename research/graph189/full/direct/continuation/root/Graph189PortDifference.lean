import Graph189PortLabels
import Graph189CutSides
import Graph189SeparatorCover

namespace Graph189PortDifference
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {A B S : Finset V}

omit [DecidableRel G.Adj] in
private theorem even_cover (R Y : Finset V) (k : ℕ) (dis : Disjoint R Y)
    (cap : ∀ a, G.distEven a ≤ k+1)
    (cover : ∀ v ∈ Y, ∃ a ∈ R, Even (G.dist a v)) : Y.card ≤ R.card*k := by
  classical
  let E (a : V) := (univ.filter (fun y => Even (G.dist a y))).erase a
  have count (a : V) : (E a).card ≤ k := by
    have self : a ∈ univ.filter (fun y => Even (G.dist a y)) := by simp
    have c := card_erase_of_mem self
    have ca := cap a
    change (univ.filter (fun y => Even (G.dist a y))).card ≤ k+1 at ca
    dsimp [E]; omega
  have incl : Y ⊆ R.biUnion E := by
    intro y hy
    obtain ⟨a,ha,he⟩ := cover y hy
    exact mem_biUnion.mpr ⟨a,ha,mem_erase.mpr
      ⟨fun eq => (Finset.disjoint_left.mp dis ha) (eq ▸ hy),mem_filter.mpr ⟨mem_univ _,he⟩⟩⟩
  calc Y.card ≤ (R.biUnion E).card := card_le_card incl
       _ ≤ ∑ a ∈ R, (E a).card := card_biUnion_le
       _ ≤ ∑ _a ∈ R, k := Finset.sum_le_sum (fun a _ => count a)
       _ = _ := by simp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem cross_two (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {x v j : V} (hx : x ∈ A) (hv : v ∈ B) (xj : G.Adj x j) (jv : G.Adj j v) :
    G.dist x v = 2 := by
  have ne : x ≠ v := by rintro rfl; exact Finset.disjoint_left.mp sides.apart hx hv
  have lo := (hc x v).one_lt_dist_of_ne_of_not_adj ne (sides.no_cross x hx v hv)
  have hi := hc.dist_triangle (u:=x) (v:=j) (w:=v)
  rw [dist_eq_one_iff_adj.mpr xj,dist_eq_one_iff_adj.mpr jv] at hi
  omega

/-- Above the separator's combined even quota, an opposite port adds at most
one label to the support of a fixed root with high-pair distance at most four. -/
theorem one_new_label (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {Y : Finset V} (ys : Y ⊆ B) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (diam : ∀ v ∈ Y, G.dist x v ≤ 4)
    (contacts : ∀ i ∈ S, ∃ u ∈ A, G.Adj u i)
    {k : ℕ} (cap : ∀ a, G.distEven a ≤ k+1) (big : S.card*k < Y.card) :
    (Graph189PortLabels.support G S y \ Graph189PortLabels.support G S x).card ≤ 1 := by
  classical
  let T := Graph189PortLabels.support G S x
  let U := Graph189PortLabels.support G S y
  let L := S \ (T ∪ U)
  let f (i : V) := if h : i ∈ S then (contacts i h).choose else x
  have rep (i : V) (hi : i ∈ S) : f i ∈ A ∧ G.Adj (f i) i := by
    simpa [f,hi] using (contacts i hi).choose_spec
  let R := insert x (insert y (T ∪ L.image f))
  have tsub : T ⊆ S := filter_subset _ _
  have usub : U ⊆ S := filter_subset _ _
  have cardL := card_sdiff_add_card_eq_card (union_subset tsub usub)
  have cardU := card_sdiff_add_card U T
  change L.card + (T ∪ U).card = S.card at cardL
  rw [union_comm U T] at cardU
  have rcard : R.card ≤ 2 + T.card + L.card := by
    have ha := card_insert_le x (insert y (T ∪ L.image f))
    have hb := card_insert_le y (T ∪ L.image f)
    have hu := card_union_le T (L.image f)
    have hf : (L.image f).card ≤ L.card := card_image_le
    change (insert x (insert y (T ∪ L.image f))).card ≤ _
    omega
  have rside : ∀ a ∈ R, a ∈ A ∨ a ∈ S := by
    intro a h
    rcases mem_insert.mp h with rfl | h
    · exact Or.inl hx
    rcases mem_insert.mp h with rfl | h
    · exact Or.inl hy
    rcases mem_union.mp h with h | h
    · exact Or.inr (tsub h)
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact Or.inl (rep i (mem_sdiff.mp hi).1).1
  have dis : Disjoint R Y := by
    apply Finset.disjoint_left.mpr
    intro v hr hv
    rcases rside v hr with h | h
    · exact Finset.disjoint_left.mp sides.apart h (ys hv)
    · exact Finset.disjoint_left.mp sides.right_cut (ys hv) h
  have cover (v : V) (hv : v ∈ Y) : ∃ a ∈ R, Even (G.dist a v) := by
    have vB := ys hv
    have root (h : Even (G.dist x v)) : ∃ a ∈ R, Even (G.dist a v) := ⟨x,mem_insert_self _ _,h⟩
    by_cases parity : Even (G.dist x v)
    · exact root parity
    have d := diam v hv
    have nx : G.dist x v ≠ 1 := fun eq => sides.no_cross x hx v vB (dist_eq_one_iff_adj.mp eq)
    have d3 : G.dist x v = 3 := by rw [Nat.even_iff] at parity; omega
    obtain ⟨p,hp⟩ := (hc x v).exists_walk_length_eq_dist
    obtain ⟨j,hj,hjp⟩ := sides.meets hx vB p
    have split : (p.takeUntil j hjp).append (p.dropUntil j hjp) = p := Walk.take_spec p hjp
    have lengths := congrArg SimpleGraph.Walk.length split
    rw [SimpleGraph.Walk.length_append] at lengths
    have left := G.dist_le (p.takeUntil j hjp)
    have right := G.dist_le (p.dropUntil j hjp)
    have tri := hc.dist_triangle (u:=x) (v:=j) (w:=v)
    have xj0 : G.dist x j ≠ 0 := by
      intro eq
      exact Finset.disjoint_left.mp sides.left_cut hx ((hc.dist_eq_zero_iff.mp eq).symm ▸ hj)
    have jv0 : G.dist j v ≠ 0 := by
      intro eq
      exact Finset.disjoint_left.mp sides.right_cut vB ((hc.dist_eq_zero_iff.mp eq) ▸ hj)
    have cases' : (G.dist x j = 1 ∧ G.dist j v = 2) ∨ G.dist j v = 1 := by omega
    rcases cases' with ⟨xj,jv⟩ | jv
    · have jt : j ∈ T := mem_filter.mpr ⟨hj,dist_eq_one_iff_adj.mp xj⟩
      exact ⟨j,mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ jt)),by simp [jv]⟩
    have edge := dist_eq_one_iff_adj.mp jv
    by_cases jt : j ∈ T
    · exact root (by simp [cross_two hc sides hx vB (mem_filter.mp jt).2 edge])
    by_cases ju : j ∈ U
    · exact ⟨y,mem_insert_of_mem (mem_insert_self _ _),
        by simp [cross_two hc sides hy vB (mem_filter.mp ju).2 edge]⟩
    have jl : j ∈ L := mem_sdiff.mpr ⟨hj,fun h => (mem_union.mp h).elim jt ju⟩
    have fr : f j ∈ R := mem_insert_of_mem (mem_insert_of_mem
      (mem_union_right _ (mem_image_of_mem _ jl)))
    exact ⟨f j,fr,by simp [cross_two hc sides (rep j hj).1 vB (rep j hj).2 edge]⟩
  have quota := even_cover (G := G) R Y k dis cap cover
  change (U \ T).card ≤ 1
  by_contra! h
  have rc : R.card ≤ S.card := by omega
  exact (not_lt_of_ge (quota.trans (Nat.mul_le_mul_right k rc))) big

omit [DecidableRel G.Adj] in
/-- Any opposite-side contact at a common label sees the whole specified
small-side population at distance two, irrespective of its own degree. -/
theorem common_label_capacity (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {X : Finset V} (xs : X ⊆ A) {i : V} (common : ∀ x ∈ X, G.Adj x i)
    {v : V} (vb : v ∈ B) (vi : G.Adj v i) {k : ℕ} (cap : ∀ a, G.distEven a ≤ k+1) :
    X.card ≤ k := by
  classical
  have dis : Disjoint ({v} : Finset V) X := by
    apply Finset.disjoint_left.mpr
    intro x hx hX
    obtain rfl := mem_singleton.mp hx
    exact Finset.disjoint_left.mp sides.apart (xs hX) vb
  have hit (x : V) (hx : x ∈ X) : ∃ a ∈ ({v} : Finset V), Even (G.dist a x) :=
    ⟨v,mem_singleton_self _,by simp [cross_two hc sides.swap vb (xs hx) vi (common x hx).symm]⟩
  simpa using even_cover (G := G) {v} X k dis cap hit

#print axioms common_label_capacity
#print axioms one_new_label
end Graph189PortDifference
