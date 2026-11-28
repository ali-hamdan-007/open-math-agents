import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Graph189OrderedAnchors

/-- An anchor touches a component on each side of the given component. -/
def Spans {A I : Type*} [LT I] (touch : A → I → Prop) (a : A) (i : I) : Prop :=
  ∃ l r, touch a l ∧ touch a r ∧ l < i ∧ i < r

/-- Inclusion-minimality bounds the components captured by each proper anchor
subset. The complement calculation gives two more incident components than
anchors for every nonempty anchor set. -/
theorem two_more_incident {A I : Type*} [DecidableEq A] [DecidableEq I]
    (anchors : Finset A) (components : Finset I) (neighbors : I → Finset A)
    (total : anchors.card + 2 ≤ components.card)
    (contained : ∀ i ∈ components, neighbors i ⊆ anchors)
    (minimal : ∀ t, t ⊂ anchors →
      (components.filter (fun i => neighbors i ⊆ t)).card ≤ t.card)
    {q : Finset A} (subset : q ⊆ anchors) (nonempty : q.Nonempty) :
    q.card + 2 ≤ (components.filter (fun i => ¬ Disjoint (neighbors i) q)).card := by
  classical
  have cap := minimal (anchors \ q) (Finset.sdiff_ssubset subset nonempty)
  have convert : components.filter (fun i => neighbors i ⊆ anchors \ q) =
      components.filter (fun i => Disjoint (neighbors i) q) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi,h⟩
      exact ⟨hi,Finset.disjoint_left.mpr fun v hv => (Finset.mem_sdiff.mp (h hv)).2⟩
    · rintro ⟨hi,h⟩
      exact ⟨hi,fun v hv => Finset.mem_sdiff.mpr
        ⟨contained i hi hv,Finset.disjoint_left.mp h hv⟩⟩
  rw [convert] at cap
  have split := Finset.card_filter_add_card_filter_not (s := components) (fun i => Disjoint (neighbors i) q)
  have rest := Finset.card_sdiff_add_card_eq_card subset
  omega

/-- Each interior position of a minimal bad cut is strictly spanned. If no
anchor spanned it, left and right components would consume disjoint anchor
sets, each subject to the proper-subset bound. -/
theorem interior_spanned {A I : Type*} [Fintype A] [DecidableEq A] [LinearOrder I]
    (components : Finset I) (neighbors : I → Finset A)
    (total : Fintype.card A + 2 ≤ components.card)
    (contact : ∀ i ∈ components, (neighbors i).Nonempty)
    (minimal : ∀ t : Finset A, t ⊂ Finset.univ →
      (components.filter (fun i => neighbors i ⊆ t)).card ≤ t.card)
    {l i r : I} (hl : l ∈ components) (hr : r ∈ components)
    (hli : l < i) (hir : i < r) :
    ∃ a, Spans (fun a j => j ∈ components ∧ a ∈ neighbors j) a i := by
  classical
  let leftSide := Finset.univ.filter (fun a => ∃ j ∈ components, j < i ∧ a ∈ neighbors j)
  let rightSide := Finset.univ \ leftSide
  by_contra missing
  have no_both {a j} (ha : a ∈ leftSide) (hj : j ∈ components) (hij : i < j) :
      a ∉ neighbors j := by
    intro hadj
    obtain ⟨b,hb,hbi,hab⟩ := (Finset.mem_filter.mp ha).2
    exact missing ⟨a,b,j,⟨hb,hab⟩,⟨hj,hadj⟩,hbi,hij⟩
  obtain ⟨a,ha⟩ := contact l hl
  obtain ⟨b,hb⟩ := contact r hr
  have al : a ∈ leftSide := Finset.mem_filter.mpr ⟨Finset.mem_univ _,l,hl,hli,ha⟩
  have bl : b ∉ leftSide := fun h => no_both h hr hir hb
  have lp : leftSide ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,?_⟩
    intro e
    exact bl (e ▸ Finset.mem_univ b)
  have rp : rightSide ⊂ Finset.univ := Finset.sdiff_ssubset (Finset.subset_univ _) ⟨a,al⟩
  have ls : components.filter (· < i) ⊆ components.filter (fun j => neighbors j ⊆ leftSide) := by
    intro j hj
    obtain ⟨hj,lt⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hj,fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,lt,hv⟩⟩
  have rs : components.filter (i < ·) ⊆ components.filter (fun j => neighbors j ⊆ rightSide) := by
    intro j hj
    obtain ⟨hj,lt⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hj,fun v hv => Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _,fun h => no_both h hj lt hv⟩⟩
  have lc := (Finset.card_le_card ls).trans (minimal leftSide lp)
  have rc := (Finset.card_le_card rs).trans (minimal rightSide rp)
  have cardA := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ leftSide)
  change rightSide.card + leftSide.card = _ at cardA
  rw [Finset.card_univ] at cardA
  have comp : components.erase i ⊆ components.filter (· < i) ∪ components.filter (i < ·) := by
    intro j hj
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hj
    rcases lt_or_gt_of_ne ne with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨mem,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨mem,h⟩)
  have compcard := (Finset.card_le_card comp).trans (Finset.card_union_le _ _)
  have erase : components.card ≤ (components.erase i).card + 1 := by
    by_cases h : i ∈ components
    · rw [Finset.card_erase_add_one h]
    · simp [Finset.erase_eq_of_notMem h]
  omega

/-- Every high interior needs a distinct anchor and the two ends need
two more. This is the ordered incidence step in the cocomparability proof. -/
theorem two_extra_anchors {A I : Type*} [Fintype A] [LinearOrder I]
    (touch : A → I → Prop) (inside : Finset I) {left right : I}
    (bounds : ∀ i ∈ inside, left < i ∧ i < right)
    (many : 2 ≤ inside.card)
    (covered : ∀ i ∈ inside, ∃ a, Spans touch a i)
    (unique : ∀ a, ∀ i ∈ inside, ∀ j ∈ inside, Spans touch a i → Spans touch a j → i = j)
    (left_pair : ∃ a b, a ≠ b ∧ touch a left ∧ touch b left)
    (right_pair : ∃ a b, a ≠ b ∧ touch a right ∧ touch b right) :
    inside.card + 2 ≤ Fintype.card A := by
  classical
  let rep (i : ↥inside) : A := (covered i i.property).choose
  have span_rep (i : ↥inside) : Spans touch (rep i) i := (covered i i.property).choose_spec
  have injective : Function.Injective rep := by
    intro i j eq
    apply Subtype.ext
    exact unique (rep i) i i.property j j.property (span_rep i) (eq ▸ span_rep j)
  let used := Finset.univ.image rep
  have same_left (i j : ↥inside) (hi : touch (rep i) left) (hj : touch (rep j) left) : i = j := by
    apply Subtype.ext
    rcases lt_trichotomy (i : I) j with h | h | h
    · obtain ⟨_,r,_,hr,_,hjr⟩ := span_rep j
      exact unique (rep j) i i.property j j.property
        ⟨left,r,hj,hr,(bounds i i.property).1,h.trans hjr⟩ (span_rep j)
    · exact h
    · obtain ⟨_,r,_,hr,_,hir⟩ := span_rep i
      exact (unique (rep i) j j.property i i.property
        ⟨left,r,hi,hr,(bounds j j.property).1,h.trans hir⟩ (span_rep i)).symm
  have same_right (i j : ↥inside) (hi : touch (rep i) right) (hj : touch (rep j) right) : i = j := by
    apply Subtype.ext
    rcases lt_trichotomy (i : I) j with h | h | h
    · obtain ⟨l,_,hl,_,hli,_⟩ := span_rep i
      exact (unique (rep i) j j.property i i.property
        ⟨l,right,hl,hi,hli.trans h,(bounds j j.property).2⟩ (span_rep i)).symm
    · exact h
    · obtain ⟨l,_,hl,_,hlj,_⟩ := span_rep j
      exact unique (rep j) i i.property j j.property
        ⟨l,right,hl,hj,hlj.trans h,(bounds i i.property).2⟩ (span_rep j)
  have spare (v : I) (pair : ∃ a b, a ≠ b ∧ touch a v ∧ touch b v)
      (common : ∀ i j : ↥inside, touch (rep i) v → touch (rep j) v → i = j) :
      ∃ a, a ∉ used ∧ touch a v := by
    obtain ⟨a,b,ne,ha,hb⟩ := pair
    by_cases h : a ∈ used
    · refine ⟨b,?_,hb⟩
      intro h'
      obtain ⟨i,_,ei⟩ := Finset.mem_image.mp h
      obtain ⟨j,_,ej⟩ := Finset.mem_image.mp h'
      exact ne (ei.symm.trans ((congrArg rep (common i j (ei ▸ ha) (ej ▸ hb))).trans ej))
    · exact ⟨a,h,ha⟩
  obtain ⟨a,ha,hal⟩ := spare left left_pair same_left
  obtain ⟨b,hb,hbr⟩ := spare right right_pair same_right
  have distinct : b ≠ a := by
    rintro rfl
    obtain ⟨i,hi,j,hj,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < inside.card)
    have both (v : I) (hv : v ∈ inside) : Spans touch b v :=
      ⟨left,right,hal,hbr,(bounds v hv).1,(bounds v hv).2⟩
    exact ne (unique b i hi j hj (both i hi) (both j hj))
  have cards : used.card = inside.card := by
    change (Finset.univ.image rep).card = inside.card
    rw [Finset.card_image_of_injective _ injective]
    simp
  have fresh : b ∉ insert a used := by simpa using And.intro distinct hb
  have upper := Finset.card_le_univ (insert b (insert a used))
  rw [Finset.card_insert_of_notMem fresh, Finset.card_insert_of_notMem ha, cards] at upper
  omega

#print axioms two_more_incident
#print axioms interior_spanned
#print axioms two_extra_anchors
end Graph189OrderedAnchors
