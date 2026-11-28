module

public import Graph189CutCore
import all Graph189CutCore

public section

namespace Graph189CutMiddle
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A cut has a nonempty side opposite any specified surviving vertex. -/
theorem side_away_from {c d : V} (hcd : c ≠ d)
    (hcut : ¬ (G.induce {x | x ≠ c}).Connected) :
    ∃ A : Finset V, Side G c A ∧ d ∉ A := by
  classical
  let D := G.induce {x | x ≠ c}
  let t : {x : V // x ≠ c} := ⟨d,hcd.symm⟩
  let A := univ.filter (fun x => ∃ hn : x ≠ c, ¬ D.Reachable ⟨x, hn⟩ t)
  have memA {x : V} : x ∈ A ↔ ∃ hn : x ≠ c, ¬ D.Reachable ⟨x,hn⟩ t := by simp [A]
  have hex : ∃ x, ¬ D.Reachable x t := by
    by_contra! hr
    exact hcut {preconnected := fun x y => (hr x).trans (hr y).symm, nonempty := ⟨t⟩}
  obtain ⟨x,hx⟩ := hex
  refine ⟨A, ⟨⟨x.val,memA.mpr ⟨x.property,hx⟩⟩,?_,?_⟩,?_⟩
  · intro h
    obtain ⟨hh,_⟩ := memA.mp h
    exact hh rfl
  · intro u v hu huv hv
    by_contra hvc
    obtain ⟨huc,hut⟩ := memA.mp hu
    have he : D.Adj ⟨u,huc⟩ ⟨v,hvc⟩ := huv
    exact hv (memA.mpr ⟨hvc, fun hr => hut (he.reachable.trans hr)⟩)
  · intro h
    obtain ⟨_, hh⟩ := memA.mp h
    exact hh (Reachable.refl _)

omit [Fintype V] in
theorem separated_sides_disjoint {c d : V} {A B : Finset V}
    (hc : G.Connected) (hcd : c ≠ d) (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have h1 := hA.dist_add hc hxA hdA
  have h2 := hB.dist_add hc hxB hcB
  rw [G.dist_comm (u := d) (v := c)] at h2
  have hpos := hc.pos_dist_of_ne hcd
  omega

private theorem complement_count {A B : Finset V} (hab : Disjoint A B) :
    Aᶜ.card = B.card + (A ∪ B)ᶜ.card := by
  have hd : Disjoint B (A ∪ B)ᶜ := by
    apply Finset.disjoint_left.mpr
    exact fun _ hb h => (mem_compl.mp h) (mem_union_right _ hb)
  have heq : Aᶜ = B ∪ (A ∪ B)ᶜ := by
    ext v
    simp only [mem_compl,mem_union]
    have hh : ¬ (v ∈ A ∧ v ∈ B) := fun hp => Finset.disjoint_left.mp hab hp.1 hp.2
    tauto
  rw [heq,card_union_of_disjoint hd]

omit [Fintype V] [DecidableEq V] in
private theorem all_contacts_of_empty_even {c : V} {S : Finset V}
    (h : Side G c S) (hc : G.Connected)
    (ha : (S.filter (fun x => Even (G.dist c x))).card = 0) :
    ∀ x ∈ S, G.Adj c x := by
  intro x hx
  by_contra hn
  obtain ⟨y,hy,hd⟩ := h.exists_distance_two hc hx hn
  have hh : (S.filter (fun x => Even (G.dist c x))).Nonempty :=
    ⟨y,mem_filter.mpr ⟨hy,by simp [hd]⟩⟩
  have := card_pos.mpr hh
  omega

/-- A vertex between the two gates has no edge into either remote side. -/
theorem middle_ball [DecidableRel G.Adj] {c d u : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G d B) (hu : u ∈ (A ∪ B)ᶜ)
    (huc : u ≠ c) (hud : u ≠ d) :
    insert u (G.neighborFinset u) ⊆ (A ∪ B)ᶜ := by
  intro v hv
  rcases mem_insert.mp hv with rfl | hv
  · exact hu
  · have he : G.Adj u v := by simpa using hv
    apply mem_compl.mpr
    intro hvab
    rcases mem_union.mp hvab with ha | hb
    · exact huc (hA.exit_eq ha he.symm (fun hh => (mem_compl.mp hu) (mem_union_left _ hh)))
    · exact hud (hB.exit_eq hb he.symm (fun hh => (mem_compl.mp hu) (mem_union_right _ hh)))

/-- Every vertex between two remote sides, other than the distinct gates,
has degree strictly below k. -/
theorem middle_vertices_low [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) {u : V} (hu : u ∈ (A ∪ B)ᶜ)
    (huc : u ≠ c) (hud : u ≠ d) : G.degree u < k := by
  classical
  by_contra! high
  have hAB := separated_sides_disjoint hc hcd hA hB hdA hcB
  obtain ⟨ha2,hak,_⟩ := hA.card_bounds hc hσ horder hpair
  obtain ⟨hb2,hbk,_⟩ := hB.card_bounds hc hσ horder hpair
  have pA := hA.parity_bound hc hσ
  have pB := hB.parity_bound hc hσ
  rw [complement_count hAB] at pA
  rw [complement_count hAB.symm,union_comm B A] at pB
  have sub := middle_ball hA hB hu huc hud
  have hcard := card_le_card sub
  have huN : u ∉ G.neighborFinset u := by simp
  have hball : (insert u (G.neighborFinset u)).card = G.degree u + 1 := by
    rw [card_insert_of_notMem huN,card_neighborFinset_eq_degree]
  rw [hball] at hcard
  have hfill := eq_of_subset_of_card_le sub (by rw [hball]; omega)
  have a := all_contacts_of_empty_even hA hc (by omega)
  have b := all_contacts_of_empty_even hB hc (by omega)
  have touch (w : V) (hw : w ∈ (A ∪ B)ᶜ) (hn : w ≠ u) : G.Adj u w := by
    rw [← hfill] at hw
    simpa using (mem_insert.mp hw).resolve_left hn
  have hcg := touch c (by simp [hA.outside,hcB]) huc.symm
  have hdg := touch d (by simp [hdA,hB.outside]) hud.symm
  have unA : u ∉ A := fun hm => (mem_compl.mp hu) (mem_union_left _ hm)
  have unB : u ∉ B := fun hm => (mem_compl.mp hu) (mem_union_right _ hm)
  have hs : insert u (A ∪ B) ⊆ univ.filter (fun x => Even (G.dist u x)) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simp
    · rcases mem_union.mp hv with ha | hb
      · rw [mem_filter]
        rw [G.dist_comm (u := u) (v := v),hA.dist_add hc ha unA,
          dist_eq_one_iff_adj.mpr (a v ha).symm,dist_eq_one_iff_adj.mpr hcg.symm]
        simp
      · rw [mem_filter]
        rw [G.dist_comm (u := u) (v := v),hB.dist_add hc hb unB,
          dist_eq_one_iff_adj.mpr (b v hb).symm,dist_eq_one_iff_adj.mpr hdg.symm]
        simp
  have cap : (insert u (A ∪ B)).card ≤ 1+k :=
    (card_le_card hs).trans (hσ u)
  rw [card_insert_of_notMem (mem_compl.mp hu),card_union_of_disjoint hAB] at cap
  omega

theorem middle_card_le_three [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) : (A ∪ B)ᶜ.card ≤ 3 := by
  classical
  let Z := (A ∪ B)ᶜ
  have hcZ : c ∈ Z := by simp [Z,hA.outside,hcB]
  have hdZ : d ∈ Z := by simp [Z,hdA,hB.outside]
  have hdZ' : d ∈ Z.erase c := mem_erase.mpr ⟨hcd.symm,hdZ⟩
  have hsmall : ((Z.erase c).erase d).card ≤ 1 := by
    refine card_le_one.mpr ?_
    intro x hx y hy
    obtain ⟨hxd,hx⟩ := mem_erase.mp hx
    obtain ⟨hxc,hx⟩ := mem_erase.mp hx
    obtain ⟨hyd,hy⟩ := mem_erase.mp hy
    obtain ⟨hyc,hy⟩ := mem_erase.mp hy
    have lx := middle_vertices_low hc hσ horder hpair hcd hA hB hdA hcB hx hxc hxd
    have ly := middle_vertices_low hc hσ horder hpair hcd hA hB hdA hcB hy hyc hyd
    by_contra hne
    exact (hpair x y hne).elim (fun hh => (Nat.not_le.mpr lx) hh)
      (fun hh => (Nat.not_le.mpr ly) hh)
  rw [card_erase_of_mem hdZ',card_erase_of_mem hcZ] at hsmall
  change Z.card ≤ 3
  omega

#print axioms middle_card_le_three
end Graph189CutMiddle
