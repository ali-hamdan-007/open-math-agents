module

public import Graph189CutMiddle
import all Graph189CutCore

public section

namespace Graph189CutUnique
open SimpleGraph Finset Graph189CutCore Graph189CutMiddle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Even-distance budgets preclude a partition with only one candidate
crossing edge. The edge's existence follows from connectedness. -/
theorem no_single_crossing {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) (horder : 2*k+3 ≤ Fintype.card V)
    {L : Finset V} {p q : V} (hp : p ∈ L) (hq : q ∉ L)
    (cross : ∀ {u v : V}, u ∈ L → G.Adj u v → v ∉ L → u = p ∧ v = q) : False := by
  classical
  have leftSide : Side G q L :=
    ⟨⟨p,hp⟩,hq,fun hu he hv => (cross hu he hv).2⟩
  have hqc : q ∈ Lᶜ := mem_compl.mpr hq
  have rightSide : Side G p Lᶜ := by
    refine ⟨⟨q,hqc⟩,fun hh => (mem_compl.mp hh) hp,?_⟩
    intro u v hu he hv
    have hvL : v ∈ L := by
      by_contra hh
      exact hv (mem_compl.mpr hh)
    exact (cross hvL he.symm (mem_compl.mp hu)).1
  obtain ⟨a,ha,haq⟩ := leftSide.contact hc
  have hap : a = p := (cross ha haq hq).1
  have hpq : G.Adj p q := hap ▸ haq
  let E (u : V) := univ.filter (fun w => Even (G.dist u w))
  have cover : (univ : Finset V) ⊆ E p ∪ E q := by
    intro w _
    simp only [E, mem_union, mem_filter, mem_univ, true_and, Nat.even_iff]
    by_cases hw : w ∈ L
    · have hd := rightSide.dist_add hc hqc (fun hh => (mem_compl.mp hh) hw)
      rw [dist_eq_one_iff_adj.mpr hpq.symm] at hd
      omega
    · have hd := leftSide.dist_add hc hp hw
      rw [dist_eq_one_iff_adj.mpr hpq] at hd
      omega
  have sums := (card_le_card cover).trans (card_union_le (E p) (E q))
  rw [card_univ] at sums
  have hpc : (E p).card ≤ 1+k := hσ p
  have hqc' : (E q).card ≤ 1+k := hσ q
  omega

/-- At least two neighbors of a gate lie in the middle between opposite
sides of distinct gates. -/
theorem gate_middle_contacts [DecidableRel G.Adj] {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) (horder : 2*k+3 ≤ Fintype.card V)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) : 2 ≤ ((A ∪ B)ᶜ.filter (G.Adj c ·)).card := by
  classical
  let L := insert c A
  let M := (A ∪ B)ᶜ.filter (G.Adj c ·)
  have hcL : c ∈ L := mem_insert_self _ _
  have hdL : d ∉ L := by simp [L,hcd.symm,hdA]
  have classify {u v : V} (hu : u ∈ L) (he : G.Adj u v) (hv : v ∉ L) :
      u = c ∧ v ∈ M := by
    have hvA : v ∉ A := fun ha => hv (mem_insert_of_mem ha)
    have hvc : v ≠ c := fun hh => hv (hh.symm ▸ hcL)
    have huc : u = c := (mem_insert.mp hu).resolve_right
      (fun ha => hvc (hA.exit_eq ha he hvA))
    have hcv : G.Adj c v := huc ▸ he
    have hvB : v ∉ B := fun hb => hcd (hB.exit_eq hb hcv.symm hcB)
    exact ⟨huc,mem_filter.mpr ⟨mem_compl.mpr (fun hm => (mem_union.mp hm).elim hvA hvB),hcv⟩⟩
  obtain ⟨walk⟩ := hc c d
  obtain ⟨dart,_,hin,hout⟩ := walk.exists_boundary_dart (L : Set V) hcL hdL
  have first := classify hin dart.adj hout
  by_contra! small
  have single : M.card ≤ 1 := by change ((A ∪ B)ᶜ.filter (G.Adj c ·)).card ≤ 1; omega
  apply no_single_crossing hc hσ horder hcL hout
  intro u v hu he hv
  have hh := classify hu he hv
  exact ⟨hh.1,card_le_one.mp single v hh.2 dart.snd first.2⟩
private theorem saturated_side_contacts [DecidableRel G.Adj] {k : ℕ} {c : V}
    {A : Finset V} (hA : Side G c A) (ha : A.card = k)
    (high : ∀ x ∈ A, k ≤ G.degree x) {x : V} (hx : x ∈ A) : G.Adj c x := by
  have hsub : G.neighborFinset x ⊆ insert c (A.erase x) := by
    intro y hy
    have he : G.Adj x y := by simpa using hy
    by_cases hyA : y ∈ A
    · exact mem_insert_of_mem (mem_erase.mpr ⟨he.ne.symm,hyA⟩)
    · exact mem_insert.mpr (Or.inl (hA.exit_eq hx he hyA))
  have heq := eq_of_subset_of_card_le hsub (by
    rw [card_insert_of_notMem (fun hc => hA.outside (mem_of_mem_erase hc)),
      card_erase_of_mem hx,card_neighborFinset_eq_degree]
    have := high x hx
    have := card_pos.mpr (show A.Nonempty from ⟨x,hx⟩)
    omega)
  have hcx : c ∈ G.neighborFinset x := by rw [heq]; exact mem_insert_self _ _
  exact (show G.Adj x c by simpa using hcx).symm

private theorem no_middle_triangle [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) {u : V} (hu : u ∈ (A ∪ B)ᶜ)
    (huc : u ≠ c) (hud : u ≠ d) (hcu : G.Adj c u) (hdu : G.Adj d u)
    (hcd' : G.Adj c d) : False := by
  classical
  have hAB := separated_sides_disjoint hc hcd hA hB hdA hcB
  obtain ⟨ha2,hak,_⟩ := hA.card_bounds hc hσ horder hpair
  obtain ⟨_,hbk,_⟩ := hB.card_bounds hc hσ horder hpair
  let E (v : V) := univ.filter (fun x => Even (G.dist v x))
  have hcover : insert c (insert d (A ∪ B)) ⊆ E c ∪ E d := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_union_left _ (by simp [E])
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_union_right _ (by simp [E])
    simp only [E,mem_union,mem_filter,mem_univ,true_and,Nat.even_iff]
    rw [G.dist_comm (u := c) (v := x), G.dist_comm (u := d) (v := x)]
    rcases mem_union.mp hx with hx | hx
    · have hd := hA.dist_add hc hx hdA
      rw [dist_eq_one_iff_adj.mpr hcd'] at hd
      omega
    · have hd := hB.dist_add hc hx hcB
      rw [dist_eq_one_iff_adj.mpr hcd'.symm] at hd
      omega
  have hh := (card_le_card hcover).trans (card_union_le (E c) (E d))
  have hdc : d ∉ A ∪ B := by simp [hdA,hB.outside]
  have hcc : c ∉ insert d (A ∪ B) := by simp [hcd,hA.outside,hcB]
  rw [card_insert_of_notMem hcc,card_insert_of_notMem hdc,card_union_of_disjoint hAB] at hh
  have ec : (E c).card ≤ 1+k := hσ c
  have ed : (E d).card ≤ 1+k := hσ d
  have unA : u ∉ A := fun h => mem_compl.mp hu (mem_union_left _ h)
  have unB : u ∉ B := fun h => mem_compl.mp hu (mem_union_right _ h)
  have low := middle_vertices_low hc hσ horder hpair hcd hA hB hdA hcB hu huc hud
  have hAcontact {y} (hy : y ∈ A) : G.Adj c y :=
    saturated_side_contacts hA (by omega) (fun x hx =>
      (hpair x u (fun he => unA (he ▸ hx))).resolve_right (Nat.not_le.mpr low)) hy
  have hBcontact {y} (hy : y ∈ B) : G.Adj d y :=
    saturated_side_contacts hB (by omega) (fun x hx =>
      (hpair x u (fun he => unB (he ▸ hx))).resolve_right (Nat.not_le.mpr low)) hy
  have hs : insert u (A ∪ B) ⊆ E u := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp [E]
    · rcases mem_union.mp hy with ha | hb
      · simp [E,G.dist_comm (u:=u) (v:=y),hA.dist_add hc ha unA,
          dist_eq_one_iff_adj.mpr (hAcontact ha).symm,dist_eq_one_iff_adj.mpr hcu]
      · simp [E,G.dist_comm (u:=u) (v:=y),hB.dist_add hc hb unB,
          dist_eq_one_iff_adj.mpr (hBcontact hb).symm,dist_eq_one_iff_adj.mpr hdu]
  have huCap := (card_le_card hs).trans (hσ u)
  rw [card_insert_of_notMem (mem_compl.mp hu),card_union_of_disjoint hAB] at huCap
  omega

omit [Fintype V] in
private theorem fill_middle [DecidableRel G.Adj] {c : V} {Z : Finset V}
    (hcZ : c ∈ Z) (hz : Z.card ≤ 3) (hc : 2 ≤ (Z.filter (G.Adj c ·)).card) :
    Z.card = 3 ∧ ∀ x ∈ Z, x ≠ c → G.Adj c x := by
  have hs : Z.filter (G.Adj c ·) ⊆ Z.erase c := by
    intro x hx
    obtain ⟨hx,he⟩ := mem_filter.mp hx
    exact mem_erase.mpr ⟨he.ne.symm,hx⟩
  have ht := card_le_card hs
  rw [card_erase_of_mem hcZ] at ht
  have hfill := eq_of_subset_of_card_le hs (by rw [card_erase_of_mem hcZ]; omega)
  refine ⟨by omega,?_⟩
  intro x hx hxc
  have hm : x ∈ Z.filter (G.Adj c ·) := hfill ▸ mem_erase.mpr ⟨hxc,hx⟩
  exact (mem_filter.mp hm).2

/-- A large qualifying graph has at most one cut vertex. -/
theorem cut_vertices_equal [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcCut : ¬ (G.induce {v | v ≠ c}).Connected)
    (hdCut : ¬ (G.induce {v | v ≠ d}).Connected) : c = d := by
  classical
  by_contra hcd
  change c ≠ d at hcd
  obtain ⟨A,hA,hdA⟩ := side_away_from hcd hcCut
  obtain ⟨B,hB,hcB⟩ := side_away_from hcd.symm hdCut
  let Z := (A ∪ B)ᶜ
  have hZ := middle_card_le_three hc hσ horder hpair hcd hA hB hdA hcB
  have hzC : c ∈ Z := by simp [Z,hA.outside,hcB]
  have hzD : d ∈ Z := by simp [Z,hdA,hB.outside]
  have hCG := gate_middle_contacts hc hσ horder hcd hA hB hdA hcB
  have hDG := gate_middle_contacts hc hσ horder hcd.symm hB hA hcB hdA
  rw [union_comm B A] at hDG
  obtain ⟨hz,allC⟩ := fill_middle hzC hZ hCG
  obtain ⟨_,allD⟩ := fill_middle hzD hZ hDG
  have hm : d ∈ Z.erase c := mem_erase.mpr ⟨hcd.symm,hzD⟩
  have hp : 0 < ((Z.erase c).erase d).card := by
    rw [card_erase_of_mem hm,card_erase_of_mem hzC,hz]
    decide
  obtain ⟨u,hu⟩ := card_pos.mp hp
  obtain ⟨hud,hu⟩ := mem_erase.mp hu
  obtain ⟨huc,hu⟩ := mem_erase.mp hu
  exact no_middle_triangle hc hσ horder hpair hcd hA hB hdA hcB hu huc hud
    (allC u hu huc) (allD u hu hud) (allC d hzD hcd.symm)

#print axioms cut_vertices_equal
end Graph189CutUnique
