import Graph189MatchedRows
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open Finset SimpleGraph
open scoped BigOperators

namespace Graph189MatchedWedge

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem predecessor {x z : V} {j : ℕ} (hz : G.dist x z = j+1) :
    ∃ a, G.dist x a = j ∧ G.Adj a z := by
  have hr : G.dist z x = j+1 := by rwa [dist_comm]
  have hp : G.Reachable z x := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hp.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at hz
  | cons he tail =>
    rename_i a
    have ht : tail.length = j := by rw [Walk.length_cons,hr] at hlen; omega
    have hh : G.dist x a ≤ j := by rw [dist_comm]; exact ht ▸ G.dist_le tail
    have := he.diff_dist_adj (u := x)
    exact ⟨a,by omega,he.symm⟩

/-- The matched-penultimate wedge estimate. The hypothesis on far points follows from
high-pair distance at most four and the unique possible vertex below degree `k`.
The cardinality of the neighborhood union keeps the signed defect implicit. -/
theorem wedge_order_matched (hc : G.Connected) {x y z : V} (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : y ≠ z) {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1)
    (far : ∀ a b : V,
      (5 ≤ G.dist x a ∧ 5 ≤ G.dist y a ∧ 5 ≤ G.dist z a) →
      (5 ≤ G.dist x b ∧ 5 ≤ G.dist y b ∧ 5 ≤ G.dist z b) → a = b) :
    ∃ t ε : ℕ, ε ≤ 1 ∧
      t + ε + (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card ≤
        G.degree x + G.distEven x ∧
      Fintype.card V + (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card +
        t*(t+1) ≤ 3*k+2 + G.degree y + G.degree z + t*k + ε := by
  classical
  let _ : Nonempty V := ⟨x⟩
  let E := Graph189MatchedRows.evenSet G
  let X := G.neighborFinset x
  let Y := G.neighborFinset y
  let Z := G.neighborFinset z
  let S := Y ∪ Z
  let U := X ∪ S
  let Q := X \ S
  let C := Y ∩ Z
  let I := C ∩ X
  let A := E x \ S
  let T := univ.filter (fun w => 3 ≤ G.dist x w ∧ G.dist y w = G.dist x w ∧
    G.dist z w = G.dist x w ∧ ¬Even (G.dist x w))
  let targets := T.filter (fun w => G.dist x w = 3)
  let rem := T \ targets
  have ecap (v : V) : (E v).card ≤ k+1 := cap v
  have memN (v w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w := G.mem_neighborFinset v w
  have near_even (a v w : V) (ha : G.Adj a v) (hw : G.Adj v w) (hn : ¬G.Adj a w) : w ∈ E a :=
    Graph189MatchedRows.evenSet_of_two_edges G hc ha hw hn
  have scset : S \ X ⊆ E x := by
    intro v hv
    obtain ⟨hs,hn⟩ := mem_sdiff.mp hv
    have hna : ¬G.Adj x v := fun hh => hn ((memN _ _).mpr hh)
    rcases mem_union.mp hs with hy|hz
    · exact near_even x y v hxy ((memN _ _).mp hy) hna
    · exact near_even x z v hxz ((memN _ _).mp hz) hna
  have ac : A.card + U.card ≤ G.distEven x + G.degree x := by
    have dj : Disjoint A (S \ X) := by
      rw [Finset.disjoint_left]
      exact fun _ ha hb => (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
    have sub : A ∪ (S \ X) ⊆ E x := by
      intro v hv
      exact (mem_union.mp hv).elim (fun ha => (mem_sdiff.mp ha).1) (fun hb => scset hb)
    have h := card_le_card sub
    rw [card_union_of_disjoint dj] at h
    have hc1 := Finset.card_sdiff_add_card_inter S X
    have hc2 := Finset.card_union_add_card_inter X S
    rw [Finset.inter_comm S X] at hc1
    have hd : X.card = G.degree x := G.card_neighborFinset_eq_degree x
    change _ ≤ G.distEven x at h
    change _ + (X ∪ S).card ≤ _
    omega
  have qc : Q.card + G.degree y + G.degree z = U.card + C.card := by
    have h1 := Finset.card_sdiff_add_card_inter X S
    have h2 := Finset.card_union_add_card_inter X S
    have h3 := Finset.card_union_add_card_inter Y Z
    have hy : Y.card = G.degree y := G.card_neighborFinset_eq_degree y
    have hz : Z.card = G.degree z := G.card_neighborFinset_eq_degree z
    change S.card+C.card=Y.card+Z.card at h3
    change (X \ S).card+_+_=(X ∪ S).card+C.card
    omega
  have ics : I.card + 1 ≤ C.card := by
    have notI : x ∉ I := fun h => (G.loopless.irrefl x) ((memN _ _).mp (mem_inter.mp h).2)
    have sub : insert x I ⊆ C := by
      intro b hb
      rcases mem_insert.mp hb with rfl|hh
      · exact mem_inter.mpr ⟨(memN _ _).mpr hxy.symm,(memN _ _).mpr hxz.symm⟩
      · exact (mem_inter.mp hh).1
    have hh := card_le_card sub
    rwa [card_insert_of_notMem notI] at hh
  have qs : Q ⊆ E y ∩ E z := by
    intro w hw
    obtain ⟨hh,hn⟩ := mem_sdiff.mp hw
    exact mem_inter.mpr ⟨near_even y x w hxy.symm ((memN _ _).mp hh)
      (fun h => hn (mem_union_left _ ((memN _ _).mpr h))),
      near_even z x w hxz.symm ((memN _ _).mp hh)
      (fun h => hn (mem_union_right _ ((memN _ _).mpr h)))⟩
  have all : univ ⊆ (((E y ∪ E z) ∪ E x) ∪ I) ∪ T := by
    intro v _
    by_cases ey : Even (G.dist y v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ ((show v ∈ E y from mem_filter.mpr ⟨mem_univ _,ey⟩)))))
    by_cases ez : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ ((show v ∈ E z from mem_filter.mpr ⟨mem_univ _,ez⟩)))))
    by_cases ex : Even (G.dist x v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ ((show v ∈ E x from mem_filter.mpr ⟨mem_univ _,ex⟩))))
    have y1 := hc.dist_triangle (u:=x) (v:=y) (w:=v)
    have y2 := hc.dist_triangle (u:=y) (v:=x) (w:=v)
    have z1 := hc.dist_triangle (u:=x) (v:=z) (w:=v)
    have z2 := hc.dist_triangle (u:=z) (v:=x) (w:=v)
    rw [dist_eq_one_iff_adj.mpr hxy] at y1
    rw [dist_eq_one_iff_adj.mpr hxy.symm] at y2
    rw [dist_eq_one_iff_adj.mpr hxz] at z1
    rw [dist_eq_one_iff_adj.mpr hxz.symm] at z2
    have ox := ex
    rw [Nat.even_iff] at ox ey ez
    by_cases hl : 3 ≤ G.dist x v
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hl,by omega,by omega,ex⟩)
    · have nx (a : V) (h : G.dist a v = 1) := (memN a v).mpr (dist_eq_one_iff_adj.mp h)
      exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨mem_inter.mpr ⟨nx y (by omega),nx z (by omega)⟩,nx x (by omega)⟩))
  have hrem_props (a : V) (ha : a ∈ rem) : 5 ≤ G.dist x a ∧ 5 ≤ G.dist y a ∧ 5 ≤ G.dist z a := by
    obtain ⟨hT,hn⟩ := mem_sdiff.mp ha
    obtain ⟨hthree,hey,hez,hodd⟩ := (mem_filter.mp hT).2
    have hneq : G.dist x a ≠ 3 := fun h => hn (mem_filter.mpr ⟨hT,h⟩)
    rw [Nat.even_iff] at hodd
    omega
  have hrem : rem.card ≤ 1 := card_le_one.mpr fun a ha b hb =>
    far a b (hrem_props a ha) (hrem_props b hb)
  have has_column (v : V) (hv : v ∈ targets) : ∃ a, G.dist x a = 2 ∧ G.Adj a v :=
    predecessor (G := G) ((mem_filter.mp hv).2 : G.dist x v = 2+1)
  let column (v : V) := if hv : v ∈ targets then (has_column v hv).choose else x
  have column_props (v : V) (hv : v ∈ targets) : G.dist x (column v) = 2 ∧ G.Adj (column v) v := by
    simpa only [column,dif_pos hv] using (has_column v hv).choose_spec
  have avoid (a v : V) (hv : v ∈ T) (hav : G.Adj a v) : ¬G.Adj y a ∧ ¬G.Adj z a := by
    obtain ⟨hthree,hey,hez,_⟩ := (mem_filter.mp hv).2
    constructor
    · intro hya
      have h := hc.dist_triangle (u:=y) (v:=a) (w:=v)
      rw [dist_eq_one_iff_adj.mpr hya,dist_eq_one_iff_adj.mpr hav] at h
      omega
    · intro hza
      have h := hc.dist_triangle (u:=z) (v:=a) (w:=v)
      rw [dist_eq_one_iff_adj.mpr hza,dist_eq_one_iff_adj.mpr hav] at h
      omega
  have accessible (v : V) (hv : v ∈ targets) : ∃ b ∈ X, G.Adj b (column v) := by
    obtain ⟨b,hb,hba⟩ := predecessor (G:=G) ((column_props v hv).1 : G.dist x (column v) = 1+1)
    exact ⟨b,(memN x b).mpr (dist_eq_one_iff_adj.mp hb),hba⟩
  obtain ⟨M,group,rep,hm,hfst,hsnd,hgroup,hrep⟩ :=
    Graph189MatchingGroups.exists_matching_groups X targets column G.Adj accessible
  have match_props (p : V × V) (hp : p ∈ M) : G.dist x p.1 = 1 ∧ G.dist x p.2 = 2 ∧
      G.Adj p.1 p.2 ∧ ¬G.Adj y p.2 ∧ ¬G.Adj z p.2 := by
    obtain ⟨hb,ha,hba⟩ := hm p hp
    obtain ⟨v,hv,he⟩ : ∃ v ∈ targets, column v = p.2 := mem_image.mp ha
    have hc' := column_props v hv
    have havoid := avoid _ _ (mem_filter.mp hv).1 hc'.2
    rw [he] at hc' havoid
    exact ⟨dist_eq_one_iff_adj.mpr ((memN _ _).mp hb),hc'.1,hba,havoid⟩
  have row_bound := Graph189MatchedRows.matched_rows_le G hc hxy hxz hyz cap targets column M group rep
    (fun v hv => ⟨(mem_filter.mp hv).2,(column_props v hv).2⟩) match_props hfst hsnd hgroup hrep
  let M1 := M.filter (fun p => G.Adj p.1 y)
  let M2 := M.filter (fun p => G.Adj p.1 z)
  let D1 := M1.image Prod.snd
  let D2 := M2.image Prod.snd
  have col_in_A (p : V × V) (hp : p ∈ M) : p.2 ∈ A := by
    obtain ⟨_,hda,_,hny,hnz⟩ := match_props p hp
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, by simp [hda]⟩,
      fun hs => (mem_union.mp hs).elim (fun hh => hny ((memN _ _).mp hh)) (fun hh => hnz ((memN _ _).mp hh))⟩
  have D1sub : D1 ⊆ E x ∩ E y := by
    intro v hv
    obtain ⟨p,hm1,rfl⟩ := mem_image.mp hv
    obtain ⟨hp,hby⟩ := mem_filter.mp hm1
    have hp' := match_props p hp
    exact mem_inter.mpr ⟨(mem_sdiff.mp (col_in_A p hp)).1,near_even _ _ _ hby.symm hp'.2.2.1 hp'.2.2.2.1⟩
  have D2sub : D2 ⊆ E x ∩ E z := by
    intro v hv
    obtain ⟨p,hm2,rfl⟩ := mem_image.mp hv
    obtain ⟨hp,hbz⟩ := mem_filter.mp hm2
    have hp' := match_props p hp
    exact mem_inter.mpr ⟨(mem_sdiff.mp (col_in_A p hp)).1,near_even _ _ _ hbz.symm hp'.2.2.1 hp'.2.2.2.2⟩
  have QD : Disjoint Q (D1 ∩ D2) := by
    rw [Finset.disjoint_left]
    intro v hq hD
    obtain ⟨p,hp,he⟩ := mem_image.mp (mem_inter.mp hD).1
    have hl : G.dist x v = 1 := dist_eq_one_iff_adj.mpr ((memN _ _).mp (mem_sdiff.mp hq).1)
    have hl' := (match_props p (mem_filter.mp hp).1).2.1
    rw [he] at hl'
    omega
  have hcredits : ∑ p ∈ M, Graph189MatchedRows.credit G y z p = D1.card + D2.card := by
    have inj1 : Set.InjOn Prod.snd (M1 : Set (V × V)) := by
      intro a ha b hb he
      exact hsnd (mem_filter.mp (show a ∈ M1 from ha)).1 (mem_filter.mp (show b ∈ M1 from hb)).1 he
    have inj2 : Set.InjOn Prod.snd (M2 : Set (V × V)) := by
      intro a ha b hb he
      exact hsnd (mem_filter.mp (show a ∈ M2 from ha)).1 (mem_filter.mp (show b ∈ M2 from hb)).1 he
    change _ = (M1.image Prod.snd).card + (M2.image Prod.snd).card
    rw [card_image_of_injOn inj1,card_image_of_injOn inj2]
    simp only [M1,M2,Graph189MatchedRows.credit,Finset.card_filter,Finset.sum_add_distrib]
  have dupl := Graph189MatchedCharging.union_add_credits_le (E x) (E y) (E z) Q D1 D2 qs D1sub D2sub QD
  let cols := M.image Prod.snd
  have cols_size : cols.card = M.card := card_image_of_injOn hsnd
  have cols_sub : cols ⊆ A := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
    exact col_in_A p hp
  have capacity : M.card + rem.card ≤ A.card := by
    by_cases hR : rem.Nonempty
    · obtain ⟨v,hv⟩ := hR
      have hT := (mem_sdiff.mp hv).1
      have hvd := (hrem_props v hv).1
      obtain ⟨a,ha,hav⟩ := predecessor (G:=G) (x:=x) (z:=v) (j:=G.dist x v-1) (by omega)
      have hd := (mem_filter.mp hT).2.2.2.2
      have hea : Even (G.dist x a) := by rw [Nat.even_iff] at hd ⊢; omega
      obtain ⟨hny,hnz⟩ := avoid a v hT hav
      have hA : a ∈ A := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,hea⟩,
        fun hs => (mem_union.mp hs).elim (fun hh => hny ((memN _ _).mp hh)) (fun hh => hnz ((memN _ _).mp hh))⟩
      have hnot : a ∉ cols := by
        intro hh
        obtain ⟨p,hp,he⟩ := mem_image.mp hh
        have hcol := (match_props p hp).2.1
        rw [he] at hcol
        omega
      have h := card_le_card (insert_subset hA cols_sub)
      rw [card_insert_of_notMem hnot,cols_size] at h
      omega
    · have h := card_le_card cols_sub
      rw [cols_size] at h
      rw [not_nonempty_iff_eq_empty.mp hR]
      simpa using h
  refine ⟨M.card,rem.card,hrem,?_,?_⟩
  · change M.card + rem.card + U.card ≤ G.degree x + G.distEven x
    omega
  have count := card_le_card all
  rw [card_univ] at count
  have hI := Finset.card_union_le ((E y ∪ E z) ∪ E x) I
  have hT := Finset.card_union_le (((E y ∪ E z) ∪ E x) ∪ I) T
  have hsplit : rem.card + targets.card = T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  rw [hcredits] at row_bound
  have hcx := ecap x
  have hcy := ecap y
  have hcz := ecap z
  change Fintype.card V + U.card + M.card*(M.card+1) ≤ _
  omega

#print axioms wedge_order_matched
end Graph189MatchedWedge
