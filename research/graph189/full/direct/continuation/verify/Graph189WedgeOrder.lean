import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Graph189WedgeOrder
open Finset SimpleGraph
open scoped BigOperators
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

/-- Exact common-neighbor and even-layer overlaps in the wedge order count. -/
theorem wedge_order_with_overlap (hc : G.Connected) {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z)
    (_hyz : ¬G.Adj y z) {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) :
    let N := G.neighborFinset x
    let C := G.neighborFinset y ∩ G.neighborFinset z
    let E (v : V) := univ.filter (fun w => Even (G.dist v w))
    Fintype.card V + (k+1)*((N ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card) +
      (C.card-((C∩N).card+1)) + ((E y∪E z)∩E x).card ≤
        3*k+2+k*(G.degree x+G.distEven x)+G.degree y+G.degree z := by
  classical
  let E (v : V) := Finset.univ.filter (fun w => Even (G.dist v w))
  let X := G.neighborFinset x
  let Y := G.neighborFinset y
  let Z := G.neighborFinset z
  let S := Y ∪ Z
  let U := X ∪ S
  let Q := X \ S
  let C := Y ∩ Z
  let I := C ∩ X
  let A := E x \ S
  let T := univ.filter (fun w => 3 ≤ G.dist x w ∧ 3 ≤ G.dist y w ∧ 3 ≤ G.dist z w ∧ ¬Even (G.dist x w))
  have ecap (v : V) : (E v).card ≤ k+1 := cap v
  have memN (v w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w := G.mem_neighborFinset v w
  have near_even (a v w : V) (ha : G.Adj a v) (hw : G.Adj v w) (hn : ¬G.Adj a w) : w ∈ E a := by
    have h := hc.dist_triangle (u:=a) (v:=v) (w:=w)
    rw [dist_eq_one_iff_adj.mpr ha, dist_eq_one_iff_adj.mpr hw] at h
    have hne : G.dist a w ≠ 1 := fun hh => hn (dist_eq_one_iff_adj.mp hh)
    exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
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
  let row (a : V) := T.filter (fun w => G.Adj a w ∧ G.dist x w = G.dist x a+1)
  have rcap (a : V) : (row a).card ≤ k := by
    by_cases hn : (row a).Nonempty
    · obtain ⟨w,hw⟩ := hn
      obtain ⟨ht,_,he⟩ := mem_filter.mp hw
      have hh := (mem_filter.mp ht).2.1
      obtain ⟨b,hb,hab⟩ := predecessor (G := G) (x := x) (z := a) (j := G.dist x a-1) (by omega)
      have hs : insert b (row a) ⊆ E b := by
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
        · obtain ⟨_,hav,hvlen⟩ := mem_filter.mp hv
          have hlu := hc.dist_triangle (u := b) (v := a) (w := v)
          rw [dist_eq_one_iff_adj.mpr hab,dist_eq_one_iff_adj.mpr hav] at hlu
          have hlo := hc.dist_triangle (u := x) (v := b) (w := v)
          exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
      have hnb : b ∉ row a := by intro h; have := (mem_filter.mp h).2.2; omega
      have hsize := (card_le_card hs).trans (ecap b)
      rw [Finset.card_insert_of_notMem hnb] at hsize
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have tr : T ⊆ A.biUnion row := by
    intro w hw
    obtain ⟨hx,hy,hz,ho⟩ := (mem_filter.mp hw).2
    obtain ⟨a,ha,haw⟩ := predecessor (G := G) (x := x) (z := w) (j := G.dist x w-1) (by omega)
    have he : Even (G.dist x a) := by rw [Nat.even_iff] at ho ⊢; omega
    have naux (v : V) (hf : 3 ≤ G.dist v w) (hh : G.Adj v a) : False := by
      have ht := hc.dist_triangle (u := v) (v := a) (w := w)
      rw [dist_eq_one_iff_adj.mpr hh,dist_eq_one_iff_adj.mpr haw] at ht
      omega
    have hs : a ∉ S := by
      intro h
      rcases mem_union.mp h with yy|zz
      · exact naux y hy ((memN _ _).mp yy)
      · exact naux z hz ((memN _ _).mp zz)
    exact mem_biUnion.mpr ⟨a,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,he⟩,hs⟩,
      mem_filter.mpr ⟨hw,haw,by omega⟩⟩
  have tc : T.card ≤ k*A.card := calc
    T.card ≤ (A.biUnion row).card := card_le_card tr
    _ ≤ ∑ a ∈ A, (row a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, k := Finset.sum_le_sum fun a _ => rcap a
    _ = _ := by simp [Nat.mul_comm]
  have all : univ ⊆ (((E y ∪ E z) ∪ E x) ∪ I) ∪ T := by
    intro v _
    by_cases ey : Even (G.dist y v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,ey⟩))))
    by_cases ez : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ez⟩))))
    by_cases ex : Even (G.dist x v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ex⟩)))
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
  have count := card_le_card all
  rw [card_univ] at count
  have h1 := Finset.card_union_add_card_inter (E y) (E z)
  have h2 := Finset.card_union_add_card_inter (E y ∪ E z) (E x)
  have h3 := Finset.card_union_le ((E y ∪ E z) ∪ E x) I
  have h4 := Finset.card_union_le (((E y ∪ E z) ∪ E x) ∪ I) T
  have h5 := card_le_card qs
  have ecx := ecap x
  have ecy := ecap y
  have ecz := ecap z
  have hh : Fintype.card V + Q.card + (C.card-(I.card+1)) + ((E y∪E z)∩E x).card ≤ 3*k+2+C.card + k*A.card := by omega
  have hm := Nat.mul_le_mul_left k ac
  rw [Nat.mul_add, Nat.add_comm (G.distEven x) (G.degree x)] at hm
  change Fintype.card V + (k+1)*U.card + (C.card-(I.card+1)) + ((E y∪E z)∩E x).card ≤ _
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The order bound at an induced two-edge path with center x. -/
theorem wedge_order (hc : G.Connected) {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z)
    (_hyz : ¬G.Adj y z) {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) :
    Fintype.card V + (k+1) * ((G.neighborFinset x ∪
        (G.neighborFinset y ∪ G.neighborFinset z)).card) ≤
        3*k+2 + k*(G.degree x + G.distEven x) + G.degree y + G.degree z := by
  have bound := wedge_order_with_overlap hc hxy hxz _hyz cap
  dsimp only at bound
  omega

#print axioms wedge_order
end Graph189WedgeOrder
