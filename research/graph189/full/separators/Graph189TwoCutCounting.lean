import Graph189DegreeTwoOuter
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Graph189TwoCutCounting
open SimpleGraph Graph189LowDegreeTwo Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Each contact at an anchor sees every contact belonging to a different component
at distance two. Summing this over the used labels bounds the external witness count. -/
theorem external_count {ι : Type*} [DecidableEq ι] (region : V → ι)
    (C : Finset V) (p : V) (k : ℕ)
    (hc : ∀ x ∈ C, G.Adj p x)
    (hn : ∀ x ∈ C, ∀ y ∈ C, region x ≠ region y → ¬ G.Adj x y)
    (cap : ∀ x : V, (univ.filter (fun y => G.dist x y = 2)).card ≤ k) :
    (C.image region).card*C.card ≤ (C.image region).card*k+C.card := by
  let L := C.image region
  let A (i : ι) := C.filter (fun x => region x = i)
  let O (i : ι) := C.filter (fun x => region x ≠ i)
  have partition (i : ι) : (A i).card + (O i).card = C.card :=
    Finset.card_filter_add_card_filter_not (s := C) (fun x => region x = i)
  have bound (i : ι) (hi : i ∈ L) : (O i).card ≤ k := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    refine (Finset.card_le_card (show O (region x) ⊆ univ.filter (fun y => G.dist x y = 2) from ?_)).trans (cap x)
    intro y hy
    obtain ⟨hyC,hyr⟩ := Finset.mem_filter.mp hy
    have hxy : x ≠ y := fun e => hyr (congrArg region e).symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      two_edges (hc x hx).symm (hc y hyC) hxy (hn x hx y hyC hyr.symm)⟩
  have hs : ∑ i ∈ L, C.card ≤ ∑ i ∈ L, (k+(A i).card) := by
    apply Finset.sum_le_sum
    intro i hi
    have := partition i
    have := bound i hi
    omega
  have hf : (∑ i ∈ L, (A i).card) = C.card :=
    (Finset.card_eq_sum_card_fiberwise (f := region) (s := C) (t := L)
      (fun x hx => Finset.mem_image_of_mem region hx)).symm
  simpa [Finset.sum_add_distrib,hf] using hs

/-- A high contact forces enough distance-two vertices inside the component.
If the contact misses the second anchor there is one additional internal slot. -/
theorem internal_count (I : Finset V) (p q x : V)
    (hx : x ∈ I) (hp : G.Adj p x)
    (hclosed : G.neighborFinset x ⊆ insert p (insert q I)) :
    let A := I.filter (G.Adj p)
    let D := I.filter (fun y => G.dist p y = 2)
    G.degree x + 1 ≤ A.card+D.card+2 ∧
      (¬ G.Adj x q → G.degree x ≤ A.card+D.card) := by
  classical
  let A := I.filter (G.Adj p)
  let D := I.filter (fun y => G.dist p y = 2)
  change G.degree x + 1 ≤ A.card+D.card+2 ∧
    (¬ G.Adj x q → G.degree x ≤ A.card+D.card)
  have hxA : x ∈ A := Finset.mem_filter.mpr ⟨hx,hp⟩
  have hpX : p ≠ x := G.ne_of_adj hp
  have internal (y : V) (hy : y ∈ I) (hyN : y ∈ G.neighborFinset x) (hne : y ≠ p) :
      y ∈ A.erase x ∪ D := by
    have hadj := (G.mem_neighborFinset x y).mp hyN
    by_cases hpY : G.Adj p y
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
        ⟨(G.ne_of_adj hadj).symm,Finset.mem_filter.mpr ⟨hy,hpY⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hy,two_edges hp hadj hne.symm hpY⟩)
  have hsub : G.neighborFinset x ⊆ insert p (insert q (A.erase x ∪ D)) := by
    intro y hy
    by_cases he : y = p
    · simp [he]
    by_cases hq : y = q
    · simp [hq]
    have hyI := ((Finset.mem_insert.mp (hclosed hy)).resolve_left he)
    have hy' := (Finset.mem_insert.mp hyI).resolve_left hq
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (internal y hy' hy he))
  have hs := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at hs
  have ha : 0 < A.card := Finset.card_pos.mpr ⟨x,hxA⟩
  have hUnion := Finset.card_union_le (A.erase x) D
  rw [Finset.card_erase_of_mem hxA] at hUnion
  have hpCard := Finset.card_insert_le p (insert q (A.erase x ∪ D))
  have hqCard := Finset.card_insert_le q (A.erase x ∪ D)
  refine ⟨by omega,?_⟩
  intro hnq
  have hsub' : G.neighborFinset x ⊆ insert p (A.erase x ∪ D) := by
    intro y hy
    by_cases he : y = p
    · simp [he]
    have hq : y ≠ q := fun e => hnq (e ▸ (G.mem_neighborFinset x y).mp hy)
    have hyI := ((Finset.mem_insert.mp (hclosed hy)).resolve_left he)
    have hy' := (Finset.mem_insert.mp hyI).resolve_left hq
    exact Finset.mem_insert_of_mem (internal y hy' hy he)
  have hs' := Finset.card_le_card hsub'
  rw [G.card_neighborFinset_eq_degree] at hs'
  have hpCard' := Finset.card_insert_le p (A.erase x ∪ D)
  omega

/-- The sum of the local high-contact bounds over declared regions. -/
theorem internal_count_sum {ι : Type*} [DecidableEq ι] (region : V → ι)
    (C : Finset V) (L : Finset ι) (p q : V) (k : ℕ)
    (chosen : ∀ i ∈ L, ∃ x ∈ C, region x = i ∧ G.Adj p x ∧ k ≤ G.degree x)
    (hn : ∀ x ∈ C, ∀ y ∈ C, region x ≠ region y → ¬ G.Adj x y)
    (hclosed : ∀ x ∈ C, G.neighborFinset x ⊆ insert p (insert q C))
    (cap : (univ.filter (fun y => G.dist p y = 2)).card ≤ k) :
    L.card*(k-1) ≤ (C.filter (G.Adj p)).card+k := by
  classical
  let A := C.filter (G.Adj p)
  let D := C.filter (fun y => G.dist p y = 2)
  have degreeBound (i : ι) (hi : i ∈ L) :
      k-1 ≤ (A.filter (fun x => region x = i)).card +
        (D.filter (fun x => region x = i)).card := by
    obtain ⟨x,hx,hxi,hpx,hdeg⟩ := chosen i hi
    let I := C.filter (fun y => region y = i)
    have hxI : x ∈ I := Finset.mem_filter.mpr ⟨hx,hxi⟩
    have hsub : G.neighborFinset x ⊆ insert p (insert q I) := by
      intro y hy
      rcases Finset.mem_insert.mp (hclosed x hx hy) with rfl | hh
      · simp
      rcases Finset.mem_insert.mp hh with rfl | hyC
      · simp
      have hxy : region x = region y := by
        by_contra hd
        exact hn x hx y hyC hd ((G.mem_neighborFinset x y).mp hy)
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨hyC,hxy.symm.trans hxi⟩))
    have hb := (internal_count I p q x hxI hpx hsub).1
    have hA : I.filter (G.Adj p) = A.filter (fun x => region x = i) := by
      ext y
      simp [I,A]
      tauto
    have hD : I.filter (fun y => G.dist p y = 2) = D.filter (fun x => region x = i) := by
      ext y
      simp [I,D]
      tauto
    change G.degree x + 1 ≤ (I.filter (G.Adj p)).card +
      (I.filter (fun y => G.dist p y = 2)).card + 2 at hb
    rw [hA,hD] at hb
    omega
  have hs : ∑ i ∈ L, (k-1) ≤ ∑ i ∈ L,
      ((A.filter (fun x => region x = i)).card +
        (D.filter (fun x => region x = i)).card) :=
    Finset.sum_le_sum degreeBound
  rw [Finset.sum_add_distrib,Finset.sum_card_fiberwise_eq_card_filter A L region,
    Finset.sum_card_fiberwise_eq_card_filter D L region] at hs
  have hA := Finset.card_le_card (Finset.filter_subset (fun x => region x ∈ L) A)
  have hD := Finset.card_le_card (Finset.filter_subset (fun x => region x ∈ L) D)
  have hd : D.card ≤ k := (Finset.card_le_card (by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2⟩ :
      D ⊆ univ.filter (fun y => G.dist p y = 2))).trans cap
  change L.card*(k-1) ≤ A.card+k
  simp only [Finset.sum_const,Nat.nsmul_eq_mul] at hs
  omega

#print axioms external_count
#print axioms internal_count
#print axioms internal_count_sum
end Graph189TwoCutCounting
