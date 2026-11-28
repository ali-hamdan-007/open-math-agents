import Graph189ResidualDoubleCharge
import Graph189CoSingleton
import Graph189PrivatePredecessor

namespace Graph189ResidualPrivatePort
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

omit [Nontrivial V] [DecidableRel G.Adj] in
theorem even_row {k : ℕ} (Y : Finset V) {a : V} (out : a ∉ Y)
    (cap : G.distEven a ≤ k+1) : (Y.filter fun y => Even (G.dist a y)).card ≤ k := by
  classical
  let E := univ.filter fun y => Even (G.dist a y)
  have self : a ∈ E := by simp [E]
  have sub : (Y.filter fun y => Even (G.dist a y)) ⊆ E.erase a := by
    intro y hy
    obtain ⟨ym,h⟩ := mem_filter.mp hy
    exact mem_erase.mpr ⟨fun e => out (e ▸ ym),mem_filter.mpr ⟨mem_univ _,h⟩⟩
  have h := card_le_card sub
  have e := card_erase_add_one self
  change E.card ≤ k+1 at cap
  omega

/-- Without a high private B port on a common label, every high B vertex
either sees a residual representative at even distance or has two different
labels at distance two. This counts the whole opposite high population in
one pass, retaining all residual exact-two incidences. -/
theorem double_cover (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (C : Finset V) (cs : C ⊆ S) (two : 2 ≤ (S \ C).card)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S \ C, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (common : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → ∀ i ∈ C, G.Adj a i)
    (single : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a \ C).card ≤ 1)
    (absent : ¬ ∃ i ∈ C, ∃ b ∈ B, G.secondSmallestDegree ≤ G.degree b ∧
      S.filter (G.Adj b) = {i}) :
    let Y := B.filter (fun y => G.secondSmallestDegree ≤ G.degree y)
    2*Y.card ≤ (2*(S \ C).card+C.card)*G.secondSmallestDegree +
      ∑ i ∈ S \ C, (Y.filter (fun y => G.dist i y = 2)).card := by
  classical
  let k := G.secondSmallestDegree
  let D := S \ C
  let Y := B.filter fun y => k ≤ G.degree y
  have ys : Y ⊆ B := filter_subset _ _
  have ds : D ⊆ S := sdiff_subset
  have has : D.Nonempty := card_pos.mp (by change 0 < (S \ C).card; omega)
  have get (i : V) : ∃ a, i ∈ D → a ∈ A ∧ k ≤ G.degree a ∧ G.Adj a i := by
    by_cases hi : i ∈ D
    · obtain ⟨a,ha,hk,ai⟩ := contacts i hi
      exact ⟨a,fun _ => ⟨ha,hk,ai⟩⟩
    · exact ⟨Classical.arbitrary V,fun h => (hi h).elim⟩
  choose f hf using get
  have label {i j : V} (hi : i ∈ D) (hj : j ∈ S) (edge : G.Adj (f i) j) :
      j ∈ C ∨ j = i := by
    by_cases jc : j ∈ C
    · exact Or.inl jc
    obtain ⟨ha,hh,ai⟩ := hf i hi
    exact Or.inr (card_le_one_iff.mp (single (f i) ha hh)
      (mem_sdiff.mpr ⟨mem_filter.mpr ⟨hj,edge⟩,jc⟩)
      (mem_sdiff.mpr ⟨mem_filter.mpr ⟨ds hi,ai⟩,(mem_sdiff.mp hi).2⟩))
  have diam {i y : V} (hi : i ∈ D) (hy : y ∈ Y) : G.dist (f i) y ≤ 4 := by
    have cf (x : V) : G.distEven x ≤ 1+k := by simpa only [Nat.add_comm 1] using cap x
    have h := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := f i) (v := y)).trans
      (diameter_le_five hc cf)
    by_contra! h'
    have five := five_endpoints hc cap (f i) y (by omega)
    exact five.elim (not_lt_of_ge (hf i hi).2.1) (not_lt_of_ge (mem_filter.mp hy).2)
  let near (i y : V) := G.dist i y = 2
  let rep (i y : V) := Even (G.dist (f i) y)
  have pay (y : V) (hy : y ∈ Y) : (∃ i ∈ D, rep i y) ∨
      2 ≤ (C.filter (fun i => near i y)).card+(D.filter (fun i => near i y)).card := by
    by_cases hit : ∃ i ∈ D, rep i y
    · exact Or.inl hit
    right
    by_contra! small
    let N := S.filter (fun i => near i y)
    have split : (D.filter (fun i => near i y)) ∪ (C.filter (fun i => near i y)) = N := by
      ext j
      simp only [N,D,mem_union,mem_filter,mem_sdiff]
      exact ⟨fun h => h.elim (fun z => ⟨z.1.1,z.2⟩) (fun z => ⟨cs z.1,z.2⟩),
        fun h => by by_cases w : j ∈ C
                    · exact Or.inr ⟨w,h.2⟩
                    · exact Or.inl ⟨⟨h.1,w⟩,h.2⟩⟩
    have dis : Disjoint (D.filter (fun i => near i y)) (C.filter (fun i => near i y)) := by
      apply Finset.disjoint_left.mpr
      intro j jd jc
      exact (mem_sdiff.mp (mem_filter.mp jd).1).2 (mem_filter.mp jc).1
    have size := congrArg Finset.card split
    rw [card_union_of_disjoint dis] at size
    have few : N.card ≤ 1 := by omega
    have np (j : V) (hj : j ∈ S) : ¬ G.Adj y j := by
      intro yj
      have seen {i : V} (hi : i ∈ D) (touch : G.Adj (f i) j) : False := by
        have de := Graph189PortDifference.cross_two hc sides (hf i hi).1 (ys hy) touch yj.symm
        exact hit ⟨i,hi,by simp [rep,de]⟩
      by_cases jc : j ∈ C
      · obtain ⟨i,hi⟩ := has
        exact seen hi (common (f i) (hf i hi).1 (hf i hi).2.1 j jc)
      · have ji : j ∈ D := mem_sdiff.mpr ⟨hj,jc⟩
        exact seen ji (hf j ji).2.2
    have none (j : V) (jc : j ∈ C) : ¬ near j y := by
      intro jn
      have only (a : V) (ha : a ∈ S) (ay : G.dist a y = 2) : a = j :=
        card_le_one_iff.mp few (mem_filter.mpr ⟨ha,ay⟩) (mem_filter.mpr ⟨cs jc,jn⟩)
      obtain ⟨b,hb,bh,_,jb,unique⟩ := Graph189PrivatePredecessor.high_private hc sides cap
        (cs jc) (ys hy) jn np only
      apply absent
      refine ⟨j,jc,b,hb,bh,?_⟩
      ext a
      constructor
      · intro hm
        obtain ⟨as,ba⟩ := mem_filter.mp hm
        exact mem_singleton.mpr (unique a as ba.symm)
      · intro hm
        obtain rfl := mem_singleton.mp hm
        exact mem_filter.mpr ⟨cs jc,jb.symm⟩
    have missed : ∃ i ∈ D, ¬ near i y := by
      by_contra! all
      have sub : D ⊆ N := fun i hi => mem_filter.mpr ⟨ds hi,all i hi⟩
      have h := (card_le_card sub).trans few
      change (S \ C).card ≤ 1 at h
      omega
    obtain ⟨i,hi,ny⟩ := missed
    have odd : ¬ Even (G.dist (f i) y) := fun h => hit ⟨i,hi,h⟩
    obtain ⟨j,hj,aj,jy⟩ := Graph189CoSingleton.odd_to_nonport hc sides (hf i hi).1 (ys hy)
      (fun a ha h => np a ha h.symm) (diam hi hy) odd
    rcases label hi hj aj with jc | rfl
    · exact none j jc jy
    · exact ny jy
  have rcap (i : V) (hi : i ∈ D) : (Y.filter (rep i)).card ≤ k :=
    even_row Y (fun hy => disjoint_left.mp sides.apart (hf i hi).1 (ys hy)) (cap _)
  have ccap (i : V) (hi : i ∈ C) : (Y.filter (near i)).card ≤ k := by
    have sub : Y.filter (near i) ⊆ Y.filter (fun y => Even (G.dist i y)) := by
      intro y hy
      obtain ⟨hy,n⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨hy,by change G.dist i y = 2 at n; simp [n]⟩
    exact (card_le_card sub).trans (even_row Y (fun hy => disjoint_left.mp sides.right_cut
      (ys hy) (cs hi)) (cap _))
  have result := Graph189ResidualDoubleCharge.budget C D Y rep near (k := k)
    (fun y hy => by convert! pay y hy using 4 <;> congr)
    (fun i hi => by convert! rcap i hi using 3)
    (fun i hi => by convert! ccap i hi using 3)
  convert! result using 4
  congr

#print axioms double_cover
end Graph189ResidualPrivatePort
