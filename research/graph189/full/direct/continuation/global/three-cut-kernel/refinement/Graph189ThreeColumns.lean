import Graph189DebitedCutProduct
import Graph189CoSingleton
import Graph189PortDifference

open SimpleGraph Finset Graph189PositiveEvenCut
namespace Graph189ThreeColumns
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S X Y : Finset V}

/-- A high nonport on the large side has a separator label in its
second layer whenever the opposite high population exceeds k. -/
theorem nonport_second (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v,G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (xh : ∀ a∈X,G.secondSmallestDegree≤G.degree a)
    (many : G.secondSmallestDegree<X.card) {b : V} (hb : b∈B)
    (bh : G.secondSmallestDegree≤G.degree b) (np : ∀ i∈S,¬G.Adj i b) :
    ∃ i∈S,G.dist i b=2 := by
  classical
  by_contra missing
  have all : X⊆evenOthers G b := by
    intro a ha
    have ne : a≠b := fun e => disjoint_left.mp cut.apart (xs ha) (e ▸ hb)
    apply mem_even_others ne
    rw [dist_comm]
    by_contra odd
    have near := high_distance_four hc cap (xh a ha) bh
    obtain ⟨i,hi,_,d⟩ := Graph189CoSingleton.odd_to_nonport hc cut (xs ha) hb np near odd
    exact missing ⟨i,hi,d⟩
  have c := (card_le_card all).trans (even_others_card
    (show G.distEven b≤G.secondSmallestDegree+1 by have h := cap b; omega))
  omega

/-- Either the small-side contacts are private or every target is covered
by at most k+v ports together with the three second-layer columns. -/
theorem concentration (hc : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v,G.distEven v≤1+G.secondSmallestDegree)
    (xs : X⊆A) (ys : Y⊆B) (xh : ∀ a∈X,G.secondSmallestDegree≤G.degree a)
    (yh : ∀ b∈Y,G.secondSmallestDegree≤G.degree b)
    (many : G.secondSmallestDegree<X.card) (three : S.card=3) {v : ℕ}
    (q : ∀ i∈S,(Y.filter (G.Adj i)).card≤v) :
    (∑ i∈S,(X.filter (G.Adj i)).card)≤X.card ∨
      Y.card≤G.secondSmallestDegree+v+∑ i∈S,(Y.filter (fun b => G.dist i b=2)).card := by
  classical
  let supp (a : V) := S.filter (fun i => G.Adj i a)
  let col (i : V) := Y.filter (G.Adj i)
  let layer (i : V) := Y.filter (fun b => G.dist i b=2)
  by_cases privatePorts : ∀ a∈X,(supp a).card≤1
  · left
    have double : (∑ i∈S,(X.filter (G.Adj i)).card)=∑ a∈X,(supp a).card := by
      simp only [supp,card_eq_sum_ones,sum_filter]
      exact Finset.sum_comm
    rw [double]
    simpa using Finset.sum_le_sum privatePorts
  · push Not at privatePorts
    obtain ⟨a,ha,multiple⟩ := privatePorts
    obtain ⟨i,is,j,js,ne⟩ := Finset.one_lt_card.mp multiple
    obtain ⟨hi,ia⟩ := mem_filter.mp is
    obtain ⟨hj,ja⟩ := mem_filter.mp js
    let C : Finset V := {i,j}
    let D := S \ C
    have csub : C⊆S := insert_subset hi (singleton_subset_iff.mpr hj)
    have cs : C.card=2 := by simp [C,ne]
    have ds := card_sdiff_add_card_eq_card csub
    change D.card+C.card=S.card at ds
    have d : D.card=1 := by omega
    have close : col i ∪ col j⊆evenOthers G a := by
      intro b hb
      have one (l : V) (al : G.Adj a l) (member : b∈col l) : b∈evenOthers G a := by
        obtain ⟨bt,lb⟩ := mem_filter.mp member
        have ne' : b≠a := fun e => disjoint_left.mp cut.apart (xs ha) (e ▸ ys bt)
        have d' := Graph189PortDifference.cross_two hc cut (xs ha) (ys bt) al lb
        exact mem_even_others ne' (by simp [d'])
      exact (mem_union.mp hb).elim (one i ia.symm) (one j ja.symm)
    have both := (card_le_card close).trans (even_others_card
      (show G.distEven a≤G.secondSmallestDegree+1 by have h := cap a; omega))
    have rest : (D.biUnion col).card≤v := by
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _i∈D,v := Finset.sum_le_sum fun l hl => q l (mem_sdiff.mp hl).1
        _ = v := by simp [d]
    have incl : Y⊆((col i∪col j)∪D.biUnion col)∪S.biUnion layer := by
      intro b hb
      by_cases port : ∃ l∈S,G.Adj l b
      · obtain ⟨l,ls,lb⟩ := port
        have member : b∈col l := mem_filter.mpr ⟨hb,lb⟩
        apply mem_union_left
        by_cases lc : l∈C
        · have eq : l=i ∨ l=j := by simpa [C] using lc
          exact mem_union_left _ (eq.elim (fun h => mem_union_left _ (h ▸ member))
            (fun h => mem_union_right _ (h ▸ member)))
        · exact mem_union_right _ (mem_biUnion.mpr ⟨l,mem_sdiff.mpr ⟨ls,lc⟩,member⟩)
      · obtain ⟨l,ls,dist⟩ := nonport_second hc cut cap xs xh many (ys hb) (yh b hb)
          (fun l ls lb => port ⟨l,ls,lb⟩)
        exact mem_union_right _ (mem_biUnion.mpr ⟨l,ls,mem_filter.mpr ⟨hb,dist⟩⟩)
    have total := (card_le_card incl).trans (card_union_le _ _)
    have ports := card_union_le (col i∪col j) (D.biUnion col)
    have layers : (S.biUnion layer).card≤∑ i∈S,(layer i).card := card_biUnion_le
    right
    change Y.card≤G.secondSmallestDegree+v+∑ i∈S,(layer i).card
    omega

#print axioms nonport_second
#print axioms concentration
end Graph189ThreeColumns
