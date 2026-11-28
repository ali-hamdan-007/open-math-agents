import Graph189TwoCutLayout

namespace Graph189TwoCutSaturatedGate
open Finset SimpleGraph Graph189PositiveEvenCut
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B : Finset V} {p q y : V}

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem two_mem (hc : G.Connected) {x a z : V} (ne : x≠z)
    (no : ¬G.Adj x z) (xa : G.Adj x a) (az : G.Adj a z) : z∈evenOthers G x := by
  have lo := (hc x z).one_lt_dist_of_ne_of_not_adj ne no
  have hi := G.dist_le (Walk.cons xa (.cons az .nil))
  change G.dist x z≤2 at hi
  exact mem_even_others ne.symm (by rw [show G.dist x z=2 by omega]; exact ⟨1,rfl⟩)

omit [Nontrivial V] in
/-- A private nonuniversal contact with one unused even place gives a unique
internal gate. Two contacts of the opposite label ensure a nonempty far arm.
Neither arm touches the anchor on the opposite side of the gate. -/
theorem build_private (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q})
    (connected : (G.induce (B:Set V)).Connected)
    (yb : y∈B) (yp : G.Adj y p)
    (contacts : (A.filter (G.Adj p)).card+1=G.secondSmallestDegree)
    (notUniversal : ∃ x∈B, x≠y ∧ ¬G.Adj y x)
    (yq : ¬G.Adj y q) (oppositePorts : 2≤(B.filter (G.Adj q)).card) :
    ∃ L : Graph189TwoCutLayout.Layout G A B p y, ∀ u∈L.U, ¬G.Adj u q := by
  classical
  let U := B.filter (fun v => v=y ∨ G.Adj y v)
  let P := A.filter (G.Adj p)
  obtain ⟨x,xb,notY,notAdj⟩ := notUniversal
  obtain ⟨path⟩ := connected (⟨y,yb⟩ : (B : Set V)) ⟨x,xb⟩
  obtain ⟨u,w,uNear,wFar,uw,_⟩ := Graph189CutSides.walk_exits
    (G:=G.induce (B:Set V)) (fun v => v.val=y ∨ G.Adj y v.val) path
    (Or.inl rfl) (not_or.mpr ⟨notY,notAdj⟩)
  let g := w.val
  have gb : g∈B := w.property
  have ug : G.Adj u.val g := uw
  have yg : ¬G.Adj y g := (not_or.mp wFar).2
  have gne : y≠g := fun eq => (not_or.mp wFar).1 eq.symm
  have yu : G.Adj y u.val := uNear.elim (fun eq => False.elim (yg (eq ▸ ug))) id
  have gU : g∉U := fun h => wFar (mem_filter.mp h).2
  let W := B \ insert g U
  have gW : g∉W := fun h => (mem_sdiff.mp h).2 (mem_insert_self _ _)
  have split : B=insert g (U∪W) := by
    ext v
    constructor
    · intro vb
      by_cases eq : v=g
      · exact mem_insert.mpr (Or.inl eq)
      by_cases hu : v∈U
      · exact mem_insert_of_mem (mem_union_left _ hu)
      · exact mem_insert_of_mem (mem_union_right _
          (mem_sdiff.mpr ⟨vb,fun h => (mem_insert.mp h).elim eq hu⟩))
    · intro hv
      rcases mem_insert.mp hv with rfl|hv
      · exact gb
      rcases mem_union.mp hv with hu|hw
      · exact (mem_filter.mp hu).1
      · exact (mem_sdiff.mp hw).1
  have ga : g∉P := fun h => disjoint_left.mp sides.apart (mem_filter.mp h).1 gb
  have row : evenOthers G y=insert g P := by
    have sub : insert g P⊆evenOthers G y := by
      intro v hv
      rcases mem_insert.mp hv with rfl|hp
      · exact two_mem hc gne yg yu ug
      obtain ⟨va,vp⟩ := mem_filter.mp hp
      exact two_mem hc (fun eq => disjoint_left.mp sides.apart va (eq ▸ yb))
        (fun e => sides.no_cross v va y yb e.symm) yp vp
    have size := even_others_card (by simpa only [Nat.add_comm 1] using cap y)
    have count := card_insert_of_notMem ga
    change P.card+1=G.secondSmallestDegree at contacts
    exact (eq_of_subset_of_card_le sub (by omega)).symm
  have qa : q∉A := fun h => disjoint_left.mp sides.left_cut h (by simp)
  have qb : q∉B := fun h => disjoint_left.mp sides.right_cut h (by simp)
  have neq : y≠q := fun eq => qb (eq ▸ yb)
  have qOut : q∉evenOthers G y := by
    rw [row]
    intro h
    rcases mem_insert.mp h with h|h
    · exact qb (h.symm ▸ gb)
    · exact qa (mem_filter.mp h).1
  have qNonneighbor (v : V) (vq : G.Adj v q) : ¬G.Adj y v := by
    intro yv
    exact qOut (two_mem hc neq yq yv vq)
  have qU (v : V) (vu : v∈U) : ¬G.Adj v q := by
    intro vq
    rcases (mem_filter.mp vu).2 with rfl|yv
    · exact yq vq
    · exact qNonneighbor v vq yv
  obtain ⟨v,hv,t,ht,vt⟩ := one_lt_card.mp
    (show 1<(B.filter (G.Adj q)).card by omega)
  obtain ⟨z,zb,zq,zg⟩ : ∃ z∈B, G.Adj z q ∧ z≠g := by
    by_cases eq : v=g
    · exact ⟨t,(mem_filter.mp ht).1,(mem_filter.mp ht).2.symm,fun h => vt (eq.trans h.symm)⟩
    · exact ⟨v,(mem_filter.mp hv).1,(mem_filter.mp hv).2.symm,eq⟩
  have nonempty : W.Nonempty :=
    ⟨z,mem_sdiff.mpr ⟨zb,fun h => (mem_insert.mp h).elim zg (fun hu => qU z hu zq)⟩⟩
  have noW (v : V) (vw : v∈W) : v∉evenOthers G y := by
    rw [row]
    intro h
    rcases mem_insert.mp h with vg|vp
    · exact gW (vg ▸ vw)
    · exact disjoint_left.mp sides.apart (mem_filter.mp vp).1 (mem_sdiff.mp vw).1
  have miss (v : V) (vw : v∈W) : y≠v ∧ ¬G.Adj y v := by
    have noU : v∉U := fun h => (mem_sdiff.mp vw).2 (mem_insert_of_mem h)
    have out : ¬(v=y ∨ G.Adj y v) :=
      fun h => noU (mem_filter.mpr ⟨(mem_sdiff.mp vw).1,h⟩)
    exact ⟨fun eq => (not_or.mp out).1 eq.symm,(not_or.mp out).2⟩
  refine ⟨⟨U,W,g,u.val,split,?_,gU,gW,nonempty,mem_filter.mpr ⟨yb,Or.inl rfl⟩,
    mem_filter.mpr ⟨u.property,uNear⟩,yu,ug,?_,?_,?_,row⟩,qU⟩
  · apply Finset.disjoint_left.mpr
    intro a hu hw
    exact (mem_sdiff.mp hw).2 (mem_insert_of_mem hu)
  · intro a au b bw ab
    rcases (mem_filter.mp au).2 with rfl|ya
    · exact (miss b bw).2 ab
    · exact noW b bw (two_mem hc (miss b bw).1 (miss b bw).2 ya ab)
  · intro b bw bp
    exact noW b bw (two_mem hc (miss b bw).1 (miss b bw).2 yp bp.symm)
  · exact fun v hv => (mem_filter.mp hv).2

variable (L : Graph189TwoCutLayout.Layout G A B p y)

omit [Nontrivial V] in
/-- The near arm is another genuine two-cut when it has no contact with
the opposite original anchor. -/
theorem near_recut (sides : Graph189CutSides.CutSides G A B {q,p}) (diff : q≠p)
    (noQ : ∀ u∈L.U, ¬G.Adj u q) :
    Graph189CutSides.CutSides G L.U (insert q (A∪L.W)) {p,L.gate} := by
  classical
  have ps : q∈({q,p}:Finset V) := by simp
  have qs : p∈({q,p}:Finset V) := by simp
  have pb : q∉B := fun hp => disjoint_left.mp sides.right_cut hp ps
  have qb : p∉B := fun hq => disjoint_left.mp sides.right_cut hq qs
  refine ⟨⟨y,L.yU⟩,⟨q,mem_insert_self _ _⟩,?_,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hw hr
    rcases mem_insert.mp hr with rfl|hr
    · exact pb (L.uSub hw)
    rcases mem_union.mp hr with ha|hu
    · exact disjoint_left.mp sides.apart ha (L.uSub hw)
    · exact disjoint_left.mp L.apart hw hu
  · apply Finset.disjoint_left.mpr
    intro v hw ht
    rcases (show v=p ∨ v=L.gate by simpa using ht) with rfl|rfl
    · exact qb (L.uSub hw)
    · exact L.gateU hw
  · apply Finset.disjoint_left.mpr
    intro v hr ht
    rcases (show v=p ∨ v=L.gate by simpa using ht) with hq|hg
    · subst v
      rcases mem_insert.mp hr with eq|hr
      · exact diff eq.symm
      rcases mem_union.mp hr with ha|hu
      · exact disjoint_left.mp sides.left_cut ha qs
      · exact qb (L.wSub hu)
    · subst v
      rcases mem_insert.mp hr with eq|hr
      · exact pb (eq ▸ L.gate_mem)
      rcases mem_union.mp hr with ha|hu
      · exact disjoint_left.mp sides.apart ha L.gate_mem
      · exact L.gateW hu
  · intro v
    rcases sides.cover v with va|vb|vs
    · exact Or.inr (Or.inl (mem_insert_of_mem (mem_union_left _ va)))
    · rw [L.split] at vb
      rcases mem_insert.mp vb with rfl|vb
      · exact Or.inr (Or.inr (by simp))
      rcases mem_union.mp vb with vu|vw
      · exact Or.inr (Or.inl (mem_insert_of_mem (mem_union_right _ vu)))
      · exact Or.inl vw
    · rcases (show v=q ∨ v=p by simpa using vs) with rfl|rfl
      · exact Or.inr (Or.inl (mem_insert_self _ _))
      · exact Or.inr (Or.inr (by simp))
  · intro w hw v hv edge
    rcases mem_insert.mp hv with rfl|hv
    · exact noQ w hw edge
    rcases mem_union.mp hv with va|vu
    · exact sides.no_cross v va w (L.uSub hw) edge.symm
    · exact L.noCross w hw v vu edge


omit [Nontrivial V] in
/-- Both arms inherit the global minimum-side bound after recutting. -/
theorem arm_census (sides : Graph189CutSides.CutSides G A B {p,q}) (different : p≠q)
    (noQ : ∀ u∈L.U, ¬G.Adj u q)
    (least : ∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) :
    A.card≤L.U.card ∧ A.card≤L.W.card ∧ B.card=L.U.card+L.W.card+1 := by
  have gp : L.gate≠p := fun h => disjoint_left.mp sides.right_cut (h ▸ L.gate_mem) (by simp)
  have gq : L.gate≠q := fun h => disjoint_left.mp sides.right_cut (h ▸ L.gate_mem) (by simp)
  have swapped : Graph189CutSides.CutSides G A B {q,p} := by
    simpa only [Finset.pair_comm] using sides
  have near := least _ _ _ (near_recut L swapped different.symm noQ) (by simp [Ne.symm gp])
  have far := least _ _ _ (L.recut sides different) (by simp [Ne.symm gq])
  refine ⟨near,far,?_⟩
  rw [L.split,card_insert_of_notMem (fun h => (mem_union.mp h).elim L.gateU L.gateW),
    card_union_of_disjoint L.apart]


omit [Fintype V] [Nontrivial V] in
/-- A triangle through an anchor edge of a common-free side supplies a
second contact of the same label. -/
theorem two_contacts (sides : Graph189CutSides.CutSides G A B {p,q})
    (smaller : ∀ T : Finset V, T.card<2 → (G.induce {u : V | u∉T}).Connected)
    (different : p≠q)
    (free : ∀ x∈B, G.Adj x p → ¬G.Adj x q)
    (triangle : ∀ x y, G.Adj x y → ∃ t, G.Adj x t ∧ G.Adj y t) :
    2≤(B.filter (G.Adj q)).card := by
  have split : ({p,q}:Finset V).card=2 := by simp [different]
  have small : ∀ T : Finset V, T.card<({p,q}:Finset V).card →
      (G.induce {u : V | u∉T}).Connected := by simpa only [split] using smaller
  obtain ⟨x,xb,xq⟩ := (sides.contacts_of_minimum small (show q∈({p,q}:Finset V) by simp)).2
  obtain ⟨t,qt,xt⟩ := triangle q x xq.symm
  have tb : t∈B := by
    rcases sides.cover t with ta|tb|ts
    · exact (sides.no_cross t ta x xb xt.symm).elim
    · exact tb
    · rcases (show t=p ∨ t=q by simpa using ts) with rfl|rfl
      · exact (free x xb xt xq).elim
      · exact (qt.ne rfl).elim
  exact Nat.succ_le_of_lt (one_lt_card.mpr
    ⟨x,mem_filter.mpr ⟨xb,xq.symm⟩,t,mem_filter.mpr ⟨tb,qt⟩,xt.ne⟩)

/-- Saturated private-label contact on an actual common-free side gives
either a universal contact or two genuine arms available for routing. -/
theorem universal_or_layout (hc : G.Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q})
    (connected : (G.induce (B:Set V)).Connected) (different : p≠q)
    (smaller : ∀ T : Finset V, T.card<2 → (G.induce {u : V | u∉T}).Connected)
    (free : ∀ x∈B, G.Adj x p → ¬G.Adj x q)
    (triangle : ∀ x y, G.Adj x y → ∃ t, G.Adj x t ∧ G.Adj y t)
    (yb : y∈B) (yp : G.Adj y p)
    (enough : (A.filter (G.Adj p)).card+1=G.secondSmallestDegree) :
    (∀ x∈B, x=y ∨ G.Adj y x) ∨
      ∃ L : Graph189TwoCutLayout.Layout G A B p y, ∀ u∈L.U, ¬G.Adj u q := by
  classical
  by_cases all : ∀ x∈B, x=y ∨ G.Adj y x
  · exact Or.inl all
  push Not at all
  exact Or.inr (build_private hc cap sides connected yb yp enough all
    (free y yb yp) (two_contacts sides smaller different free triangle))

end Graph189TwoCutSaturatedGate
#print axioms Graph189TwoCutSaturatedGate.build_private
#print axioms Graph189TwoCutSaturatedGate.near_recut
#print axioms Graph189TwoCutSaturatedGate.arm_census
#print axioms Graph189TwoCutSaturatedGate.two_contacts
#print axioms Graph189TwoCutSaturatedGate.universal_or_layout
