import Graph189TwoCutRecut

namespace Graph189TwoCutLayout
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

structure Layout (G : SimpleGraph V) (A B : Finset V) (p y : V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] where
  U : Finset V
  W : Finset V
  gate : V
  near : V
  split : B=insert gate (U∪W)
  apart : Disjoint U W
  gateU : gate∉U
  gateW : gate∉W
  wNonempty : W.Nonempty
  yU : y∈U
  nearU : near∈U
  yNear : G.Adj y near
  nearGate : G.Adj near gate
  noCross : ∀ u∈U, ∀ w∈W, ¬G.Adj u w
  noP : ∀ w∈W, ¬G.Adj w p
  center : ∀ u∈U, u=y ∨ G.Adj y u
  row : evenOthers G y=insert gate (A.filter (G.Adj p))

omit [Nontrivial V] in
/-- A p-contact bounds all opposite p-contacts by its positive even row. -/
theorem contact_bound (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (ya : y∈A) (yp : G.Adj y p) :
    (B.filter (G.Adj p)).card≤G.secondSmallestDegree := by
  apply (card_le_card ?_).trans (even_others_card (by simpa only [Nat.add_comm 1] using cap y))
  intro v hv
  obtain ⟨vb,vp⟩ := mem_filter.mp hv
  exact two_mem hc (fun eq => disjoint_left.mp sides.apart (eq ▸ ya) vb)
    (sides.no_cross y ya v vb) yp vp

omit [Nontrivial V] in
/-- A p-contact dominating its side except for at most one vertex bounds
that side by 2k+1 through the contact count and the second layer at p. -/
theorem closed_bound (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (yp : G.Adj y p)
    (bPorts : (B.filter (G.Adj p)).card≤G.secondSmallestDegree)
    (g : V) (cover : ∀ v∈B, v=g ∨ v=y ∨ G.Adj y v) :
    B.card≤2*G.secondSmallestDegree+1 := by
  classical
  let K := B.filter (G.Adj p)
  let L := evenOthers G p
  have ps : p∈({p,q}:Finset V) := by simp
  have cnt : B⊆insert g (K∪L) := by
    intro v vb
    by_cases pv : G.Adj p v
    · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨vb,pv⟩))
    rcases cover v vb with rfl|rfl|yv
    · exact mem_insert_self _ _
    · exact (pv yp.symm).elim
    · have pvne : p≠v := fun h => disjoint_left.mp sides.right_cut vb (h ▸ ps)
      exact mem_insert_of_mem (mem_union_right _ (two_mem hc pvne pv yp.symm yv))
  have first := (card_le_card cnt).trans (card_insert_le _ _)
  have pair := card_union_le K L
  have even : L.card≤G.secondSmallestDegree :=
    even_others_card (by simpa only [Nat.add_comm 1] using cap p)
  change K.card≤G.secondSmallestDegree at bPorts
  omega

omit [Nontrivial V] in
/-- A saturated contact on a large connected side creates a unique
second-layer gate, with actual anticomplete arms. -/
theorem build (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q})
    (connected : (G.induce (B:Set V)).Connected)
    (yb : y∈B) (yp : G.Adj y p)
    (contacts : (A.filter (G.Adj p)).card+1=G.secondSmallestDegree)
    (bPorts : (B.filter (G.Adj p)).card≤G.secondSmallestDegree)
    (large : 2*G.secondSmallestDegree+1<B.card) :
    Nonempty (Layout G A B p y) := by
  classical
  let U := B.filter (fun v => v=y ∨ G.Adj y v)
  let P := A.filter (G.Adj p)
  obtain ⟨x,xb,notY,notAdj⟩ : ∃ x∈B, x≠y ∧ ¬G.Adj y x := by
    by_contra none
    exact (not_le_of_gt large) (closed_bound hc cap sides yp bPorts y
      (fun v vb => Or.inr (by
        by_cases eq : v=y
        · exact Or.inl eq
        by_cases edge : G.Adj y v
        · exact Or.inr edge
        · exact (none ⟨v,vb,eq,edge⟩).elim)))
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
  have nonempty : W.Nonempty := by
    by_contra bad
    have empty := not_nonempty_iff_eq_empty.mp bad
    have bound := closed_bound hc cap sides yp bPorts g (by
      intro v vb
      have vg : v∈insert g U := by simpa only [split,empty,union_empty] using vb
      rcases mem_insert.mp vg with eq|hu
      · exact Or.inl eq
      · exact Or.inr (mem_filter.mp hu).2)
    exact (not_le_of_gt large) bound
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
    mem_filter.mpr ⟨u.property,uNear⟩,yu,ug,?_,?_,?_,row⟩⟩
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

namespace Layout
variable (L : Layout G A B p y)

omit [Nontrivial V] in
theorem uSub : L.U⊆B := by
  intro u hu
  rw [L.split]
  exact mem_insert_of_mem (mem_union_left _ hu)

omit [Nontrivial V] in
theorem wSub : L.W⊆B := by
  intro w hw
  rw [L.split]
  exact mem_insert_of_mem (mem_union_right _ hw)

omit [Nontrivial V] in
theorem gate_mem : L.gate∈B :=
  (congrArg (fun D : Finset V => L.gate∈D) L.split).mpr (mem_insert_self _ _)

omit [Nontrivial V] in
/-- The unique gate and q are a second genuine two-cut, with the far
arm on one side. This uses only actual graph edges and finset disjointness. -/
theorem recut (sides : Graph189CutSides.CutSides G A B {p,q}) (diff : p≠q) :
    Graph189CutSides.CutSides G L.W (insert p (A∪L.U)) {q,L.gate} := by
  classical
  have ps : p∈({p,q}:Finset V) := by simp
  have qs : q∈({p,q}:Finset V) := by simp
  have pb : p∉B := fun hp => disjoint_left.mp sides.right_cut hp ps
  have qb : q∉B := fun hq => disjoint_left.mp sides.right_cut hq qs
  refine ⟨L.wNonempty,⟨p,mem_insert_self _ _⟩,?_,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hw hr
    rcases mem_insert.mp hr with rfl|hr
    · exact pb (L.wSub hw)
    rcases mem_union.mp hr with ha|hu
    · exact disjoint_left.mp sides.apart ha (L.wSub hw)
    · exact disjoint_left.mp L.apart hu hw
  · apply Finset.disjoint_left.mpr
    intro v hw ht
    rcases (show v=q ∨ v=L.gate by simpa using ht) with rfl|rfl
    · exact qb (L.wSub hw)
    · exact L.gateW hw
  · apply Finset.disjoint_left.mpr
    intro v hr ht
    rcases (show v=q ∨ v=L.gate by simpa using ht) with hq|hg
    · subst v
      rcases mem_insert.mp hr with eq|hr
      · exact diff eq.symm
      rcases mem_union.mp hr with ha|hu
      · exact disjoint_left.mp sides.left_cut ha qs
      · exact qb (L.uSub hu)
    · subst v
      rcases mem_insert.mp hr with eq|hr
      · exact pb (eq ▸ L.gate_mem)
      rcases mem_union.mp hr with ha|hu
      · exact disjoint_left.mp sides.apart ha L.gate_mem
      · exact L.gateU hu
  · intro v
    rcases sides.cover v with va|vb|vs
    · exact Or.inr (Or.inl (mem_insert_of_mem (mem_union_left _ va)))
    · rw [L.split] at vb
      rcases mem_insert.mp vb with rfl|vb
      · exact Or.inr (Or.inr (by simp))
      rcases mem_union.mp vb with vu|vw
      · exact Or.inr (Or.inl (mem_insert_of_mem (mem_union_right _ vu)))
      · exact Or.inl vw
    · rcases (show v=p ∨ v=q by simpa using vs) with rfl|rfl
      · exact Or.inr (Or.inl (mem_insert_self _ _))
      · exact Or.inr (Or.inr (by simp))
  · intro w hw v hv edge
    rcases mem_insert.mp hv with rfl|hv
    · exact L.noP w hw edge
    rcases mem_union.mp hv with va|vu
    · exact sides.no_cross v va w (L.wSub hw) edge.symm
    · exact L.noCross v vu w hw edge.symm

include L

omit [Nontrivial V] in
theorem qOut (sides : Graph189CutSides.CutSides G A B {p,q}) : q∉evenOthers G y := by
  classical
  have qs : q∈({p,q}:Finset V) := by simp
  rw [L.row]
  intro h
  rcases mem_insert.mp h with eq|qa
  · exact disjoint_left.mp sides.right_cut (eq.symm ▸ L.gate_mem) qs
  · exact disjoint_left.mp sides.left_cut (mem_filter.mp qa).1 qs

omit [Nontrivial V] in
theorem wOut (sides : Graph189CutSides.CutSides G A B {p,q}) {w : V} (hw : w∈L.W) :
    w∉evenOthers G y := by
  rw [L.row]
  intro h
  rcases mem_insert.mp h with eq|ha
  · exact L.gateW (eq ▸ hw)
  · exact disjoint_left.mp sides.apart (mem_filter.mp ha).1 (L.wSub hw)

omit [Nontrivial V] in
theorem q_contact (sides : Graph189CutSides.CutSides G A B {p,q}) (diff : p≠q)
    (smaller : ∀ T : Finset V, T.card<2 → (G.induce {v : V | v∉T}).Connected) :
    ∃ f∈L.W, G.Adj f q := by
  have qs : q∈({p,q}:Finset V) := by simp
  have ng : q≠L.gate := fun e =>
    disjoint_left.mp sides.right_cut (e.symm ▸ L.gate_mem) qs
  have size : ({q,L.gate}:Finset V).card=2 := by simp [ng]
  have small : ∀ T : Finset V, T.card<({q,L.gate}:Finset V).card →
      (G.induce {v : V | v∉T}).Connected := by simpa only [size] using smaller
  exact ((L.recut sides diff).contacts_of_minimum small (by simp)).1

omit [Nontrivial V] in
theorem private_y (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B {p,q})
    (diff : p≠q) (yp : G.Adj y p)
    (smaller : ∀ T : Finset V, T.card<2 → (G.induce {v : V | v∉T}).Connected) :
    ¬G.Adj y q := by
  intro yq
  obtain ⟨f,fw,fq⟩ := L.q_contact sides diff smaller
  have fy : y≠f := by
    intro e
    exact L.noP f fw (e ▸ yp)
  have no := L.noCross y L.yU f fw
  exact L.wOut sides fw (two_mem hc fy no yq fq.symm)

end Layout

#print axioms build
#print axioms Layout.recut
#print axioms Layout.q_contact
#print axioms Layout.private_y
end Graph189TwoCutLayout
