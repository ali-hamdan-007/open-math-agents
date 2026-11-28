import Graph189TwoCutLayout

namespace Graph189TwoCutShallow
open Finset SimpleGraph Graph189PositiveEvenCut Graph189TwoCutLayout
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
theorem boundary (L : Layout G A B p y) (hc : G.Connected)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (yp : G.Adj y p) (yq : ¬G.Adj y q) :
    (¬G.Adj p q) ∧ (∀ u∈L.U, ¬G.Adj u q) := by
  have nq : y≠q := fun eq =>
    disjoint_left.mp sides.right_cut (eq ▸ L.uSub L.yU) (by simp)
  have qOut := L.qOut sides
  refine ⟨fun h => qOut (two_mem hc nq yq yp h),?_⟩
  intro u uu uq
  rcases L.center u uu with rfl|yu
  · exact yq uq
  · exact qOut (two_mem hc nq yq yu uq)

/-- A high far-arm vertex reaches the center in three steps, whose unique
second-layer vertex in B is the gate. -/
theorem high_gate (L : Layout G A B p y) (hc : G.Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q})
    (highY : G.secondSmallestDegree≤G.degree y) :
    ∀ w∈L.W, G.secondSmallestDegree≤G.degree w → G.Adj L.gate w := by
  intro w hw highW
  have ne : y≠w := fun eq => disjoint_left.mp L.apart L.yU (eq.symm ▸ hw)
  have no := L.noCross y L.yU w hw
  have low := (hc y w).one_lt_dist_of_ne_of_not_adj ne no
  have upper := high_distance_four hc cap highY highW
  have odd : ¬Even (G.dist y w) := fun even => L.wOut sides hw (mem_even_others ne.symm even)
  rw [Nat.even_iff] at odd
  have three : G.dist y w=3 := by omega
  obtain ⟨P,lp⟩ := (hc y w).exists_walk_length_eq_dist
  have len : P.length=3 := lp.trans three
  let v := P.getVert 2
  have ends : P.getVert 3=w := by rw [←len,P.getVert_length]
  have vw : G.Adj v w := by
    simpa only [v,ends] using P.adj_getVert_succ (show 2<P.length by omega)
  have first : G.Adj y (P.getVert 1) := by
    simpa using P.adj_getVert_succ (show 0<P.length by omega)
  have mid : G.Adj (P.getVert 1) v := P.adj_getVert_succ (show 1<P.length by omega)
  have dh := G.dist_le (Walk.cons first (.cons mid .nil))
  change G.dist y v≤2 at dh
  have dt := hc.dist_triangle (u:=y) (v:=v) (w:=w)
  rw [three,dist_eq_one_iff_adj.mpr vw] at dt
  have two : G.dist y v=2 := by omega
  have vne : v≠y := by
    intro eq
    have h := two
    rw [eq,dist_self] at h
    omega
  have ev : v∈evenOthers G y :=
    mem_even_others vne (by rw [two]; exact ⟨1,rfl⟩)
  rw [L.row] at ev
  rcases mem_insert.mp ev with eq|inA
  · exact eq ▸ vw
  · exact (sides.no_cross v (mem_filter.mp inA).1 w (L.wSub hw) vw).elim

omit [Nontrivial V] in
private theorem private_degree (sides : Graph189CutSides.CutSides G A B {p,q})
    {a : V} (aa : a∈A) (aq : ¬G.Adj a q) : G.degree a≤A.card := by
  classical
  have sub : G.neighborFinset a⊆insert p (A.erase a) := by
    intro v hv
    have edge := (G.mem_neighborFinset _ _).mp hv
    rcases sides.cover v with va|vb|vs
    · exact mem_insert_of_mem (mem_erase.mpr ⟨edge.ne.symm,va⟩)
    · exact (sides.no_cross a aa v vb edge).elim
    · rcases (show v=p ∨ v=q by simpa using vs) with rfl|rfl
      · exact mem_insert_self _ _
      · exact (aq edge).elim
  have count := (card_le_card sub).trans (card_insert_le _ _)
  rw [G.card_neighborFinset_eq_degree] at count
  exact count.trans_eq (card_erase_add_one aa)

private theorem few_low (U : Finset V) :
    (U.filter (fun u => ¬G.secondSmallestDegree≤G.degree u)).card≤1 := by
  classical
  apply card_le_one.mpr
  intro x hx y hy
  by_contra ne
  obtain h|h := degree_pair (G:=G) x y ne
  · exact (mem_filter.mp hx).2 h
  · exact (mem_filter.mp hy).2 h

private theorem high_contact (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (diff : p≠q)
    (smaller : ∀ T : Finset V, T.card<2 → (G.induce {v : V | v∉T}).Connected)
    (connected : (G.induce (B:Set V)).Connected)
    (contacts : (A.filter (G.Adj p)).card+1=G.secondSmallestDegree)
    (bPorts : (B.filter (G.Adj p)).card≤G.secondSmallestDegree)
    (large : 2*G.secondSmallestDegree+1<B.card)
    (triangle : ∀ x y, G.Adj x y → ∃ t, G.Adj x t ∧ G.Adj y t) :
    ∃ y∈B, G.Adj y p ∧ G.secondSmallestDegree≤G.degree y := by
  classical
  have size : ({p,q}:Finset V).card=2 := by simp [diff]
  have small : ∀ T : Finset V, T.card<({p,q}:Finset V).card →
      (G.induce {v : V | v∉T}).Connected := by simpa only [size] using smaller
  obtain ⟨x,xb,xp⟩ := (sides.contacts_of_minimum small (by simp : p∈({p,q}:Finset V))).2
  by_cases high : G.secondSmallestDegree≤G.degree x
  · exact ⟨x,xb,xp,high⟩
  obtain ⟨t,pt,xt⟩ := triangle p x xp.symm
  rcases sides.cover t with ta|tb|ts
  · exact (sides.no_cross t ta x xb xt.symm).elim
  · exact ⟨t,tb,pt.symm,(degree_pair (G:=G) x t xt.ne).resolve_left high⟩
  · rcases (show t=p ∨ t=q by simpa using ts) with rfl|rfl
    · exact (G.loopless.irrefl _ pt).elim
    · obtain ⟨L⟩ := build hc cap sides connected xb xp contacts bPorts large
      exact (L.private_y hc sides diff xp smaller xt).elim

/-- Once the recut is available, a high private contact in A would force
both sides of the new cut to disagree with the minimum choice of A. -/
private theorem common_of_gate (sides : Graph189CutSides.CutSides G A B {p,q})
    (L : Layout G A B p y)
    (allP : ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a p)
    (contacts : (A.filter (G.Adj p)).card+1=G.secondSmallestDegree)
    (least : A.card≤L.W.card)
    (highGate : ∀ w∈L.W, G.secondSmallestDegree≤G.degree w → G.Adj L.gate w)
    (wbound : (L.W.filter (G.Adj L.gate)).card+1≤G.secondSmallestDegree) :
    ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a q := by
  classical
  intro a aa high
  by_contra privateA
  have large := high.trans (private_degree sides aa privateA)
  obtain ⟨z,za,low⟩ : ∃ z∈A, ¬G.secondSmallestDegree≤G.degree z := by
    by_contra! all
    have sub : A⊆A.filter (G.Adj p) := fun u hu =>
      mem_filter.mpr ⟨hu,(allP u hu (all u hu)).symm⟩
    have h := card_le_card sub
    omega
  have highW (w : V) (hw : w∈L.W) : G.secondSmallestDegree≤G.degree w := by
    have ne : z≠w := fun eq => disjoint_left.mp sides.apart (eq ▸ za) (L.wSub hw)
    exact (degree_pair (G:=G) z w ne).resolve_left low
  have h := card_le_card (show L.W⊆L.W.filter (G.Adj L.gate) from
    fun w hw => mem_filter.mpr ⟨hw,highGate w hw (highW w hw)⟩)
  omega

/-- The original-graph shallow branch in which exactly k−1 vertices of A
contact p, and B exceeds 2k+1. Every cut used here is derived in G. -/
theorem order_bound (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B {p,q}) (diff : p≠q)
    (smaller : ∀ T : Finset V, T.card<2 → (G.induce {v : V | v∉T}).Connected)
    (connected : (G.induce (B:Set V)).Connected)
    (triangle : ∀ x y, G.Adj x y → ∃ t, G.Adj x t ∧ G.Adj y t)
    (degree : 4≤G.secondSmallestDegree) (aSize : G.secondSmallestDegree≤A.card+1)
    (bSize : 2*G.secondSmallestDegree+1<B.card)
    (contacts : (A.filter (G.Adj p)).card+1=G.secondSmallestDegree)
    (allP : ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a p)
    (minimumSide : ∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) :
    Fintype.card V≤3*G.secondSmallestDegree+2 := by
  classical
  let k := G.secondSmallestDegree
  have aPorts : (A.filter (G.Adj p)).Nonempty := by
    apply card_pos.mp
    omega
  obtain ⟨a,aPort⟩ := aPorts
  obtain ⟨aa,pa⟩ := mem_filter.mp aPort
  have bPorts := contact_bound hc cap sides aa pa.symm
  obtain ⟨y,yb,yp,hy⟩ := high_contact hc cap sides diff smaller connected contacts bPorts bSize triangle
  obtain ⟨L⟩ := build hc cap sides connected yb yp contacts bPorts bSize
  have privateY := L.private_y hc sides diff yp smaller
  obtain ⟨pq,uq⟩ := boundary L hc sides yp privateY
  have highGate := high_gate L hc cap sides hy
  have qs : q∈({p,q}:Finset V) := by simp
  have qg : q≠L.gate := fun e => disjoint_left.mp sides.right_cut (e.symm ▸ L.gate_mem) qs
  have size : ({q,L.gate}:Finset V).card=2 := by simp [qg]
  have least := minimumSide L.W (insert p (A∪L.U)) {q,L.gate} (L.recut sides diff) size
  let H := L.W.filter (fun w => k≤G.degree w)
  let D := L.W.filter (G.Adj L.gate)
  have part := card_filter_add_card_filter_not (s:=L.W) (fun w => k≤G.degree w)
  have low := few_low (G:=G) L.W
  change (L.W.filter (fun w => ¬k≤G.degree w)).card≤1 at low
  have enough : k≤H.card+2 := by
    change H.card+(L.W.filter (fun w => ¬k≤G.degree w)).card=L.W.card at part
    change k≤A.card+1 at aSize
    omega
  have hD : H⊆D := by
    intro w hw
    obtain ⟨ww,wh⟩ := mem_filter.mp hw
    exact mem_filter.mpr ⟨ww,highGate w ww wh⟩
  have dH := card_le_card hD
  have two : 2≤D.card := by change 4≤k at degree; omega
  have dBound := Graph189TwoCutRecut.gate_arm_row hc cap sides L.split diff L.apart
    L.noCross uq contacts two L.yNear L.nearU yp L.nearGate
  have aCommon := common_of_gate sides L allP contacts least highGate (by omega)
  obtain ⟨f,fw,fq,fh⟩ := Graph189TwoCutRecut.exists_high_q_contact sides L.split L.noCross
    L.noP triangle highGate enough dBound (L.q_contact sides diff smaller)
  have wBudget : H.card+(if G.Adj L.gate q then 1 else 0)+1≤k := by
    change D.card+(if G.Adj L.gate q then 1 else 0)+1≤k at dBound
    omega
  exact Graph189TwoCutRecut.final_bound hc cap sides L.split L.apart L.gateU
    L.noCross uq L.noP pq aCommon fw fq (highGate f fw fh).symm fh wBudget

#print axioms order_bound
#print axioms boundary
#print axioms high_gate
end Graph189TwoCutShallow
