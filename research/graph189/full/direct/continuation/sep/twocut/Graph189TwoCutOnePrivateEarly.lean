import Graph189TwoCutCensusJoint

namespace Graph189TwoCutOnePrivate
open Finset SimpleGraph Graph189PositiveEvenCut Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B : Finset V} {p q : V}

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem two (hc : G.Connected) {x a y : V} (ne : x≠y)
    (miss : ¬G.Adj x y) (xa : G.Adj x a) (ay : G.Adj a y) : G.dist x y=2 := by
  have lo := (hc x y).one_lt_dist_of_ne_of_not_adj ne miss
  have hi := G.dist_le (Walk.cons xa (.cons ay .nil))
  change G.dist x y≤2 at hi
  omega

omit [Nontrivial V] in
/-- When p has k contacts in A, its opposite contact must dominate B.
The even row at p then bounds the side by 2k. -/
theorem full_anchor (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : CutSides G A B {p,q})
    (connB : (G.induce (B : Set V)).Connected)
    {y : V} (yb : y∈B) (yp : G.Adj y p)
    (full : (A.filter (G.Adj p)).card=G.secondSmallestDegree)
    (bPorts : (B.filter (G.Adj p)).card≤G.secondSmallestDegree) :
    B.card≤2*G.secondSmallestDegree := by
  classical
  let P := A.filter (G.Adj p)
  let Q := B.filter (G.Adj p)
  have even : evenOthers G y=P := by
    have sub : P⊆evenOthers G y := by
      intro v hv
      obtain ⟨va,vp⟩ := mem_filter.mp hv
      have ne : y≠v := fun eq => disjoint_left.mp sides.apart va (eq ▸ yb)
      have h := two hc ne (fun e => sides.no_cross v va y yb e.symm) yp vp
      exact mem_even_others ne.symm (by rw [h]; exact ⟨1,rfl⟩)
    have size := even_others_card (by simpa only [Nat.add_comm 1] using cap y)
    exact (eq_of_subset_of_card_le sub (size.trans_eq full.symm)).symm
  have complete (z : V) (zb : z∈B) (ne : z≠y) : G.Adj y z := by
    by_contra miss
    obtain ⟨P⟩ := connB (⟨y,yb⟩ : (B:Set V)) ⟨z,zb⟩
    obtain ⟨u,w,uNear,wFar,uw,_⟩ := walk_exits (G:=G.induce (B:Set V))
      (fun v => v.val=y ∨ G.Adj y v.val) P (Or.inl rfl) (not_or.mpr ⟨ne,miss⟩)
    have edge : G.Adj u.val w.val := uw
    have yu : G.Adj y u.val := uNear.elim (fun eq => ((not_or.mp wFar).2 (eq ▸ edge)).elim) id
    have ne' : y≠w.val := fun eq => (not_or.mp wFar).1 eq.symm
    have d := two hc ne' (not_or.mp wFar).2 yu edge
    have witness : w.val∈evenOthers G y :=
      mem_even_others ne'.symm (by rw [d]; exact ⟨1,rfl⟩)
    rw [even] at witness
    exact disjoint_left.mp sides.apart (mem_filter.mp witness).1 w.property
  have cover : B⊆Q∪evenOthers G p := by
    intro z zb
    by_cases pz : G.Adj p z
    · exact mem_union_left _ (mem_filter.mpr ⟨zb,pz⟩)
    have ne : z≠y := by intro eq; exact pz (eq.symm ▸ yp.symm)
    have np : p≠z := fun eq => disjoint_left.mp sides.right_cut zb (eq ▸ (by simp : p∈({p,q}:Finset V)))
    have d := two hc np pz yp.symm (complete z zb ne)
    exact mem_union_right _ (mem_even_others np.symm (by rw [d]; exact ⟨1,rfl⟩))
  have cnt := (card_le_card cover).trans (card_union_le _ _)
  have e := even_others_card (by simpa only [Nat.add_comm 1] using cap p)
  change Q.card≤G.secondSmallestDegree at bPorts
  omega

omit [Nontrivial V] in
private theorem degree_without_q (sides : CutSides G A B {p,q}) {a : V}
    (aa : a∈A) (aq : ¬G.Adj a q) : G.degree a≤A.card := by
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

/-- In the smallest possible side, a low nonport and a high neighbor count
complementary parities on the opposite side. -/
theorem min_side_low_nonport (hc : G.Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : CutSides G A B {p,q}) (diff : p≠q)
    (minimum : 3≤G.minDegree) (size : A.card+1=G.secondSmallestDegree)
    (allP : ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a p)
    {z : V} (za : z∈A) (low : ¬G.secondSmallestDegree≤G.degree z)
    (zp : ¬G.Adj z p) (zq : ¬G.Adj z q) :
    B.card+2≤2*G.secondSmallestDegree := by
  classical
  have pos : 0<(G.neighborFinset z).card := by
    rw [G.card_neighborFinset_eq_degree]
    have := minimum.trans (G.minDegree_le_degree z)
    omega
  obtain ⟨x,hn⟩ := card_pos.mp pos
  have zx := (G.mem_neighborFinset _ _).mp hn
  have xa : x∈A := by
    rcases sides.cover x with h|h|h
    · exact h
    · exact (sides.no_cross z za x h zx).elim
    · rcases (show x=p ∨ x=q by simpa using h) with rfl|rfl
      · exact (zp zx).elim
      · exact (zq zx).elim
  have high := (degree_pair (G:=G) z x zx.ne).resolve_left low
  have xp := allP x xa high
  have xq : G.Adj x q := by
    by_contra miss
    have d := high.trans (degree_without_q sides xa miss)
    omega
  have zpn : z≠p := fun eq => disjoint_left.mp sides.left_cut (eq ▸ za) (by simp)
  have zqn : z≠q := fun eq => disjoint_left.mp sides.left_cut (eq ▸ za) (by simp)
  exact Graph189TwoCutParity.complementary_rows hc sides diff xa za (dist_eq_one_iff_adj.mpr xp)
    (dist_eq_one_iff_adj.mpr xq) (two hc zpn zp zx xp) (two hc zqn zq zx xq)
    (by simpa only [Nat.add_comm 1] using cap x) (by simpa only [Nat.add_comm 1] using cap z)

#print axioms full_anchor
#print axioms min_side_low_nonport
end Graph189TwoCutOnePrivate
