import Graph189TwoCutShallow
import Graph189TwoCutOnePrivateEarly

namespace Graph189TwoCutOnePrivate
open Finset SimpleGraph Graph189PositiveEvenCut Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B : Finset V} {p q : V}

omit [Nontrivial V] in
private theorem degree_bound (sides : CutSides G A B {p,q}) {a : V} (aa : a∈A) :
    G.degree a≤A.card+1 := by
  classical
  have sub : G.neighborFinset a⊆((A.erase a)∪{p,q}) := by
    intro v hv
    have edge := (G.mem_neighborFinset _ _).mp hv
    rcases sides.cover v with va|vb|vs
    · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,va⟩)
    · exact (sides.no_cross a aa v vb edge).elim
    · exact mem_union_right _ vs
  have count := (card_le_card sub).trans (card_union_le _ _)
  rw [G.card_neighborFinset_eq_degree] at count
  have erase := card_erase_add_one aa
  have size : ({p,q}:Finset V).card≤2 := (card_insert_le p {q}).trans (by simp)
  omega

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem graph_order (sides : CutSides G A B {p,q}) (diff : p≠q) :
    Fintype.card V=A.card+B.card+2 := by
  have complete : (A∪B)∪({p,q}:Finset V)=univ := eq_univ_iff_forall.mpr (fun v => by
    rcases sides.cover v with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h)
  have partitions := congrArg Finset.card complete
  rw [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨sides.left_cut,sides.right_cut⟩),
    card_union_of_disjoint sides.apart,card_univ] at partitions
  simpa [diff] using partitions.symm

/-- The complete shallow no-q-private branch for k≥9. The earlier
index-three order supplies the lower bound in the original graph. -/
theorem excluded (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (sides : CutSides G A B {p,q}) (diff : p≠q)
    (smaller : ∀ T : Finset V, T.card<2 → (G.induce {v : V | v∉T}).Connected)
    (connB : (G.induce (B:Set V)).Connected)
    (triangle : ∀ x y, G.Adj x y → ∃ t, G.Adj x t ∧ G.Adj y t)
    (large : 9≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (size : 2≤A.card)
    (order : 4*G.secondSmallestDegree≤Fintype.card V+5)
    (shallow : ∀ a∈A, G.secondSmallestDegree≤G.degree a → G.Adj a p ∨ G.Adj a q)
    (onePrivate : ∀ a∈A, G.Adj a q → G.Adj a p)
    (minimumSide : ∀ C D T, CutSides G C D T → T.card=2 → A.card≤C.card) : False := by
  classical
  let k := G.secondSmallestDegree
  let P := A.filter (G.Adj p)
  let N := A \ P
  have allP (a : V) (aa : a∈A) (high : k≤G.degree a) : G.Adj a p :=
    (shallow a aa high).elim id (onePrivate a aa)
  have cutSize : ({p,q}:Finset V).card=2 := by simp [diff]
  have small : ∀ T : Finset V, T.card<({p,q}:Finset V).card →
      (G.induce {v : V | v∉T}).Connected := by simpa only [cutSize] using smaller
  obtain ⟨⟨x,xa,xp⟩,⟨y,yb,yp⟩⟩ := sides.contacts_of_minimum small (show p∈({p,q}:Finset V) by simp)
  have ap := Graph189TwoCutLayout.contact_bound hc cap sides.swap yb yp
  have bp := Graph189TwoCutLayout.contact_bound hc cap sides xa xp
  have whole := graph_order sides diff
  have boundA : k≤A.card+1 := by
    obtain ⟨a,aa,b,ba,ne⟩ := one_lt_card.mp (show 1<A.card by omega)
    obtain h|h := degree_pair (G:=G) a b ne
    · exact h.trans (degree_bound sides aa)
    · exact h.trans (degree_bound sides ba)
  have miss (a : V) (an : a∈N) : ¬G.Adj a p :=
    fun e => (mem_sdiff.mp an).2 (mem_filter.mpr ⟨(mem_sdiff.mp an).1,e.symm⟩)
  have low (a : V) (an : a∈N) : ¬k≤G.degree a :=
    fun h => miss a an (allP a (mem_sdiff.mp an).1 h)
  have nsize : N.card≤1 := by
    apply card_le_one.mpr
    intro a na b nb
    by_contra ne
    obtain h|h := degree_pair (G:=G) a b ne
    · exact low a na h
    · exact low b nb h
  have aSplit : N.card+P.card=A.card := by
    have sub : P⊆A := filter_subset _ _
    simpa only [inter_eq_right.mpr sub] using card_sdiff_add_card_inter A P
  change P.card≤k at ap
  change 9≤k at large
  change 4*k≤Fintype.card V+5 at order
  by_cases full : P.card=k
  · have short := full_anchor hc cap sides connB yb yp full bp
    change B.card≤2*k at short
    omega
  by_cases exactCount : P.card+1=k
  · have big : 2*k+1<B.card := by omega
    have short := Graph189TwoCutShallow.order_bound hc cap sides diff smaller connB triangle
      (by omega : 4≤k) boundA big exactCount allP minimumSide
    change Fintype.card V≤3*k+2 at short
    omega
  have aExact : A.card+1=k := by omega
  have some : N.Nonempty := card_pos.mp (by omega)
  obtain ⟨z,zn⟩ := some
  have za := (mem_sdiff.mp zn).1
  have zq : ¬G.Adj z q := fun h => miss z zn (onePrivate z za h)
  have short := min_side_low_nonport hc cap sides diff minimum aExact allP za (low z zn) (miss z zn) zq
  change B.card+2≤2*k at short
  omega

#print axioms excluded
end Graph189TwoCutOnePrivate
