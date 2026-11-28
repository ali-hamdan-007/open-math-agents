import Graph189PrivatePortRecut
import Graph189PositiveEvenCut
import Graph189PortDifference

open SimpleGraph Finset Graph189PositiveEvenCut
namespace Graph189FourCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {i v : V}

/-- A private port lies on the smaller side of its recut whenever n≥4k+s+1.
Every internal neighbor of the port touches its anchor or lies at distance two
from that anchor. Each of these classes has at most k vertices. -/
theorem private_recut (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (minimum : S.card=G.vertexConnectivity) (point : ∀x,G.distEven x≤1+G.secondSmallestDegree)
    (order : 4*G.secondSmallestDegree+S.card+1≤Fintype.card V)
    (vb : v∈B) (high : G.secondSmallestDegree≤G.degree v) (support : S.filter (G.Adj v)={i})
    (many : G.secondSmallestDegree+1≤S.card+(A∩G.neighborFinset i).card)
    (uniform : ∀ W F T : Finset V, Graph189CutSides.CutSides G W F T → T.card=G.vertexConnectivity →
      (W.filter (fun y => G.secondSmallestDegree≤G.degree y)).card≤
      (F.filter (fun y => G.secondSmallestDegree≤G.degree y)).card →
      ∀ y∈W,G.secondSmallestDegree≤G.degree y → 2≤(T.filter (G.Adj y)).card) : False := by
  classical
  let k := G.secondSmallestDegree
  have sm (T : Finset V) (lt : T.card<S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  obtain ⟨W,F,T,cut,sz,layout,_,_,vw,tag⟩ := sides.private_port_recut sm vb support (point v) many
  have mark : i∈S.filter (G.Adj v) := support ▸ mem_singleton_self i
  obtain ⟨si,vi⟩ := mem_filter.mp mark
  obtain ⟨a,aa,ai⟩ := (sides.contacts_of_minimum sm si).1
  let P := B.filter (G.Adj i)
  have port : P⊆evenOthers G a := by
    intro x xP
    obtain ⟨xb,ix⟩ := mem_filter.mp xP
    have dist := Graph189PortDifference.cross_two hc sides aa xb ai ix
    exact mem_even_others (fun e => disjoint_left.mp sides.apart aa (e ▸ xb)) (by rw [dist]; decide)
  have bound (u : V) : (evenOthers G u).card≤k := even_others_card (by simpa only [Nat.add_comm] using point u)
  have cover : W⊆P∪evenOthers G i := by
    intro x xw
    rw [layout] at xw
    rcases mem_insert.mp xw with rfl|inside
    · exact mem_union_left _ (mem_filter.mpr ⟨vb,vi.symm⟩)
    obtain ⟨xb,vx⟩ := mem_inter.mp inside
    by_cases ix : G.Adj i x
    · exact mem_union_left _ (mem_filter.mpr ⟨xb,ix⟩)
    have diff : x≠i := fun e => disjoint_left.mp sides.right_cut xb (e.symm ▸ si)
    have low := (hc i x).one_lt_dist_of_ne_of_not_adj diff.symm ix
    have upper := G.dist_le (Walk.cons vi.symm (Walk.cons ((G.mem_neighborFinset _ _).mp vx) Walk.nil))
    change G.dist i x≤2 at upper
    exact mem_union_right _ (mem_even_others diff (by rw [show G.dist i x=2 by omega]; decide))
  have lim := (card_le_card cover).trans (card_union_le _ _)
  have pmax := (card_le_card port).trans (bound a)
  have emax := bound i
  change 4*k+S.card+1≤Fintype.card V at order
  have orientation := cut.high_orientation (by omega)
  have neq := uniform W F T cut (sz.trans minimum) orientation v vw high
  rw [tag,card_singleton] at neq
  omega

end Graph189FourCut
#print axioms Graph189FourCut.private_recut
