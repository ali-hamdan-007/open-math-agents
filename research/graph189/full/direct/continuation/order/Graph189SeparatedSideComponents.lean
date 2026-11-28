import Graph189AnySingletonCut
import Graph189LowSoleNearest

open SimpleGraph Finset
namespace Graph189SeparatedSideComponents
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- If one side of a separation fails to be connected, three different
actual components remain after deleting the separator. -/
theorem three_of_disconnected_side (sides : Graph189CutSides.CutSides G A B S)
    (disc : ¬(G.induce (A:Set V)).Connected) :
    Nonempty (Fin 3 ↪ (G.induce {v : V | v∉S}).ConnectedComponent) := by
  classical
  let H := G.induce {v : V | v∉S}
  let f := (Embedding.induce (G:=G) {v : V | v∉S}).toHom
  let liftA (a : A) : {v : V | v∉S} := ⟨a.val,fun h => Finset.disjoint_left.mp sides.left_cut a.property h⟩
  let liftB (b : B) : {v : V | v∉S} := ⟨b.val,fun h => Finset.disjoint_left.mp sides.right_cut b.property h⟩
  have stays {a b : {v : V | v∉S}} (p : H.Walk a b) (ha : a.val∈A) :
      ∀v∈p.support, v.val∈A := by
    intro v vm
    by_contra bad
    obtain ⟨u,w,ua,wa,e,_⟩ := Graph189CutSides.walk_exits (fun v : {v : V | v∉S} => v.val∈A)
      (p.takeUntil v vm) ha bad
    rcases sides.cover w.val with h|h|h
    · exact wa h
    · exact sides.no_cross u.val ua w.val h e
    · exact w.property h
  obtain ⟨a,aa⟩ := sides.left_nonempty
  let a' : A := ⟨a,aa⟩
  obtain ⟨b,bb⟩ := sides.right_nonempty
  let b' : B := ⟨b,bb⟩
  obtain ⟨c,ac⟩ : ∃ c : A, ¬(G.induce (A:Set V)).Reachable a' c := by
    by_contra! all
    exact disc ((connected_iff_exists_forall_reachable _).mpr ⟨a',all⟩)
  have same : H.connectedComponentMk (liftA a')≠H.connectedComponentMk (liftA c) := by
    intro eq
    obtain ⟨p⟩ := ConnectedComponent.exact eq
    let q := p.map f
    apply ac
    exact (q.induce (A:Set V) (by
      intro v hv
      rw [show q.support=p.support.map f from Walk.support_map _ _] at hv
      obtain ⟨w,wm,rfl⟩ := List.mem_map.mp hv
      exact stays p aa w wm)).reachable
  have opposite (r : A) : H.connectedComponentMk (liftA r)≠H.connectedComponentMk (liftB b') := by
    intro eq
    obtain ⟨p⟩ := ConnectedComponent.exact eq
    exact Finset.disjoint_left.mp sides.apart (stays p r.property _ p.end_mem_support) bb
  let values : Fin 3 → H.ConnectedComponent := ![H.connectedComponentMk (liftA a'),
    H.connectedComponentMk (liftA c),H.connectedComponentMk (liftB b')]
  refine ⟨⟨values,?_⟩⟩
  intro i j e
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact (same e).elim
    | exact (same e.symm).elim
    | exact (opposite a' e).elim
    | exact (opposite a' e.symm).elim
    | exact (opposite c e).elim
    | exact (opposite c e.symm).elim

/-- The original two-cut implication needs no connectedness assumptions on
the chosen sides and allows the low vertex on either side or the separator. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (two : S.card=2) (large : 10≤G.secondSmallestDegree) {x i y j : V}
    (left : Graph189SoleNearestSides.Witness G A S x i) (right : Graph189SoleNearestSides.Witness G B S y j) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have many (c : Fin 3 ↪ (G.induce {v : V | v∉S}).ConnectedComponent) :=
    Graph189AnySingletonCut.of_three_components hc cap S sc (by omega) (by omega) (by omega) c
  by_cases hA : (G.induce (A:Set V)).Connected
  · by_cases hB : (G.induce (B:Set V)).Connected
    · exact Graph189LowSoleNearest.traceable hc cap sides sc two large hA hB left right
    · exact (three_of_disconnected_side sides.swap hB).elim many
  · exact (three_of_disconnected_side sides hA).elim many

#print axioms three_of_disconnected_side
#print axioms traceable
end Graph189SeparatedSideComponents
