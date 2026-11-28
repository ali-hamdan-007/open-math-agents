import Graph189ExteriorMatching

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

omit [Fintype V] in
/-- A finite subset of real path vertices has canonical distinct positions on the path. -/
theorem vertex_positions_equiv (p : G.Walk x y) (M : Finset V) (onPath : ∀ z∈M, z∈p.support) :
    ∃ marks : Finset (Fin p.support.length), ∃ e : marks ≃ M,
      ∀ i : marks, p.support[i.val.val]=(e i).val := by
  classical
  let pos (u : M) : Fin p.support.length :=
    ⟨p.support.idxOf u.val,List.idxOf_lt_length_iff.mpr (onPath u.val u.property)⟩
  have eval (u : M) : p.support[(pos u).val] = u.val := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (onPath u.val u.property))
  have inj : Function.Injective pos := by
    intro a b h
    apply Subtype.ext
    calc
      a.val = p.support[(pos a).val] := (eval a).symm
      _ = p.support[(pos b).val] := by rw [h]
      _ = b.val := eval b
  let marks := M.attach.image pos
  let embed (u : M) : marks := ⟨pos u, Finset.mem_image.mpr ⟨u,Finset.mem_attach _ _,rfl⟩⟩
  have bij : Function.Bijective embed := by
    constructor
    · intro a b eq
      exact inj (congrArg Subtype.val eq)
    · intro i
      obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp i.property
      exact ⟨u,Subtype.ext eq⟩
  let e := Equiv.ofBijective embed bij
  refine ⟨marks,e.symm,?_⟩
  intro i
  have posEq : pos (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
  have value := eval (e.symm i)
  rwa [posEq] at value

/-- Vertex form: an actual finite matching from a subset of the path vertices
into a Hamilton-connected exterior induced graph, with no order data supplied. -/
theorem exterior_vertex_matching_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (M : Finset V) (nonempty : M.Nonempty) (onPath : ∀ z∈M, z∈p.support)
    (attach : M ↪ K) (edges : ∀ i : M, G.Adj i.val (attach i).val) :
    (M.card+2)*K.card + M.card ≤ Fintype.card V := by
  classical
  obtain ⟨marks,e,value⟩ := vertex_positions_equiv p M onPath
  let assigned := e.toEmbedding.trans attach
  have edges' (i : marks) : G.Adj p.support[i.val.val] (assigned i).val := by
    rw [value]
    exact edges (e i)
  have card : marks.card=M.card := by simpa using Fintype.card_congr e
  have has : marks.Nonempty := Finset.card_pos.mp (by rw [card]; exact Finset.card_pos.mpr nonempty)
  have bound := exterior_hamilton_connected_matching p hp longest K size outside hconn marks has assigned edges'
  rwa [card] at bound

/-- Vertex-subset interface for the selected-port bound, compatible with the
matching at a component boundary. No subgraph-wide Hamilton-connectivity is assumed. -/
theorem selected_vertex_matching_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (outside : ∀ z∈K, z∉p.support)
    (M : Finset V) (two : 2 ≤ M.card) (onPath : ∀ z∈M, z∈p.support)
    (attach : M ↪ K) (edges : ∀ z : M, G.Adj z.val (attach z).val)
    (selected : ∀ i j : M, i≠j →
      ∃ q : (G.induce (K : Set V)).Walk (attach i) (attach j), q.IsHamiltonian) :
    (M.card+2)*K.card+M.card ≤ Fintype.card V := by
  classical
  obtain ⟨marks,e,value⟩ := vertex_positions_equiv p M onPath
  let assigned := e.toEmbedding.trans attach
  have touching (i : marks) : G.Adj p.support[i.val.val] (assigned i).val := by
    rw [value]
    exact edges (e i)
  have routes (i j : marks) (ne : i≠j) :
      ∃ q : (G.induce (K : Set V)).Walk (assigned i) (assigned j), q.IsHamiltonian :=
    selected (e i) (e j) (e.injective.ne ne)
  have card : marks.card=M.card := by simpa using Fintype.card_congr e
  have bound := exterior_selected_port_matching p hp longest K outside marks
    (by omega) assigned touching routes
  rwa [card] at bound

#print axioms selected_vertex_matching_order

#print axioms exterior_vertex_matching_order
end Graph189ExteriorGap
