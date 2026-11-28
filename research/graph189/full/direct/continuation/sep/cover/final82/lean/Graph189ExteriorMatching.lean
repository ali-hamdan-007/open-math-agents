import Graph189MatchedOrder
import Mathlib.Data.Finset.Sort

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

omit [Fintype V] in
theorem route_of_induced_hamilton (p : G.Walk x y) (K : Finset V)
    (outside : ∀ z∈K, z∉p.support) {a b : K}
    {q : (G.induce (K : Set V)).Walk a b} (hq : q.IsHamiltonian) :
    ExteriorRoute p a.val b.val K.card := by
  let e := SimpleGraph.Embedding.induce (G := G) (K : Set V)
  let r := q.map e.toHom
  refine ⟨r, hq.isPath.map e.injective, ?_, ?_⟩
  · rw [List.disjoint_left]
    intro z hz hp
    change z∈(q.map e.toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact outside w.val w.property hp
  · change K.card≤(q.map e.toHom).support.length
    rw [Walk.support_map,List.length_map,hq.length_support]
    simp

/-- An arbitrary unordered family of distinct marked positions, together with
distinct actual contact vertices in an exterior Hamilton-connected induced graph,
forces the standard matched-core lower bound on the order. -/
theorem exterior_hamilton_connected_matching (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+2)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := longest_matched_route_order p hp longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at bound ⊢
  omega

/-- Only the selected distinct ports need spanning routes between them. When
there are at least two selected ports, each tail can use another selected port. -/
theorem exterior_selected_port_matching (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (outside : ∀ z∈K, z∉p.support)
    (marks : Finset (Fin p.support.length)) (two : 2 ≤ marks.card)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val)
    (selected : ∀ i j : marks, i≠j →
      ∃ q : (G.induce (K : Set V)).Walk (attach i) (attach j), q.IsHamiltonian) :
    (marks.card+2)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1,by omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have route (i l : Fin (j+1)) (ne : i≠l) : ExteriorRoute p (T i).val (T l).val K.card := by
    obtain ⟨q,hq⟩ := selected (iso i) (iso l) (iso.injective.ne ne)
    exact route_of_induced_hamilton p K outside hq
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (ne_of_lt i.castSucc_lt_succ)
  have ends_ne : (0 : Fin (j+1)) ≠ Fin.last j := by
    intro eq
    have he := congrArg Fin.val eq
    simp only [Fin.val_zero,Fin.val_last] at he
    omega
  have tail := route (Fin.last j) 0 ends_ne.symm
  have bound := longest_matched_route_order p hp longest M (fun i => (T i).val) touching inner
    ⟨(T (Fin.last j)).val,tail⟩ ⟨(T 0).val,tail⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at bound ⊢
  omega

#print axioms exterior_selected_port_matching

#print axioms exterior_hamilton_connected_matching
end Graph189ExteriorGap
