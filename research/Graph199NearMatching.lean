import Graph199Matching

namespace Graph199
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend a graph by one universal vertex, to represent a single unmatched
vertex by the mate of the apex. -/
def withApex (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | some _, none | none, some _ => True
    | some x, some y => G.Adj x y
  symm := by constructor; rintro (_|x) (_|y) h <;> first | exact h | exact h.symm
  loopless := by constructor; rintro (_|x) <;> first | exact id | exact G.loopless.irrefl _

omit [DecidableEq V] in
theorem apex_perfect_matching_of_component_bound {G : SimpleGraph V} (he : Odd (Nat.card V))
    (hc : ∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) :
    ∃ M : (withApex G).Subgraph, M.IsPerfectMatching := by
  classical
  apply perfect_matching_of_component_bound
  · simp only [Nat.card_eq_fintype_card,Fintype.card_option] at he ⊢
    obtain ⟨k,hk⟩ := he
    exact ⟨k+1,by omega⟩
  intro U
  let K := (withApex G).induce ((U : Set (Option V))ᶜ)
  by_cases ha : none ∈ U
  · let B := U.eraseNone
    have heq (x : V) : x ∈ B ↔ some x ∈ U := Finset.mem_eraseNone
    let e : ↥((U : Set (Option V))ᶜ) ≃ ↥((B : Set V)ᶜ) :=
      { toFun := fun x => match x with
          | ⟨none,h⟩ => (h ha).elim
          | ⟨some v,h⟩ => ⟨v,fun hb => h ((heq v).mp hb)⟩
        invFun := fun x => ⟨some x.val,fun h => x.property ((heq x.val).mpr h)⟩
        left_inv := by rintro ⟨_|v,h⟩; exact (h ha).elim; rfl
        right_inv := by intro; rfl }
    let f : K ≃g G.induce ((B : Set V)ᶜ) :=
      ⟨e,by
        rintro ⟨_|x,hx⟩ ⟨_|y,hy⟩
        · exact (hx ha).elim
        · exact (hx ha).elim
        · exact (hy ha).elim
        · rfl⟩
    have h := hc B
    change Nat.card K.ConnectedComponent ≤ _
    rw [Nat.card_congr f.connectedComponentEquiv]
    exact h.trans (Nat.succ_le_succ (Finset.card_eraseNone_le U))
  · let z : ↥((U : Set (Option V))ᶜ) := ⟨none,ha⟩
    have hz (x : ↥((U : Set (Option V))ᶜ)) : K.Reachable z x := by
      rcases x with ⟨_|v,hv⟩
      · exact Reachable.rfl
      · exact (show K.Adj z ⟨some v,hv⟩ from trivial).reachable
    have conn : K.Preconnected := fun x y => (hz x).symm.trans (hz y)
    let _ : Subsingleton K.ConnectedComponent := conn.subsingleton_connectedComponent
    change Nat.card K.ConnectedComponent ≤ _
    let _ : Finite K.ConnectedComponent := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
    let _ := Fintype.ofFinite K.ConnectedComponent
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_le_one_iff_subsingleton.mpr inferInstance).trans (by omega)

omit [Fintype V] [DecidableEq V] in
/-- A matching of the apex extension restricts to a matching which misses
exactly the neighbor of the apex. -/
theorem matching_missing_one_of_apex {G : SimpleGraph V}
    (hp : ∃ M : (withApex G).Subgraph, M.IsPerfectMatching) :
    ∃ a : V, ∃ N : G.Subgraph, N.IsMatching ∧ N.verts = {a}ᶜ := by
  classical
  obtain ⟨M,hM⟩ := hp
  have huniq := Subgraph.isPerfectMatching_iff.mp hM
  obtain ⟨a,ha,hu⟩ := huniq none
  cases a with
  | none => exact (M.loopless.irrefl _ ha).elim
  | some a =>
    have avoid {x y : V} (h : M.Adj (some x) (some y)) : x ≠ a := by
      rintro rfl
      obtain ⟨w,_,hw⟩ := huniq (some x)
      have he := (hw (some y) h).trans (hw none (M.adj_symm ha)).symm
      cases he
    let N : G.Subgraph := {
      verts := {a}ᶜ
      Adj := fun x y => M.Adj (some x) (some y)
      adj_sub := fun h => M.adj_sub h
      edge_vert := fun h => avoid h
      symm := ⟨fun _ _ h => M.adj_symm h⟩ }
    refine ⟨a,N,?_,rfl⟩
    intro x hx
    obtain ⟨w,hw,hxw⟩ := huniq (some x)
    cases w with
    | none =>
      exact (hx (Option.some.inj (hu (some x) (M.adj_symm hw)))).elim
    | some w =>
      exact ⟨w,hw,fun t ht => Option.some.inj (hxw (some t) ht)⟩

/-- On an odd number of vertices the induced-tree criterion of Conjecture 199
guarantees a matching covering every vertex except one. -/
theorem near_perfect_matching_of_tree_bound [Nontrivial V] {G : SimpleGraph V}
    (hG : G.Connected) (he : Odd (Nat.card V))
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a : V, ∃ N : G.Subgraph, N.IsMatching ∧ N.verts = {a}ᶜ :=
  matching_missing_one_of_apex
    (apex_perfect_matching_of_component_bound he (all_separator_component_bound hG ht))

#print axioms near_perfect_matching_of_tree_bound
end Graph199
