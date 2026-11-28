import Graph189ParentFocused
import Graph189ExteriorPopulation

namespace Graph189DeletionOrders
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The deletion path, its omitted vertices, and the deleted vertex partition the
ambient order. Here path order counts its vertices. -/
theorem deletion_partition (z : V) {x y : {v : V | v ≠ z}}
    (P : (G.induce {v : V | v ≠ z}).Walk x y) (hP : P.IsPath) :
    Fintype.card V = P.support.length +
      (univ.filter (fun v : {v : V | v ≠ z} => v ∉ P.support)).card + 1 := by
  classical
  let S := {v : V | v ≠ z}
  have part := card_filter_add_card_filter_not (s:=(univ : Finset S)) (p:=fun v => v ∈ P.support)
  have first : (univ.filter (fun v : S => v ∈ P.support)) = P.support.toFinset := by
    ext t
    simp
  rw [first,List.toFinset_card_of_nodup hP.support_nodup,card_univ] at part
  have del : Fintype.card S = Fintype.card V - 1 := by
    change Fintype.card {u : V // ¬u = z} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun u : V => u = z),Fintype.card_subtype_eq]
  let _ : Nonempty V := ⟨z⟩
  have pos : 0 < Fintype.card V := Fintype.card_pos
  let B := (univ : Finset S).filter (fun v : S => ¬v ∈ P.support)
  change P.support.length+B.card = Fintype.card S at part
  have h : Fintype.card V = P.support.length+B.card+1 := by omega
  refine h.trans ?_
  congr 1

variable [DecidableRel G.Adj]

/-- At a connected deletion with all retained vertices high, a longest path
that omits a vertex has the small-moderate search's lower path order and upper
omitted order. -/
theorem orders_of_high_deletion (z : V) {k : ℕ}
    (high : ∀ a : {v : V | v ≠ z}, k ≤ G.degree a.val)
    (hc : (G.induce {v : V | v ≠ z}).Connected)
    {x y : {v : V | v ≠ z}} (P : (G.induce {v : V | v ≠ z}).Walk x y)
    (hP : P.IsPath)
    (longest : ∀ {u v}, ∀ Q : (G.induce {v : V | v ≠ z}).Walk u v,
      Q.IsPath → Q.length ≤ P.length)
    (miss : ∃ a : {v : V | v ≠ z}, a ∉ P.support)
    (two : 2 ≤ P.support.length) (order : Fintype.card V ≤ 3*k+2) :
    let p := P.support.length
    let b := (univ.filter (fun v : {v : V | v ≠ z} => v ∉ P.support)).card
    Fintype.card V = p+b+1 ∧ 2*k-1 ≤ p ∧ b ≤ k+2 := by
  classical
  let S := {v : V | v ≠ z}
  let H := G.induce S
  let L := P.support
  let b := (univ.filter (fun v : S => v ∉ L)).card
  have part : Fintype.card V = L.length+b+1 := deletion_partition z P hP
  have bpos : 0 < b := by
    obtain ⟨a,ha⟩ := miss
    exact card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,ha⟩⟩
  have del : Fintype.card S = Fintype.card V - 1 := by
    change Fintype.card {u : V // ¬u = z} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun u : V => u = z),Fintype.card_subtype_eq]
  have less : L.length < Fintype.card S := by omega
  have maxList (l : List S) (nd : l.Nodup) (chain : l.IsChain H.Adj) : l.length ≤ L.length := by
    by_cases he : l = []
    · simp [he]
    let Q := Walk.ofSupport l he chain
    have qpath : Q.IsPath := Walk.IsPath.mk' (by simpa [Q,Walk.support_ofSupport] using nd)
    have h := longest Q qpath
    have hq : Q.length+1 = l.length := by
      rw [←Q.length_support]
      simp [Q,Walk.support_ofSupport]
    have hlen : L.length = P.length+1 := P.length_support
    omega
  have ore := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.lemma4
    (G:=H) hc L P.support_ne_nil hP.support_nodup P.isChain_adj_support maxList less two).2.2.1
  have head := Graph189ExteriorDegreeCycle.degree_le_deletion_add_one (G:=G) z (L.head P.support_ne_nil)
  have last := Graph189ExteriorDegreeCycle.degree_le_deletion_add_one (G:=G) z (L.getLast P.support_ne_nil)
  have hiHead := high (L.head P.support_ne_nil)
  have hiLast := high (L.getLast P.support_ne_nil)
  change G.degree (L.head P.support_ne_nil).val ≤ H.degree (L.head P.support_ne_nil)+1 at head
  change G.degree (L.getLast P.support_ne_nil).val ≤ H.degree (L.getLast P.support_ne_nil)+1 at last
  change Fintype.card V = L.length+b+1 ∧ 2*k-1 ≤ L.length ∧ b ≤ k+2
  omega

variable [Nontrivial V]

/-- A minimum-degree deletion retains only high vertices in the original graph. -/
theorem orders_at_minimum (z : V) (minimum : G.degree z = G.minDegree)
    (hc : (G.induce {v : V | v ≠ z}).Connected)
    {x y : {v : V | v ≠ z}} (P : (G.induce {v : V | v ≠ z}).Walk x y)
    (hP : P.IsPath)
    (longest : ∀ {u v}, ∀ Q : (G.induce {v : V | v ≠ z}).Walk u v,
      Q.IsPath → Q.length ≤ P.length)
    (miss : ∃ a : {v : V | v ≠ z}, a ∉ P.support)
    (two : 2 ≤ P.support.length) (order : Fintype.card V ≤ 3*G.secondSmallestDegree+2) :
    let p := P.support.length
    let b := (univ.filter (fun v : {v : V | v ≠ z} => v ∉ P.support)).card
    Fintype.card V = p+b+1 ∧ 2*G.secondSmallestDegree-1 ≤ p ∧ b ≤ G.secondSmallestDegree+2 := by
  have high (a : {v : V | v ≠ z}) : G.secondSmallestDegree ≤ G.degree a.val := by
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.degree_pair
      (G:=G) a.val z a.property with h | h
    · exact h
    · exact h.trans (minimum.symm ▸ G.minDegree_le_degree a.val)
  exact orders_of_high_deletion z high hc P hP longest miss two order

omit [Nontrivial V] [DecidableRel G.Adj] in
/-- Transport the original-graph gap through the injective induced embedding. -/
theorem omitted_lower_of_original_gap (z : V) {k : ℕ}
    {x y : {v : V | v ≠ z}} (P : (G.induce {v : V | v ≠ z}).Walk x y) (hP : P.IsPath)
    (gap : ∀ a b, ∀ Q : G.Walk a b, Q.IsPath → Q.support.length+(k+1)/2+2 ≤ Fintype.card V) :
    (k+1)/2+1 ≤ (univ.filter (fun v : {v : V | v ≠ z} => v ∉ P.support)).card := by
  classical
  let S := {v : V | v ≠ z}
  let f := (Embedding.induce (G:=G) S).toHom
  have qp := (Walk.isPath_map_iff_of_injective (p:=P) (f:=f) Subtype.val_injective).mpr hP
  have h := gap _ _ (P.map f) qp
  rw [Walk.support_map,List.length_map] at h
  have part := deletion_partition z P hP
  omega

/-- All search-order constraints, with the genuine original path gap supplied
as a separate hypothesis. -/
theorem orders_at_minimum_with_gap (z : V) (minimum : G.degree z = G.minDegree)
    (hc : (G.induce {v : V | v ≠ z}).Connected)
    {x y : {v : V | v ≠ z}} (P : (G.induce {v : V | v ≠ z}).Walk x y)
    (hP : P.IsPath)
    (longest : ∀ {u v}, ∀ Q : (G.induce {v : V | v ≠ z}).Walk u v,
      Q.IsPath → Q.length ≤ P.length)
    (miss : ∃ a : {v : V | v ≠ z}, a ∉ P.support)
    (two : 2 ≤ P.support.length) (order : Fintype.card V ≤ 3*G.secondSmallestDegree+2)
    (gap : ∀ a b, ∀ Q : G.Walk a b, Q.IsPath →
      Q.support.length+(G.secondSmallestDegree+1)/2+2 ≤ Fintype.card V) :
    let p := P.support.length
    let b := (univ.filter (fun v : {v : V | v ≠ z} => v ∉ P.support)).card
    Fintype.card V = p+b+1 ∧ 2*G.secondSmallestDegree-1 ≤ p ∧
      (G.secondSmallestDegree+1)/2+1 ≤ b ∧ b ≤ G.secondSmallestDegree+2 := by
  obtain ⟨part,lower,upper⟩ := orders_at_minimum z minimum hc P hP longest miss two order
  exact ⟨part,lower,omitted_lower_of_original_gap z P hP gap,upper⟩

/-- The exact half-open ranges and total-order guard in the finite search. -/
theorem search_loop_bounds {n k p b : ℕ} (hk : 3 ≤ k) (part : n = p+b+1)
    (lo : 2*k-1 ≤ p) (gap : (k+1)/2+1 ≤ b) (hi : n ≤ 3*k+2) :
    (k+1)/2+1 ≤ b ∧ b ≤ k+2 ∧ 2*k-1 ≤ p ∧ p < 3*k+2-b ∧ 2*k+3 ≤ p+b+1 := by
  omega

#print axioms orders_of_high_deletion
#print axioms orders_at_minimum_with_gap
#print axioms search_loop_bounds
end Graph189DeletionOrders
