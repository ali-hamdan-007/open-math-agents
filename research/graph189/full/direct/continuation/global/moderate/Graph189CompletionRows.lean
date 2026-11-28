import Graph189CompletionCertificate

namespace Graph189Completion
open SimpleGraph Finset
variable {V : Type*}

/-- A finite row presents the entire open neighborhood. -/
def RowsRepresent (rows : V→Finset V) (G : SimpleGraph V) : Prop :=
  ∀ x y, y∈rows x ↔ G.Adj x y

/-- Named intermediate graphs can be checked against an edge update using
only decidable row membership on the finite vertex type. -/
theorem RowsRepresent.add_eq {G H : SimpleGraph V} {old new : V→Finset V}
    (before : RowsRepresent old G) (after : RowsRepresent new H) (a b : V)
    (update : ∀ x y, y∈new x ↔ y∈old x ∨ ((x=a ∧ y=b ∨ x=b ∧ y=a) ∧ x≠y)) :
    G⊔edge a b=H := by
  ext x y
  rw [sup_adj,edge_adj,←before x y,←after x y]
  exact (update x y).symm

theorem RowsRepresent.remove_eq {G H : SimpleGraph V} {old new : V→Finset V}
    (before : RowsRepresent old G) (after : RowsRepresent new H) (a b : V)
    (update : ∀ x y, y∈new x ↔ y∈old x ∧ ¬((x=a ∧ y=b ∨ x=b ∧ y=a) ∧ x≠y)) :
    G\edge a b=H := by
  ext x y
  rw [sdiff_adj,edge_adj,←before x y,←after x y]
  exact (update x y).symm

theorem RowsRepresent.path_of_list {G : SimpleGraph V} {rows : V→Finset V}
    (rep : RowsRepresent rows G) {a : V} {l : List V} {t : ℕ}
    (chain : (a::l).IsChain (fun x y => y∈rows x)) (unique : (a::l).Nodup)
    (length : t≤(a::l).length) : HasPath G t :=
  hasPath_of_list (chain.imp (fun x y => (rep x y).mp)) unique length

theorem RowsRepresent.path_induce_of_list {G : SimpleGraph V} {rows : V→Finset V}
    (rep : RowsRepresent rows G) {S : Set V} {a : V} {l : List V} {t : ℕ}
    (inside : ∀ v∈a::l, v∈S) (chain : (a::l).IsChain (fun x y => y∈rows x))
    (unique : (a::l).Nodup) (length : t≤(a::l).length) : HasPath (G.induce S) t :=
  hasPath_induce_of_list inside (chain.imp (fun x y => (rep x y).mp)) unique length

section Finite
variable [Fintype V] [DecidableEq V] {G L U : SimpleGraph V}

omit [DecidableEq V] in
theorem RowsRepresent.degree_eq {rows : V→Finset V} (h : RowsRepresent rows G)
    [DecidableRel G.Adj] (v : V) : G.degree v=(rows v).card := by
  have eq : G.neighborFinset v=rows v := by
    ext y
    exact (G.mem_neighborFinset v y).trans (h v y).symm
  rw [←G.card_neighborFinset_eq_degree,eq]

/-- The union of the lower rows of the lower neighbors, with the upper
neighbors and the origin removed. This is the checker's exact bitmask. -/
def rowTwo (low high : V→Finset V) (x : V) : Finset V :=
  ((low x).biUnion low \ high x).erase x

theorem RowsRepresent.forcedTwo_eq {low high : V→Finset V}
    (lo : RowsRepresent low L) (hi : RowsRepresent high U) (x : V) :
    forcedTwo L U x=rowTwo low high x := by
  classical
  ext y
  simp only [forcedTwo,mem_filter,mem_univ,true_and,rowTwo,mem_erase,mem_sdiff,mem_biUnion]
  constructor
  · rintro ⟨ne,miss,v,xv,yv⟩
    exact ⟨ne.symm,⟨v,(lo x v).mpr xv,(lo v y).mpr yv.symm⟩,fun hy => miss ((hi x y).mp hy)⟩
  · rintro ⟨ne,⟨v,hv,hy⟩,miss⟩
    exact ⟨ne.symm,fun e => miss ((hi x y).mpr e),v,(lo x v).mp hv,((lo v y).mp hy).symm⟩

omit [DecidableEq V] in
/-- A list of (target, middle) pairs certifies a violation without computing
any graph distance or the whole distance-two shell. -/
theorem RowsRepresent.excess_of_pairs {low high : V→Finset V}
    (lo : RowsRepresent low L) (hi : RowsRepresent high U) (x : V) {k : ℕ}
    (pairs : List (V×V)) (distinct : (pairs.map Prod.fst).Nodup) (size : k<pairs.length)
    (witness : ∀ t∈pairs, x≠t.1 ∧ t.1∉high x ∧ t.2∈low x ∧ t.1∈low t.2) :
    k<(forcedTwo L U x).card := by
  classical
  have inc : (pairs.map Prod.fst).toFinset ⊆ forcedTwo L U x := by
    intro y hy
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    obtain ⟨ne,missing,first,second⟩ := witness t ht
    simp only [forcedTwo,mem_filter,mem_univ,true_and]
    exact ⟨ne,fun e => missing ((hi _ _).mpr e),t.2,
      (lo _ _).mp first,((lo _ _).mp second).symm⟩
  have count := card_le_card inc
  rw [List.toFinset_card_of_nodup distinct,List.length_map] at count
  exact size.trans_le count

end Finite

/-- Two surviving representatives separated by a row-closed subset witness
disconnection of the upper graph after deleting z. The subset may contain z. -/
theorem RowsRepresent.disconnected_after_delete {U : SimpleGraph V} {rows : V→Finset V}
    (hi : RowsRepresent rows U) (z : V) (C : Finset V) {a b : V}
    (az : a≠z) (bz : b≠z) (ha : a∈C) (hb : b∉C)
    (closed : ∀ x∈C, ∀ y∈rows x, y≠z → y∈C) :
    ¬(U.induce {x | x≠z}).Connected := by
  intro conn
  let T : Set V := {x | x≠z}
  have stay {u v : T} (P : (U.induce T).Walk u v) : u.val∈C → v.val∈C := by
    induction P with
    | nil => exact id
    | @cons u v w e P ih =>
      intro seen
      exact ih (closed u.val seen v.val ((hi _ _).mpr e) v.property)
  obtain ⟨P⟩ := conn (⟨a,az⟩ : T) (⟨b,bz⟩ : T)
  exact hb (stay P ha)

/-- A checker row is the natural number whose j-th bit records vertex j. -/
def maskRows {n : ℕ} (rows : List ℕ) (v : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => (rows.getD v.val 0).testBit w.val = true)

def maskGraph (n : ℕ) (rows : List ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun v w : Fin n => (rows.getD v.val 0).testBit w.val = true)

instance {n : ℕ} (rows : List ℕ) : DecidableRel (maskGraph n rows).Adj := by
  unfold maskGraph
  infer_instance

theorem maskRows_represent {n : ℕ} (rows : List ℕ)
    (symm : ∀ x y : Fin n, (rows.getD x.val 0).testBit y.val=(rows.getD y.val 0).testBit x.val)
    (loopless : ∀ x : Fin n, (rows.getD x.val 0).testBit x.val=false) :
    RowsRepresent (maskRows rows) (maskGraph n rows) := by
  intro x y
  simp only [maskRows,mem_filter,mem_univ,true_and,maskGraph,fromRel_adj]
  constructor
  · intro e
    exact ⟨fun h => by subst y; rw [loopless] at e; contradiction,Or.inl e⟩
  · rintro ⟨_,h|h⟩
    · exact h
    · exact (symm x y).trans h

section Rules
open scoped Classical
variable [Fintype V] {L U : SimpleGraph V} {z : V} {f d k : ℕ} {req : V→ℕ}

theorem Rejection.degree_row {high : V→Finset V} (hi : RowsRepresent high U) (v : V)
    (small : (high v).card<req v) : Rejection z f d k req L U :=
  .degree v (by rwa [hi.degree_eq])

theorem Rejection.force_row {high : V→Finset V} (hi : RowsRepresent high U) (a b : V)
    (possible : b∈high a) (tight : (high a).card=req a)
    (child : Rejection z f d k req (L⊔edge a b) U) : Rejection z f d k req L U :=
  .force a b ((hi a b).mp possible) (by rwa [hi.degree_eq]) child

theorem Rejection.cut_row {high : V→Finset V} (hi : RowsRepresent high U) (v : V)
    (C : Finset V) {a b : V} (av : a≠v) (bv : b≠v) (ha : a∈C) (hb : b∉C)
    (closed : ∀ x∈C, ∀ y∈high x, y≠v → y∈C) : Rejection z f d k req L U :=
  .cut v (hi.disconnected_after_delete v C av bv ha hb closed)

theorem Rejection.even_row {low high : V→Finset V} (lo : RowsRepresent low L)
    (hi : RowsRepresent high U) (v : V) (excess : k<(rowTwo low high v).card) :
    Rejection z f d k req L U :=
  .even v (by rwa [lo.forcedTwo_eq hi])

end Rules
end Graph189Completion
#print axioms Graph189Completion.RowsRepresent.degree_eq
#print axioms Graph189Completion.RowsRepresent.forcedTwo_eq
#print axioms Graph189Completion.RowsRepresent.disconnected_after_delete
#print axioms Graph189Completion.maskRows_represent
