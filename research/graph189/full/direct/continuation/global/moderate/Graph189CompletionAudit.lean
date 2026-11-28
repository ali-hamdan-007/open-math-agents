import Graph189CompletionRows
import Graph189CompletionIso

open SimpleGraph Graph189Completion

/-- A concrete list certificate in a nontrivial lower graph. It remains a
forbidden four-vertex path in all of its completions. -/
private theorem four_path :
    HasPath ((edge (0 : Fin 4) 1⊔edge 1 2)⊔edge 2 3) 4 := by
  apply hasPath_of_list (a:=(0:Fin 4)) (l:=[1,2,3])
  · simp [List.isChain_cons_cons,edge_adj,SimpleGraph.sup_adj]
  · decide
  · decide

example (required : Fin 4→ℕ) : Rejection (0:Fin 4) 4 5 4 required
    ((edge (0 : Fin 4) 1⊔edge 1 2)⊔edge 2 3) ⊤ := .path (Or.inl four_path)

private abbrev masks4 : List ℕ := [2,5,10,4]
private abbrev chain4 := maskGraph 4 masks4
private theorem present4 : RowsRepresent (maskRows masks4) chain4 :=
  maskRows_represent masks4 (by decide) (by decide)

/-- These small examples use the exact bit-row presentation of generated
certificates, including forcing, deleted connectivity, and the even cap. -/
example : Rejection (0:Fin 4) 9 9 10 (fun _ => 1) ⊥ chain4 := by
  apply Rejection.force_row present4 0 1 (by decide) (by decide)
  exact Rejection.cut_row present4 1 {0} (a:=0) (b:=2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example : Rejection (0:Fin 4) 9 9 0 (fun _ => 1) chain4 chain4 :=
  Rejection.even_row present4 present4 0 (by decide)

example : Rejection (0:Fin 4) 9 9 10 (fun _ => 2) ⊥ chain4 :=
  Rejection.degree_row present4 0 (by decide)

example : Rejection (0:Fin 4) 9 9 0 (fun _ => 1) chain4 chain4 :=
  .even 0 (present4.excess_of_pairs present4 0 [(2,1)] (by decide) (by decide) (by decide))

example : HasPath (chain4.induce {v | v≠3}) 3 :=
  present4.path_induce_of_list (a:=0) (l:=[1,2]) (by decide) (by decide) (by decide) (by decide)

private abbrev cycleMasks : List ℕ := [10,5,10,5]
private theorem cycleRep : RowsRepresent (maskRows cycleMasks) (maskGraph 4 cycleMasks) :=
  maskRows_represent cycleMasks (by decide) (by decide)

example : chain4 ⊔ edge 0 3 = maskGraph 4 cycleMasks :=
  present4.add_eq cycleRep 0 3 (by decide)

example : maskGraph 4 cycleMasks \ edge 0 3 = chain4 :=
  cycleRep.remove_eq present4 0 3 (by decide)

#check Graph189Completion.Rejection.sound
#print axioms Graph189Completion.hasPath_of_list
#print axioms Graph189Completion.hasPath_induce_of_list
#print axioms Graph189Completion.saturated_neighbors
#print axioms Graph189Completion.forcedTwo_card_le
#print axioms Graph189Completion.Rejection.sound

#print axioms Graph189Completion.Rejection.excludes_relabel
#print axioms Graph189Completion.RowsRepresent.disconnected_after_delete
#print axioms Graph189Completion.RowsRepresent.excess_of_pairs
#print axioms Graph189Completion.RowsRepresent.add_eq
#print axioms Graph189Completion.Rejection.cut_row
#print axioms Graph189Completion.Rejection.even_row
