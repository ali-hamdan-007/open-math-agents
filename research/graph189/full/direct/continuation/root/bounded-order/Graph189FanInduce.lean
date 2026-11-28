import Graph189FanLinkage

open SimpleGraph Finset
namespace Graph189FanCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Single-vertex deletions in the ambient type supply the intrinsic
vertex-two-connectivity predicate on the finite induced graph. -/
theorem induced_two_connected (S : Finset V) (three : 3≤S.card)
    (noncut : ∀ u∈S, (G.induce (S.erase u : Set V)).Preconnected) :
    (G.induce (S : Set V)).IsKConnected 2 := by
  classical
  let H := G.induce (S : Set V)
  have conn : H.Connected := by
    have pos : S.Nonempty := Finset.card_pos.mp (by omega)
    refine { preconnected := ?_, nonempty := ⟨⟨pos.choose,pos.choose_spec⟩⟩ }
    intro a b
    have few : ({a.val,b.val} : Finset V).card < S.card := (card_insert_le _ _).trans_lt (by simp; omega)
    obtain ⟨x,xS,sep⟩ := exists_mem_notMem_of_card_lt_card few
    have ae : a.val ∈ S.erase x := mem_erase.mpr ⟨fun eq => sep (by simp [eq]),a.property⟩
    have be : b.val ∈ S.erase x := mem_erase.mpr ⟨fun eq => sep (by simp [eq]),b.property⟩
    let f := (G.induceHomOfLE (show (S.erase x : Set V) ⊆ S from fun _ h => (mem_erase.mp h).2)).toHom
    exact ((noncut x xS) ⟨_,ae⟩ ⟨_,be⟩).map f
  refine ⟨by change 2 < Fintype.card S; rw [Fintype.card_coe]; omega,?_⟩
  intro D small
  by_cases empty : D=∅
  · subst D
    change (H.induce ((↑(∅ : Finset S) : Set S)ᶜ)).Connected
    rw [coe_empty,Set.compl_empty]
    exact H.induceUnivIso.connected_iff.mpr conn
  obtain ⟨z,rfl⟩ := Finset.card_eq_one.mp (show D.card=1 from by
    have e := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty); omega)
  let A := S.erase z.val
  let T : Set S := (({z} : Finset S) : Set S)ᶜ
  let f : (G.induce (A:Set V)) →g H.induce T := {
    toFun := fun v => ⟨⟨v.val,(mem_erase.mp v.property).2⟩,by
      change ¬ _ ∈ ({z}:Finset S)
      intro h
      have eq := congrArg (fun q : S => q.val) (mem_singleton.mp h)
      exact (mem_erase.mp v.property).1 eq⟩
    map_rel' := fun e => e }
  have up (v : T) : v.val.val ∈ A := mem_erase.mpr ⟨fun eq => v.property
    (show v.val∈({z}:Finset S) from mem_singleton.mpr (Subtype.ext eq)),v.val.property⟩
  obtain ⟨u,uS,uz⟩ := Finset.exists_mem_ne (show 1<S.card by omega) z.val
  refine { preconnected := ?_, nonempty := ⟨f ⟨u,mem_erase.mpr ⟨uz,uS⟩⟩⟩ }
  intro a b
  exact ((noncut z.val z.property) ⟨_,up a⟩ ⟨_,up b⟩).map f

/-- Every vertex of a finite two-connected graph has two neighbours. -/
theorem degree_two_of_connected (two : G.IsKConnected 2) (z : V) : 2 ≤ G.degree z := by
  classical
  by_contra! small
  let D := G.neighborFinset z
  have size : D.card < 2 := by simpa [D] using small
  have width := two.1
  have room : (insert z D).card < (univ : Finset V).card := by
    have le := card_insert_le z D
    rw [card_univ]; omega
  obtain ⟨b,_,outside⟩ := exists_mem_notMem_of_card_lt_card room
  have off : b∉D := fun h => outside (mem_insert_of_mem h)
  let Z : {v : V | v∉D} := ⟨z,by simp [D]⟩
  let B : {v : V | v∉D} := ⟨b,off⟩
  let _ : Nontrivial {v : V | v∉D} := ⟨⟨B,Z,fun eq => outside (mem_insert.mpr
    (Or.inl (congrArg (fun v : {v : V | v∉D} => v.val) eq)))⟩⟩
  obtain ⟨w,e⟩ := (two.2 D size).preconnected.exists_adj_of_nontrivial Z
  exact w.property ((G.mem_neighborFinset _ _).mpr e)

end Graph189FanCycle
#print axioms Graph189FanCycle.induced_two_connected
#print axioms Graph189FanCycle.degree_two_of_connected
