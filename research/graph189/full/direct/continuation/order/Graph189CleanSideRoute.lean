import Graph189MarkedLowCut

open SimpleGraph Finset Graph189DenseSideRoute
namespace Graph189CleanSideRoute
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One private contact per vertex bounds the degree lost to a pair of
separator vertices. Deleting a possible low vertex costs one more. -/
theorem loss {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) {p q : V}
    (pair : S={p,q}) (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q))
    (x : A) : G.degree x.val≤(G.induce (A:Set V)).degree x+1 := by
  classical
  let N := G.neighborFinset x.val
  let T := S.filter (G.Adj x.val)
  have one : T.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    obtain ⟨us,xu⟩ := mem_filter.mp hu
    obtain ⟨vs,xv⟩ := mem_filter.mp hv
    have cases (w : V) (ws : w∈S) : w=p ∨ w=q := by simpa [pair] using ws
    rcases cases u us with rfl|rfl <;> rcases cases v vs with rfl|rfl
    · rfl
    · exact (free _ x.property ⟨xu,xv⟩).elim
    · exact (free _ x.property ⟨xv,xu⟩).elim
    · rfl
  have sub : N⊆N.filter (fun v => v∈(A:Set V))∪T := by
    intro v hv
    have e := (G.mem_neighborFinset _ _).mp hv
    rcases sides.cover v with va|vb|vs
    · exact mem_union_left _ (mem_filter.mpr ⟨hv,va⟩)
    · exact (sides.no_cross _ x.property _ vb e).elim
    · exact mem_union_right _ (mem_filter.mpr ⟨vs,e⟩)
  have count := (card_le_card sub).trans (card_union_le _ _)
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  rw [←G.card_neighborFinset_eq_degree]
  exact count.trans (Nat.add_le_add_left one _)

theorem high_route (A : Finset V) (i : V) {k r : ℕ} (large : 26≤k) (few : r≤7)
    (con : (G.induce (A:Set V)).Connected)
    (min : ∀v : A,k-1≤(G.induce (A:Set V)).degree v)
    (size : A.card≤2*k-2+r) (marks : 4≤(A.filter (G.Adj i)).card)
    (miss : (A.filter (fun v => ¬G.Adj i v)).card≤k-1+r) :
    Route G A i (2*r+1) := by
  classical
  have upper := card_le_card (filter_subset (G.Adj i) A)
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<(A.filter (G.Adj i)).card by omega)
  obtain ⟨a,b,w,hw,start,inside,len⟩ := from_region A i (d:=k-1) (b:=r) (t:=r+1)
    (by omega) min (by omega) (by omega) (Or.inr con)
    ⟨x,(mem_filter.mp hx).1,(mem_filter.mp hx).2⟩ (by omega) (by omega)
  exact ⟨a,b,w,hw,start,inside,by omega⟩

/-- If deleting the low vertex disconnects this side, the two dense end
pieces have a marked spanning route. Otherwise rotate a longest path
in its connected high part and charge the low vertex to the loss. -/
theorem low_route (A : Finset V) (i : V) {k r : ℕ} (large : 26≤k) (few : r≤7)
    (con : (G.induce (A:Set V)).Connected) {z : V} (za : z∈A)
    (min : ∀v : A,v.val≠z → k-1≤(G.induce (A:Set V)).degree v)
    (size : A.card≤2*k-2+r) (enough : 4≤(A.filter (G.Adj i)).card)
    (miss : (A.filter (fun v => ¬G.Adj i v)).card≤k-1+r) :
    Route G A i (2*r+3) := by
  classical
  let R := A.erase z
  let J := G.induce (A:Set V)
  let z' : A := ⟨z,za⟩
  have sz : R.card+1=A.card := card_erase_add_one za
  have remote := (card_le_card (filter_subset_filter (fun v => ¬G.Adj i v) (erase_subset z A))).trans miss
  change (R.filter (fun v => ¬G.Adj i v)).card≤k-1+r at remote
  have drop : A.filter (G.Adj i) ⊆ insert z (R.filter (G.Adj i)) := by
    intro x hx
    by_cases eq : x=z
    · exact mem_insert.mpr (Or.inl eq)
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_erase.mpr ⟨eq,(mem_filter.mp hx).1⟩,(mem_filter.mp hx).2⟩)
  have remain := (card_le_card drop).trans (card_insert_le z _)
  have inside := card_le_card (filter_subset (G.Adj i) R)
  have minR (v : R) : k-2≤(G.induce (R:Set V)).degree v := by
    let a : A := ⟨v.val,(mem_erase.mp v.property).2⟩
    have h := min a (mem_erase.mp v.property).1
    rw [Graph189ExteriorDegreeCycle.degree_induce_filter] at h ⊢
    let X := (G.neighborFinset v.val).filter (fun w => w∈(A:Set V))
    let Y := (G.neighborFinset v.val).filter (fun w => w∈(R:Set V))
    have inc : X ⊆ insert z Y := by
      intro w hw
      by_cases eq : w=z
      · exact mem_insert.mpr (Or.inl eq)
      · exact mem_insert_of_mem (mem_filter.mpr ⟨(mem_filter.mp hw).1,mem_erase.mpr ⟨eq,(mem_filter.mp hw).2⟩⟩)
    have cnt := (card_le_card inc).trans (card_insert_le z Y)
    change k-1≤X.card at h
    change k-2≤Y.card
    omega
  obtain ⟨v,mv⟩ := card_pos.mp (show 0<(R.filter (G.Adj i)).card by omega)
  by_cases ok : R.card≤2*(k-2)+1 ∨ (G.induce (R:Set V)).Connected
  · obtain ⟨a,b,w,hw,iv,range,len⟩ := from_region R i (d:=k-2) (t:=r+2) (b:=r) (by omega)
      minR (by omega) (by omega) ok ⟨v,(mem_filter.mp mv).1,(mem_filter.mp mv).2⟩ (by omega) (by omega)
    exact ⟨a,b,w,hw,iv,fun v hv => (mem_erase.mp (range v hv)).2,by omega⟩
  push_neg at ok
  have growth := ok.1
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  let P := (A.filter (G.Adj i)).subtype (fun v => v∈A)
  have cardP : P.card=(A.filter (G.Adj i)).card := by
    rw [show P=(A.filter (G.Adj i)).subtype (fun v => v∈A) from rfl,card_subtype,
      filter_eq_self.mpr (fun v h => (mem_filter.mp h).1)]
  have marks : 3≤(P.erase z').card := by
    by_cases zP : z'∈P
    · have er := card_erase_add_one zP
      omega
    · rw [erase_eq_of_notMem zP]
      omega
  have disc : ¬(J.induce {v : A | v∉({z'}:Finset A)}).Connected := by
    intro connected
    let f : (J.induce {v : A | v∉({z'}:Finset A)}) →g G.induce (R:Set V) :=
      { toFun := fun v => ⟨v.val.val,mem_erase.mpr ⟨fun eq => v.property (mem_singleton.mpr (Subtype.ext eq)),v.val.property⟩⟩
        map_rel' := fun h => h }
    apply ok.2 (SimpleGraph.Connected.map f (fun v => ?_) connected)
    have vr := mem_erase.mp v.property
    refine ⟨⟨⟨v.val,vr.2⟩,fun eq => vr.1 (congrArg Subtype.val (mem_singleton.mp eq))⟩,rfl⟩
  have minJ (v : A) (diff : v≠z') : k-2+1≤J.degree v := by
    have h := min v (fun eq => diff (Subtype.ext eq))
    omega
  obtain ⟨a,aP,b,q,hq⟩ := Graph189MarkedLowCut.of_cut (G:=J) con z' P (d:=k-2) (by omega)
    minJ (by rw [Fintype.card_coe]; omega) marks disc
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let result := q.map f
  have aports : a.val∈A.filter (G.Adj i) := mem_subtype.mp aP
  refine ⟨_,_,result,hq.isPath.map Subtype.val_injective,(mem_filter.mp aports).2,?_,?_⟩
  · intro v hv
    rw [show result.support=q.support.map f from Walk.support_map _ _] at hv
    obtain ⟨v',_,rfl⟩ := List.mem_map.mp hv
    exact v'.property
  · have eq : result.support.length=q.support.length := by simp [result]
    rw [eq,hq.length_support,Fintype.card_coe]
    omega

#print axioms low_route
end Graph189CleanSideRoute
