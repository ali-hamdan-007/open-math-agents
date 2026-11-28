import Graph189ConnectedMarkedRoute
import Graph189MarkedLowCut

open SimpleGraph Finset Graph189DenseSideRoute
namespace Graph189BalancedSideRoutes
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

private theorem retained_at (W T : Finset V) (a : W)
    (exit : ∀y,G.Adj a.val y → y∉W → y∈T) :
    G.degree a.val≤(G.induce (W:Set V)).degree a+T.card := by
  classical
  let N := (G.neighborFinset a.val).filter (fun y => y∈(W:Set V))
  have sub : G.neighborFinset a.val⊆N∪T := by
    intro y h
    by_cases wy : y∈W
    · exact mem_union_left _ (mem_filter.mpr ⟨h,wy⟩)
    · exact mem_union_right _ (exit y ((G.mem_neighborFinset _ _).mp h) wy)
  have count := (card_le_card sub).trans (card_union_le _ _)
  rw [G.card_neighborFinset_eq_degree] at count
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  exact count

private theorem mark_count (W : Finset V) (pred : V → Prop) [DecidablePred pred] :
    ((W.filter pred).subtype (fun v => v∈W)).card=(W.filter pred).card := by
  rw [card_subtype,filter_eq_self.mpr (fun v h => (mem_filter.mp h).1)]

private theorem outside (sides : Graph189CutSides.CutSides G A B S) {x y : V}
    (xa : x∈A) (e : G.Adj x y) (ya : y∉A) : y∈S := by
  rcases sides.cover y with h|h|h
  · exact (ya h).elim
  · exact (sides.no_cross x xa y h e).elim
  · exact h

/-- A wholly high balanced side begins at a contact of either prescribed
anchor and loses at most three vertices, including when it has common ports. -/
theorem high {k : ℕ} (large : 10≤k) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (con : (G.induce (A:Set V)).Connected)
    (minimum : ∀x∈A,k≤G.degree x) (size : A.card+1≤2*k) (marks : 2≤(A.filter (G.Adj p)).card) :
    Route G A p 3 := by
  classical
  let H := G.induce (A:Set V)
  let P := (A.filter (G.Adj p)).subtype (fun v => v∈A)
  have cardP : P.card=(A.filter (G.Adj p)).card := mark_count A (G.Adj p)
  have fit := card_le_univ P
  rw [Fintype.card_coe] at fit
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have sz : S.card=2 := by simp [pair,ne]
  have minH (v : A) : k-2≤H.degree v := by
    have h := retained_at A S v (fun y e h => outside sides v.property e h)
    have d := minimum v.val v.property
    change G.degree v.val≤H.degree v+S.card at h
    omega
  have strong (v : A) (absent : v∉P) : k-1≤H.degree v := by
    have np : ¬G.Adj p v.val := fun e => absent (mem_subtype.mpr (mem_filter.mpr ⟨v.property,e⟩))
    have h := retained_at A {q} v (fun y e h => by
      have sy := outside sides v.property e h
      rcases (show y=p ∨ y=q by simpa [pair] using sy) with rfl|eq
      · exact (np e.symm).elim
      · exact mem_singleton.mpr eq)
    have d := minimum v.val v.property
    change G.degree v.val≤H.degree v+({q}:Finset V).card at h
    rw [card_singleton] at h
    omega
  obtain ⟨x,xP,y,w,hw,len⟩ := Graph189ConnectedMarkedRoute.route con P (card_pos.mp (by omega))
    (d:=k-2) (u:=k-1) (loss:=2) (by omega) minH strong
    (by change Fintype.card A≤2*(k-2)+1+2; rw [Fintype.card_coe]; omega)
    (by change Fintype.card A<2*(k-1)+P.card; rw [Fintype.card_coe]; omega)
  let f := (Embedding.induce (G:=G) (A:Set V)).toHom
  let r := w.map f
  refine ⟨_,_,r,hw.map Subtype.val_injective,(mem_filter.mp (mem_subtype.mp xP)).2,?_,?_⟩
  · intro v seen
    rw [show r.support=w.support.map f from Walk.support_map _ _] at seen
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp seen
    exact u.property
  · change Fintype.card A≤w.support.length+(2+1) at len
    rw [Fintype.card_coe] at len
    have mapped : r.support.length=w.support.length := by simp [r]
    omega

/-- A balanced side containing the possible low vertex starts from an
actual port and loses at most five vertices. -/
theorem exceptional {k : ℕ} (large : 10≤k) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (con : (G.induce (A:Set V)).Connected) {z : V} (za : z∈A)
    (minimum : ∀x∈A,x≠z → k≤G.degree x) (size : A.card+1≤2*k)
    (marks : 4≤(A.filter (fun v => ∃i∈S,G.Adj i v)).card) :
    ∃i∈S,Route G A i 5 := by
  classical
  let P := A.filter (fun v => ∃i∈S,G.Adj i v)
  let W := A.erase z
  let H := G.induce (A:Set V)
  let J := G.induce (W:Set V)
  let z' : A := ⟨z,za⟩
  let PA := P.subtype (fun v => v∈A)
  let M := (W.filter (fun v => ∃i∈S,G.Adj i v)).subtype (fun v => v∈W)
  change 4≤P.card at marks
  have mA : PA.card=P.card := mark_count A _
  have cardW : W.card+1=A.card := card_erase_add_one za
  have cardM : M.card=(W.filter (fun v => ∃i∈S,G.Adj i v)).card := mark_count W _
  have mfit := card_le_univ PA
  rw [Fintype.card_coe] at mfit
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  letI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have survivors : 3≤(PA.erase z').card := by
    by_cases inside : z'∈PA
    · have eq := card_erase_add_one inside
      omega
    · rw [erase_eq_of_notMem inside]
      omega
  have active : M.Nonempty := by
    have keep : P ⊆ insert z (W.filter (fun v => ∃i∈S,G.Adj i v)) := by
      intro u hu
      by_cases eq : u=z
      · exact mem_insert.mpr (Or.inl eq)
      · obtain ⟨ua,i,si,iu⟩ := mem_filter.mp hu
        exact mem_insert_of_mem (mem_filter.mpr ⟨mem_erase.mpr ⟨eq,ua⟩,i,si,iu⟩)
    have bound := (card_le_card keep).trans (card_insert_le _ _)
    exact card_pos.mp (by omega)
  have sz : S.card=2 := by simp [pair,ne]
  have degA (v : A) (different : v≠z') : k-3+1≤H.degree v := by
    have h := retained_at A S v (fun y e h => outside sides v.property e h)
    have d := minimum v.val v.property (fun e => different (Subtype.ext e))
    change G.degree v.val≤H.degree v+S.card at h
    omega
  by_cases connected : J.Connected
  swap
  · let K := H.induce {v : A | v∉({z'}:Finset A)}
    have disc : ¬K.Connected := by
      intro c
      let f : K →g J :=
        { toFun := fun v => ⟨v.val.val,mem_erase.mpr ⟨fun eq => v.property (mem_singleton.mpr (Subtype.ext eq)),v.val.property⟩⟩
          map_rel' := fun h => h }
      apply connected (SimpleGraph.Connected.map f (fun v => ?_) c)
      have vr := mem_erase.mp v.property
      exact ⟨⟨⟨v.val,vr.2⟩,fun eq => vr.1 (congrArg Subtype.val (mem_singleton.mp eq))⟩,rfl⟩
    obtain ⟨x,xP,y,w,hw⟩ := Graph189MarkedLowCut.of_cut con z' PA (by omega : 2≤k-3)
      degA (by change Fintype.card A≤3*(k-3); rw [Fintype.card_coe]; omega) survivors disc
    obtain ⟨_,i,si,ix⟩ := mem_filter.mp (mem_subtype.mp xP)
    let f := (Embedding.induce (G:=G) (A:Set V)).toHom
    let r := w.map f
    refine ⟨i,si,_,_,r,hw.isPath.map Subtype.val_injective,ix,?_,?_⟩
    · intro v seen
      rw [show r.support=w.support.map f from Walk.support_map _ _] at seen
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp seen
      exact u.property
    · have length := hw.length_support
      change w.support.length=Fintype.card A at length
      rw [Fintype.card_coe] at length
      have mapped : r.support.length=w.support.length := by simp [r]
      omega
  have drop (v : W) (t : V) (e : G.Adj v.val t) (miss : t∉W) : t=z ∨ t∈S := by
    by_cases eq : t=z
    · exact Or.inl eq
    · exact Or.inr (outside sides (mem_erase.mp v.property).2 e (fun h => miss (mem_erase.mpr ⟨eq,h⟩)))
  have minJ (v : W) : k-3≤J.degree v := by
    have h := retained_at W (insert z S) v (fun t e h => mem_insert.mpr (drop v t e h))
    have d := minimum v.val (mem_erase.mp v.property).2 (mem_erase.mp v.property).1
    have cnt := card_insert_le z S
    change G.degree v.val≤J.degree v+(insert z S).card at h
    omega
  have strong (v : W) (miss : v∉M) : k-1≤J.degree v := by
    have h := retained_at W {z} v (fun t e dead => by
      rcases drop v t e dead with eq|ts
      · exact mem_singleton.mpr eq
      · exact (miss (mem_subtype.mpr (mem_filter.mpr ⟨v.property,t,ts,e.symm⟩))).elim)
    have d := minimum v.val (mem_erase.mp v.property).2 (mem_erase.mp v.property).1
    change G.degree v.val≤J.degree v+({z}:Finset V).card at h
    rw [card_singleton] at h
    omega
  obtain ⟨x,xM,y,w,hw,len⟩ := Graph189ConnectedMarkedRoute.route connected M active
    (d:=k-3) (u:=k-1) (loss:=3) (by omega) minJ strong
    (by change Fintype.card W≤2*(k-3)+1+3; rw [Fintype.card_coe]; omega)
    (by change Fintype.card W<2*(k-1)+M.card; rw [Fintype.card_coe]; have := active.card_pos; omega)
  obtain ⟨_,i,si,ix⟩ := mem_filter.mp (mem_subtype.mp xM)
  let f := (Embedding.induce (G:=G) (W:Set V)).toHom
  let r := w.map f
  refine ⟨i,si,_,_,r,hw.map Subtype.val_injective,ix,?_,?_⟩
  · intro v seen
    rw [show r.support=w.support.map f from Walk.support_map _ _] at seen
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp seen
    exact (mem_erase.mp u.property).2
  · change Fintype.card W≤w.support.length+(3+1) at len
    rw [Fintype.card_coe] at len
    have mapped : r.support.length=w.support.length := by simp [r]
    omega

#print axioms high
#print axioms exceptional
end Graph189BalancedSideRoutes
