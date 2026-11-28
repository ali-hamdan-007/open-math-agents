import Graph189LongPathClosure
import Graph189RotationExterior
import Graph189NativeCycleLinked

open SimpleGraph Finset
namespace Graph189RotationLinked
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private def fill (G : SimpleGraph V) (P : V → Prop) : SimpleGraph V where
  Adj x y := G.Adj x y ∨ P x ∧ P y ∧ x≠y
  symm := ⟨fun _ _ h => h.elim (fun e => Or.inl e.symm) (fun ⟨px,py,ne⟩ => Or.inr ⟨py,px,ne.symm⟩)⟩
  loopless := ⟨fun _ h => h.elim (fun e => G.irrefl e) (fun h => h.2.2 rfl)⟩

/-- A clique can be covered by a prescribed endpoint path if every external
endpoint has two available contacts. -/
private theorem route_clique (R : Finset V)
    (clique : ∀ u∈R, ∀ v∈R, u≠v → G.Adj u v)
    (ports : ∀ v, v∉R → 2 ≤ (G.neighborFinset v ∩ R).card)
    (x y : V) (different : x≠y) :
    ∃ q : G.Walk x y, q.IsPath ∧ R.card ≤ q.support.length := by
  classical
  have get {w : V} (out : w∉R) (avoid : V) : ∃ v∈R, G.Adj w v ∧ v≠avoid := by
    obtain ⟨v,hv,ne⟩ := exists_mem_ne (ports w out) avoid
    exact ⟨v,(mem_inter.mp hv).2,(G.mem_neighborFinset _ _).mp (mem_inter.mp hv).1,ne⟩
  have ends : ∃ u∈R, ∃ v∈R, u≠v ∧ (x=u ∨ x∉R ∧ G.Adj x u) ∧ (y=v ∨ y∉R ∧ G.Adj y v) := by
    by_cases hx : x∈R
    · by_cases hy : y∈R
      · exact ⟨x,hx,y,hy,different,Or.inl rfl,Or.inl rfl⟩
      obtain ⟨v,hv,edge,ne⟩ := get hy x
      exact ⟨x,hx,v,hv,ne.symm,Or.inl rfl,Or.inr ⟨hy,edge⟩⟩
    obtain ⟨u,hu,ux,uy⟩ := get hx y
    by_cases hy : y∈R
    · exact ⟨u,hu,y,hy,uy,Or.inr ⟨hx,ux⟩,Or.inl rfl⟩
    obtain ⟨v,hv,vy,ne⟩ := get hy u
    exact ⟨u,hu,v,hv,ne.symm,Or.inr ⟨hx,ux⟩,Or.inr ⟨hy,vy⟩⟩
  obtain ⟨u,hu,v,hv,ne,xu,yv⟩ := ends
  let i : R := ⟨u,hu⟩
  let j : R := ⟨v,hv⟩
  let f : (⊤ : SimpleGraph R) →g G := {
    toFun := Subtype.val
    map_rel' := fun {a b} h => clique _ a.property _ b.property (fun eq => (top_adj _ _).mp h (Subtype.ext eq)) }
  obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.complete_prescribed i j (fun eq => ne (congrArg Subtype.val eq))
  let r : G.Walk u v := q.map f
  have hpath : r.IsPath := hq.isPath.map Subtype.val_injective
  have contained (t : V) (ht : t∈r.support) : t∈R := by
    have h : t∈q.support.map f := (Walk.support_map f q) ▸ ht
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
    exact w.property
  have size : r.support.length=R.card := by
    have mapped := congrArg List.length (Walk.support_map f q)
    rw [List.length_map,hq.length_support,Fintype.card_coe] at mapped
    exact mapped
  rcases xu with rfl|⟨xo,link⟩ <;> rcases yv with rfl|⟨yo,back⟩
  · exact ⟨r,hpath,size.ge⟩
  · refine ⟨r.concat back.symm,hpath.concat (fun h => yo (contained _ h)) back.symm,?_⟩
    simp [size]
  · refine ⟨r.cons link,hpath.cons (fun h => xo (contained _ h)),?_⟩
    simp [size]
  · let t := r.cons link
    have tp : t.IsPath := hpath.cons (fun h => xo (contained _ h))
    have fresh : y∉t.support := fun h => yo (contained _ ((List.mem_cons.mp h).resolve_left different.symm))
    refine ⟨t.concat back.symm,tp.concat fresh back.symm,?_⟩
    simp [t,size]
    omega

/-- The degree-sum cost of removing a vertex is at most one for each pair
of distinct retained endpoints if the removed vertex contacts at most one. -/
private theorem pair_degree (B R S : Finset V) (sb : S⊆B)
    (near : ∀ r∈R, G.neighborFinset r⊆B)
    (removed : ∀ v∈B, v∉S → (G.neighborFinset v ∩ R).card ≤ 1)
    {x y : S} (xr : x.val∈R) (yr : y.val∈R) (ne : x≠y)
    (sum : B.card+1 ≤ G.degree x.val + G.degree y.val) :
    Fintype.card S+1 ≤ (G.induce (S : Set V)).degree x+(G.induce (S : Set V)).degree y := by
  classical
  let A := G.neighborFinset x.val
  let C := G.neighborFinset y.val
  have dis : Disjoint (A \ S) (C \ S) := by
    rw [Finset.disjoint_left]
    intro t hx hy
    have tx := ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hx).1).symm
    have ty := ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1).symm
    have bound := removed t (near _ xr (mem_sdiff.mp hx).1) (mem_sdiff.mp hx).2
    have many := one_lt_card.mpr (show ∃ a∈G.neighborFinset t∩R, ∃ b∈G.neighborFinset t∩R, a≠b from
      ⟨x.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr tx,xr⟩,
       y.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ty,yr⟩,fun h => ne (Subtype.ext h)⟩)
    omega
  have loss := card_le_card (show (A\S) ∪ (C\S) ⊆ B\S from by
    intro t ht
    rcases mem_union.mp ht with h|h
    · exact mem_sdiff.mpr ⟨near _ xr (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩
    · exact mem_sdiff.mpr ⟨near _ yr (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)
  rw [card_union_of_disjoint dis] at loss
  have ax := card_sdiff_add_card_inter A S
  have cy := card_sdiff_add_card_inter C S
  have rem := card_sdiff_add_card_eq_card sb
  change B.card+1 ≤ A.card+C.card at sum
  rw [Fintype.card_coe,Graph189ExteriorDegreeCycle.degree_induce_filter,Graph189ExteriorDegreeCycle.degree_induce_filter]
  have filter (T : Finset V) : T.filter (fun v => v∈(S : Set V))=T∩S := by ext v; simp
  rw [filter,filter]
  change S.card+1 ≤ (A∩S).card+(C∩S).card
  omega

/-- Every shortest-cycle-exclusion window with enough protected initial
endpoints contains a linked set with one more vertex than the degree bound. -/
theorem linked_of_window (B R : Finset V) {d : ℕ} (rows : d≤R.card) (rb : R⊆B)
    (small : B.card+1≤2*d) (minimum : ∀ w∈R, d≤G.degree w)
    (near : ∀ w∈R, G.neighborFinset w⊆B) : Graph189LinkedExterior.Linked G d := by
  classical
  let S := R ∪ B.filter (fun w => 2≤(G.neighborFinset w∩R).card)
  have rs : R⊆S := subset_union_left
  have sb : S⊆B := union_subset rb (filter_subset _ _)
  have removed (t : V) (tb : t∈B) (out : t∉S) : (G.neighborFinset t∩R).card≤1 := by
    by_contra! big
    exact out (mem_union_right _ (mem_filter.mpr ⟨tb,big⟩))
  have size : d+1≤S.card := by
    by_contra! few
    have er := card_le_card rs
    have same : S=R := (eq_of_subset_of_card_le rs (by omega)).symm
    have choose (r : R) : ∃ w : ↥(B\R), G.Adj r.val w.val := by
      by_contra! all
      have inc : G.neighborFinset r.val ⊆ R.erase r.val := by
        intro t ht
        have e := (G.mem_neighborFinset _ _).mp ht
        apply mem_erase.mpr
        refine ⟨e.ne.symm,?_⟩
        by_contra missing
        exact all ⟨t,mem_sdiff.mpr ⟨near _ r.property ht,missing⟩⟩ e
      have count := card_le_card inc
      rw [G.card_neighborFinset_eq_degree,card_erase_of_mem r.property] at count
      have lo := minimum r.val r.property
      have pos := card_pos.mpr (show R.Nonempty from ⟨r.val,r.property⟩)
      omega
    choose f edge using choose
    have injective : Function.Injective f := by
      intro x y eq
      by_contra ne
      let t := (f x).val
      have xadj : G.Adj t x.val := (edge x).symm
      have yadj : G.Adj t y.val := by
        change G.Adj (f x).val y.val
        rw [eq]
        exact (edge y).symm
      have enough : 1 < (G.neighborFinset t∩R).card := one_lt_card.mpr
        ⟨x.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr xadj,x.property⟩,
         y.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr yadj,y.property⟩,fun h => ne (Subtype.ext h)⟩
      have bound := removed t (mem_sdiff.mp (f x).property).1 (by rw [same]; exact (mem_sdiff.mp (f x).property).2)
      omega
    have bound := card_le_card_of_injective injective
    have sizeB := card_sdiff_add_card_eq_card rb
    omega
  let H := G.induce (S : Set V)
  let P (w : S) := w.val∈R
  let J := fill H P
  let emb : R ↪ S := ⟨fun w => ⟨w.val,rs w.property⟩,fun _ _ e => Subtype.ext (congrArg (fun t : S => t.val) e)⟩
  let Z := (univ : Finset R).map emb
  have zm (w : S) : w∈Z ↔ w.val∈R := by
    constructor
    · intro h
      obtain ⟨r,_,rfl⟩ := mem_map.mp h
      exact r.property
    · intro h
      exact mem_map.mpr ⟨⟨w.val,h⟩,mem_univ _,Subtype.ext rfl⟩
  have zsize : Z.card=R.card := by simp [Z]
  have complete (u : S) (hu : u∈Z) (v : S) (hv : v∈Z) (ne : u≠v) : J.Adj u v :=
    Or.inr ⟨(zm _).mp hu,(zm _).mp hv,ne⟩
  have ports (w : S) (no : w∉Z) : 2≤(J.neighborFinset w∩Z).card := by
    have out : w.val∉R := fun h => no ((zm _).mpr h)
    have orig := (mem_filter.mp ((mem_union.mp w.property).resolve_left out)).2
    obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp orig
    let i : S := ⟨u,rs (mem_inter.mp hu).2⟩
    let j : S := ⟨v,rs (mem_inter.mp hv).2⟩
    have wi : J.Adj w i := Or.inl ((G.mem_neighborFinset _ _).mp (mem_inter.mp hu).1)
    have wj : J.Adj w j := Or.inl ((G.mem_neighborFinset _ _).mp (mem_inter.mp hv).1)
    exact one_lt_card.mpr ⟨i,mem_inter.mpr ⟨(J.mem_neighborFinset _ _).mpr wi,(zm _).mpr (mem_inter.mp hu).2⟩,
      j,mem_inter.mpr ⟨(J.mem_neighborFinset _ _).mpr wj,(zm _).mpr (mem_inter.mp hv).2⟩,fun h => ne (congrArg Subtype.val h)⟩
  have degree (x y : S) (xy : J.Adj x y) (nonedge : ¬H.Adj x y) : Fintype.card S+1 ≤ H.degree x+H.degree y := by
    obtain ⟨xr,yr,ne⟩ := xy.resolve_left nonedge
    have dx := minimum _ xr
    have dy := minimum _ yr
    exact pair_degree B R S sb near removed xr yr ne (by omega)
  have linked : Graph189LinkedExterior.Linked H d := by
    refine ⟨univ,by simpa using size,?_⟩
    intro x _ y _ ne
    obtain ⟨q,hq,sz⟩ := route_clique Z complete ports x y ne
    obtain ⟨r,hr,count⟩ := Graph189LongPathClosure.long_of_supergraph (G:=H) (K:=J)
      (fun _ _ h => Or.inl h) degree q hq
    rw [zsize] at sz
    exact ⟨r,hr,rows.trans (sz.trans count),fun w _ => mem_univ w⟩
  exact Graph189LinkedExterior.map (Embedding.induce (G:=G) (S : Set V)).toHom Subtype.val_injective linked

/-- Every finite graph of minimum degree at least l contains l+1 vertices in
one internally linked set with prescribed paths using at least l vertices. -/
theorem of_minimum (z : V) {l : ℕ} (three : 3≤l) (minimum : ∀ v, l≤G.degree v) :
    Graph189LinkedExterior.Linked G l := by
  let L := 2*l-3
  by_cases long : ∃ x, ∃ q : G.Walk x x, q.IsCycle ∧ L+1≤q.length
  · obtain ⟨_,q,hq,sz⟩ := long
    apply Graph189NativeCycleLinked.of_cycle q hq <;> dsimp [L] at sz <;> omega
  have short (x : V) (q : G.Walk x x) (hq : q.IsCycle) : q.length≤L := by
    by_contra! big
    exact long ⟨x,q,hq,big⟩
  obtain ⟨B,E,sz,sub,len,near⟩ := Graph189RotationExterior.degree_window z (by dsimp [L]; omega) minimum short
  exact linked_of_window B E sz sub (by dsimp [L] at len; omega) (fun w _ => minimum w) near

end Graph189RotationLinked
#print axioms Graph189RotationLinked.of_minimum
