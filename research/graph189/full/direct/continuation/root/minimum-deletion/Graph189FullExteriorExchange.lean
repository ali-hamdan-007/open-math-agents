import Graph189NearFinal

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189RootedSplice
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {x y : V}

omit [Fintype V] in
theorem full_exterior_splice (p : G.Walk x y) (hp : p.IsPath)
    (root : V) (rootOn : root∈p.support) (E : Finset V) (m : ℕ) (size : E.card=m)
    (outside : ∀ v∈E, v∉p.support) (a b : E) (ne : a≠b)
    (routes : ∀ i j : E, i≠j → ∃ h : (G.induce (E : Set V)).Walk i j, h.IsHamiltonian)
    (uniform : ∀ v∈p.support, G.Adj v a.val → G.Adj v b.val)
    (A J B : List V) (split : p.support=A++J++B) (retains : root∉J)
    (before : ∀ w∈A.getLast?, G.Adj w a.val) (after : ∀ w∈B.head?, G.Adj a.val w) :
    ∃ u v, ∃ r : G.Walk u v, r.IsPath ∧ root∈r.support ∧
      r.support.length+J.length=p.support.length+m ∧
      (∀ i∈J, i∉r.support) ∧ ∀ i∈A++B, i∈r.support := by
  classical
  obtain ⟨h,hHam⟩ := routes a b ne
  let emb := Embedding.induce (G:=G) (E : Set V)
  let hG := h.map emb.toHom
  have isPath : hG.IsPath := hHam.isPath.map emb.injective
  have len : hG.support.length=m := by
    change (h.map emb.toHom).support.length=m
    rw [Walk.support_map,List.length_map,hHam.length_support]
    simpa using size
  have dis : List.Disjoint hG.support p.support := by
    apply List.disjoint_left.mpr
    intro v hit on
    change v∈(h.map emb.toHom).support at hit
    rw [Walk.support_map] at hit
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hit
    exact outside i.val i.property on
  have endEdge (v : V) (member : v∈B.head?) : G.Adj b.val v := by
    have on : v∈p.support := by
      rw [split]
      apply List.mem_append_right
      cases eqn : B with
      | nil => simp [eqn] at member
      | cons v₀ vs =>
        simp [eqn] at member
        simp [member]
    exact (uniform v on (after v member).symm).symm
  obtain ⟨u,v,r,hr,order⟩ := splice_path p hp A J B split
    hG isPath dis before endEdge
  have preserve : root∈r.support := by
    rw [order]
    rw [split] at rootOn
    simp only [List.mem_append] at rootOn ⊢
    tauto
  have sizes : r.support.length+J.length=p.support.length+m := by
    rw [order,split]
    simp only [List.length_append]
    omega
  have old := hp.support_nodup
  rw [split] at old
  have blockOn (i : V) (hi : i∈J) : i∈p.support := by simp [split,hi]
  have omitted (i : V) (hi : i∈J) : i∉r.support := by
    rw [order]
    simp only [List.mem_append]
    rintro ((left|middle)|right)
    · exact List.disjoint_left.mp old.of_append_left.disjoint left hi
    · exact List.disjoint_left.mp dis middle (blockOn _ hi)
    · exact List.disjoint_left.mp old.disjoint (List.mem_append_right _ hi) right
  refine ⟨u,v,r,hr,preserve,sizes,omitted,?_⟩
  intro i hi
  rw [order]
  simp only [List.mem_append] at hi ⊢
  tauto

omit [Fintype V] in
/-- Transfer contact incidence on the current path and on all equal-order
paths retaining the protected vertex after a full exterior substitution. -/
theorem full_gap_dist_two (p : G.Walk x y) (hp : p.IsPath)
    (root : V) (rootOn : root∈p.support) (E : Finset V) (m : ℕ) (size : E.card=m)
    (outside : ∀ v∈E, v∉p.support) (a b : E) (ne : a≠b)
    (routes : ∀ i j : E, i≠j → ∃ h : (G.induce (E : Set V)).Walk i j, h.IsHamiltonian)
    (uniform : ∀ v∈p.support, G.Adj v a.val → G.Adj v b.val)
    (alternative : ∀ {u v}, ∀ t : G.Walk u v, t.IsPath → root∈t.support → t.length=p.length →
      ∀ i, i∉t.support → ∀ j, j∉t.support → ∀ w∈t.support, G.Adj w i → G.Adj w j)
    (gap : TightGap p a.val m) (retains : root∉gap.block) :
    ∀ w∈gap.block, G.dist a.val w=2 := by
  obtain ⟨u,v,r,hr,preserve,sizes,omitted,stays⟩ := full_exterior_splice p hp root rootOn
    E m size outside a b ne routes uniform gap.left gap.block gap.right gap.split retains gap.before gap.after
  have same : r.length=p.length := by
    have lp := p.length_support
    have lr := r.length_support
    have original := gap.size
    omega
  obtain ⟨c,hc,ac,i,hi,ci⟩ := gap.boundary
  intro w hw
  have on : w∈p.support := by simp [gap.split,hw]
  have diff : a.val≠w := fun e => outside a.val a.property (by simpa [e] using on)
  have cw := alternative r hr preserve same i (omitted _ hi) w (omitted _ hw) c (stays _ hc) ci
  exact two_step_metric diff (gap.unmarked w hw) ac cw.symm

/-- The two disjoint full gaps certified by the protected mark count force
twice the exterior order into an actual vertex's even-distance allowance. -/
theorem even_budget_of_full_gaps (p : G.Walk x y) (hp : p.IsPath) (a : V) (m k : ℕ)
    (left right : TightGap p a m) (separate : List.Disjoint left.block right.block)
    (leftHits : ∀ w∈left.block, G.dist a w=2) (rightHits : ∀ w∈right.block, G.dist a w=2)
    (cap : G.distEven a≤k+1) : 2*m≤k := by
  classical
  let S := left.block.toFinset∪right.block.toFinset
  have dis : Disjoint left.block.toFinset right.block.toFinset := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => List.disjoint_left.mp separate (List.mem_toFinset.mp h₁) (List.mem_toFinset.mp h₂))
  have nodup (g : TightGap p a m) : g.block.Nodup := by
    have nd := hp.support_nodup
    rw [g.split] at nd
    exact nd.of_append_left.of_append_right
  have cnt : S.card=2*m := by
    simp only [S,card_union_of_disjoint dis,List.toFinset_card_of_nodup (nodup left),
      List.toFinset_card_of_nodup (nodup right),left.size,right.size]
    omega
  have two (w : V) (hw : w∈S) : G.dist a w=2 := by
    rcases mem_union.mp hw with h|h
    · exact leftHits w (List.mem_toFinset.mp h)
    · exact rightHits w (List.mem_toFinset.mp h)
  have absent : a∉S := by intro h; have := two a h; simp at this
  have cover : insert a S⊆univ.filter (fun w => Even (G.dist a w)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [two w h]; decide⟩
  have c := card_le_card cover
  rw [card_insert_of_notMem absent,cnt] at c
  change 2*m+1≤G.distEven a at c
  omega

#print axioms full_exterior_splice
#print axioms full_gap_dist_two
#print axioms even_budget_of_full_gaps
end Graph189RootedSplice
