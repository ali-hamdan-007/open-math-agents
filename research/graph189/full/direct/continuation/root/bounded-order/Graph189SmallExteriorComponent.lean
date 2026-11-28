import Graph189DenseClique

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem max_parts (U : Finset V) : ∃F : V→Finset V,Partition G U F ∧
    ∀K : V→Finset V,Partition G U K → score K≤score F := by
  classical
  let good := (univ : Finset (V→Finset V)).filter (Partition G U)
  let first (i : V) : Finset V := if i∈U then {i} else ∅
  have singleton : Partition G U first := by
    constructor
    · intro v
      constructor
      · intro vu; exact ⟨v,by simp [first,vu]⟩
      rintro ⟨i,hi⟩
      by_cases mem : i∈U <;> simp_all [first]
    · intro i j ne
      dsimp [first]; split_ifs <;> simp_all
    · intro i u v
      have left := u.property
      have right := v.property
      have eq : u=v := by
        apply Subtype.ext
        by_cases mem : i∈U <;> simp_all [first]
      subst v; exact Reachable.refl _
  obtain ⟨F,hF,maximal⟩ := good.exists_max_image score ⟨first,mem_filter.mpr ⟨mem_univ _,singleton⟩⟩
  exact ⟨F,(mem_filter.mp hF).2,fun K hk => maximal K (mem_filter.mpr ⟨mem_univ _,hk⟩)⟩

/-- If a longest path omits at most k−1 vertices, all its omitted high vertices
are in one component. The midpoint exchange is valid on this particular path
irrespective of which longest path was originally optimized. -/
theorem chosen_of_small_exterior {a b w : V} {p : G.Walk a b} (hp : p.IsPath)
    (mx : ∀{i j},∀q : G.Walk i j,q.IsPath → q.length≤p.length) {k : ℕ}
    (size : p.support.toFinsetᶜ.card+1≤k) (wo : w∉p.support) (wh : k≤G.degree w)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    ∃D : Finset V,Chosen p D k ∧ w∈D ∧ ∀v,v∉p.support → k≤G.degree v → v∈D := by
  classical
  let E := p.support.toFinsetᶜ
  obtain ⟨F,part,best⟩ := max_parts (G:=G) E
  have off (i v : V) (vi : v∈F i) : v∉p.support :=
    fun on => mem_compl.mp ((part.cover _).mpr ⟨i,vi⟩) (List.mem_toFinset.mpr on)
  have covered (v : V) (vo : v∉p.support) : ∃i,v∈F i := (part.cover _).mp
    (mem_compl.mpr (fun mem => vo (List.mem_toFinset.mp mem)))
  have closed (i x : V) (xi : x∈F i) (y : V) (e : G.Adj x y) (yo : y∉p.support) : y∈F i := by
    obtain ⟨j,yj⟩ := covered y yo
    exact (same_part part best xi yj e).symm ▸ yj
  have large (i v : V) (vi : v∈F i) (high : k≤G.degree v) : k≤2*(F i).card := by
    have half := (high_exterior_half p hp mx (off i v vi) (quota _) high minimum uniqueLow).2
    have sub : G.neighborFinset v \ p.support.toFinset ⊆ F i := by
      intro z hz
      exact closed i v vi z ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hz).1)
        (fun on => (mem_sdiff.mp hz).2 (List.mem_toFinset.mpr on))
    have := card_le_card sub
    omega
  obtain ⟨i,wi⟩ := covered w wo
  have unique (v : V) (vo : v∉p.support) (high : k≤G.degree v) : v∈F i := by
    obtain ⟨j,vj⟩ := covered v vo
    by_cases eq : i=j
    · exact eq.symm ▸ vj
    have sub : F i∪F j⊆E := by
      intro z hz
      exact (part.cover _).mpr ((mem_union.mp hz).elim (fun m => ⟨i,m⟩) (fun m => ⟨j,m⟩))
    have both := card_le_card sub
    rw [card_union_of_disjoint (part.separate _ _ eq)] at both
    have left := large i w wi wh
    have right := large j v vj high
    change E.card+1≤k at size
    omega
  refine ⟨F i,⟨hp,mx,part.connected i,off i,closed i,⟨w,wi,wh⟩,?_⟩,wi,unique⟩
  intro x xi _ t lt rt
  obtain ⟨valid,right⟩ := (mem_contactPositions p x _).mp rt
  have left := ((mem_contactPositions p x _).mp lt).2
  let y := p.getVert (t+1)
  change G.degree y<k
  by_contra! high
  obtain ⟨u,v,q,hq,len,swap⟩ := swap_contact_midpoint p hp (off i x xi) t valid left right
  have yon : y∈p.support.toFinset := List.mem_toFinset.mpr (p.getVert_mem_support _)
  have ne : x≠y := fun eq => off i x xi (eq ▸ List.mem_toFinset.mp yon)
  have newE : q.support.toFinsetᶜ=insert y (E.erase x) := by
    ext z
    rw [swap]
    simp only [E,mem_compl,mem_insert,mem_erase]
    change (¬(z=x ∨ z≠y ∧ z∈p.support.toFinset)) ↔ z=y ∨ z≠x ∧ z∉p.support.toFinset
    grind
  have yo : y∉q.support := fun on => mem_compl.mp (newE ▸ mem_insert_self _ _) (List.mem_toFinset.mpr on)
  obtain ⟨⟨z,zo,edge,zh⟩,_⟩ := high_exterior_half q hq
    (fun r hr => (mx r hr).trans_eq len.symm) yo (quota _) high minimum uniqueLow
  have ze : z∈q.support.toFinsetᶜ := mem_compl.mpr (fun on => zo (List.mem_toFinset.mp on))
  rw [newE] at ze
  have old := (mem_erase.mp ((mem_insert.mp ze).resolve_left edge.ne.symm)).2
  have zi := unique z (fun on => mem_compl.mp old (List.mem_toFinset.mpr on)) zh
  exact no_next_contact p hp mx part xi zi (by omega) left edge.symm

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.chosen_of_small_exterior
