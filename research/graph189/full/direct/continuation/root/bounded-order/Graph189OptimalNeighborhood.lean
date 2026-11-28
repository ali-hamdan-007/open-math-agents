import Graph189ChosenExterior

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degree_split {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    {x : V} (xc : x∈C) : (contactPositions p x).card+(G.neighborFinset x∩C).card=G.degree x := by
  classical
  have eq : G.neighborFinset x \ p.support.toFinset=G.neighborFinset x∩C := by
    ext v
    constructor
    · intro hv
      obtain ⟨adj,off⟩ := mem_sdiff.mp hv
      exact mem_inter.mpr ⟨adj,h.closed _ xc _ ((G.mem_neighborFinset _ _).mp adj)
        (fun on => off (List.mem_toFinset.mpr on))⟩
    intro hv
    obtain ⟨adj,vc⟩ := mem_inter.mp hv
    exact mem_sdiff.mpr ⟨adj,fun on => h.outside _ vc (List.mem_toFinset.mp on)⟩
  rw [contact_card_neighbors p h.path,←eq]
  exact card_inter_add_card_sdiff _ _

/-- The local constraints at a real noncut high vertex in the selected component.
Here q is its internal degree, R its internal distance-two shell measured in G,
and X the closed internal neighborhood. -/
theorem local_bounds {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    {x : V} (xc : x∈C) (high : k≤G.degree x)
    (noncut : (G.induce (C.erase x:Set V)).Preconnected)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (quota : (univ.filter (fun v => G.dist x v=2)).card≤k) :
    let N := G.neighborFinset x∩C
    let X := insert x N
    let R := C.filter (fun v => G.dist x v=2)
    let ε := (p.support.toFinset.filter (fun y => G.degree y<k)).card
    R.card+k≤2*N.card+ε ∧
    ∀y∈X,k≤G.degree y →
      k≤(G.neighborFinset y∩X).card+N.card ∧
      k≤(contactPositions p y).card+N.card+R.card := by
  classical
  let N := G.neighborFinset x∩C
  let X := insert x N
  let R := C.filter (fun v => G.dist x v=2)
  let Q := p.support.toFinset.filter (fun v => G.dist x v=2)
  let ε := (p.support.toFinset.filter (fun y => G.degree y<k)).card
  have split := degree_split h xc
  change (contactPositions p x).card+N.card=G.degree x at split
  have shell := shell_count p h.path h.longest (h.outside _ xc) C h.outside quota (h.midpoint x xc noncut)
  change R.card+2*(contactPositions p x).card≤k+ε at shell
  have nox : x∉N := fun m => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_inter.mp m).1)
  have size : X.card=N.card+1 := card_insert_of_notMem nox
  have dis : Disjoint R Q := Finset.disjoint_left.mpr (fun _ r q =>
    h.outside _ (mem_filter.mp r).1 (List.mem_toFinset.mp (mem_filter.mp q).1))
  have within : R∪Q⊆univ.filter (fun v => G.dist x v=2) := by
    intro v m
    rcases mem_union.mp m with r|q
    · exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp r).2⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp q).2⟩
  have total := (card_le_card within).trans quota
  rw [card_union_of_disjoint dis] at total
  refine ⟨by change R.card+k≤2*N.card+ε; omega,?_⟩
  intro y yX yh
  change y∈X at yX
  have yc : y∈C := (mem_insert.mp yX).elim (fun eq => eq ▸ xc) (fun n => (mem_inter.mp n).2)
  have degree := degree_split h yc
  let T := G.neighborFinset y∩X
  have Tsub : T⊆X.erase y := by
    intro v hv
    obtain ⟨adj,vX⟩ := mem_inter.mp hv
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp adj).ne.symm,vX⟩
  have tmax := card_le_card Tsub
  have er := card_erase_add_one yX
  have capacity : T.card≤N.card := by omega
  by_cases yx : y=x
  · subst y
    have same : T=N := by ext v; simp [T,X,N]
    change k≤T.card+N.card ∧ k≤(contactPositions p x).card+N.card+R.card
    have outside := (high_exterior_half p h.path h.longest (h.outside _ xc) quota high minimum uniqueLow).2
    have partition := card_sdiff_add_card_inter (G.neighborFinset x) p.support.toFinset
    rw [←contact_card_neighbors p h.path x] at partition
    change _+(contactPositions p x).card=G.degree x at partition
    rw [same]
    omega
  have yn : y∈N := (mem_insert.mp yX).resolve_left yx
  have xy := (G.mem_neighborFinset _ _).mp (mem_inter.mp yn).1
  have cols := cross_positions_le_path_shell p h.path h.longest (h.outside _ xc) (h.outside _ yc) xy
  change (contactPositions p x).card+(contactPositions p y).card≤Q.card at cols
  have cover : G.neighborFinset y∩C⊆T∪R := by
    intro z hz
    obtain ⟨adj,zc⟩ := mem_inter.mp hz
    by_cases zX : z∈X
    · exact mem_union_left _ (mem_inter.mpr ⟨adj,zX⟩)
    have neq : x≠z := by intro e; exact zX (e ▸ mem_insert_self _ _)
    have miss : ¬G.Adj x z := fun e => zX (mem_insert_of_mem (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr e,zc⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨zc,two_step_metric neq miss xy ((G.mem_neighborFinset _ _).mp adj).symm⟩)
  have count := (card_le_card cover).trans (card_union_le _ _)
  change k≤T.card+N.card ∧ k≤(contactPositions p y).card+N.card+R.card
  omega

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.local_bounds
