import Graph189DenseSideRoute

open SimpleGraph Finset
namespace Graph189MarkedLowCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem side_contact {A B : Finset V} {z : V}
    (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B {z}) :
    ∃ v∈A, G.Adj v z := by
  obtain ⟨x,hx⟩ := sides.left_nonempty
  obtain ⟨p⟩ := hc x z
  have outside : z∉A := fun h => Finset.disjoint_left.mp sides.left_cut h (mem_singleton_self _)
  obtain ⟨a,b,aa,ba,e,_⟩ := Graph189CutSides.walk_exits (·∈A) p hx outside
  rcases sides.cover b with h|h|h
  · exact (ba h).elim
  · exact (sides.no_cross a aa b h e).elim
  · exact ⟨a,aa,(mem_singleton.mp h) ▸ e⟩

/-- If deleting one vertex disconnects a dense graph and there are three
marked surviving vertices, there is a Hamiltonian path starting at a mark. -/
theorem of_cut (hc : G.Connected) (z : V) (P : Finset V) {d : ℕ} (two : 2≤d)
    (min : ∀ v, v≠z → d+1≤G.degree v) (order : Fintype.card V≤3*d)
    (marks : 3≤(P.erase z).card) (disc : ¬(G.induce {v : V | v∉({z}:Finset V)}).Connected) :
    ∃ x∈P, ∃ y, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  obtain ⟨w,ne⟩ := exists_ne z
  obtain ⟨A,B,l⟩ := Graph189CutSides.exists_cutSides_of_disconnected ({z}:Finset V) ⟨w,by simpa using ne⟩ disc
  have high {R T : Finset V} (sides : Graph189CutSides.CutSides G R T {z}) (a : R) :
      d≤(G.induce (R:Set V)).degree a := by
    have sum := Graph189DenseSideRoute.retained R {z} (fun v vr u e ur => by
      rcases sides.cover u with h|h|h
      · exact (ur h).elim
      · exact (sides.no_cross v vr u h e).elim
      · exact h) a
    have ne : a.val≠z := fun eq => Finset.disjoint_left.mp sides.left_cut a.property (mem_singleton.mpr eq)
    have h := min a.val ne
    rw [card_singleton] at sum
    omega
  have wide {R T : Finset V} (sides : Graph189CutSides.CutSides G R T {z}) : d+1≤R.card := by
    obtain ⟨u,ur⟩ := sides.left_nonempty
    let a : R := ⟨u,ur⟩
    have low := high sides a
    have up := (G.induce (R:Set V)).degree_lt_card_verts a
    change _<Fintype.card R at up
    rw [Fintype.card_coe] at up
    omega
  have complete {R T : Finset V} (sides : Graph189CutSides.CutSides G R T {z}) (a b : R) (ne : a≠b) :
      ∃ p : (G.induce (R:Set V)).Walk a b, p.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph le_top _
      (Graph189TerminalLeafClosure.complete_prescribed a b ne)
    intro i j _ _
    have ha := high sides i
    have hb := high sides j
    have lower := wide sides.swap
    have n := card_le_card (subset_univ (R∪T))
    rw [card_univ,card_union_of_disjoint sides.apart] at n
    change Fintype.card R+1≤_
    rw [Fintype.card_coe]
    omega
  have route {R T : Finset V} (sides : Graph189CutSides.CutSides G R T {z}) (many : 2≤(R∩P).card) :
      ∃ x∈P, ∃ y, ∃ p : G.Walk x y, p.IsHamiltonian := by
    obtain ⟨a,aR,az⟩ := side_contact hc sides
    obtain ⟨b,bT,bz⟩ := side_contact hc sides.swap
    obtain ⟨u,up,v,vp,ne⟩ := one_lt_card.mp (show 1<(R∩P).card by omega)
    obtain ⟨start,sR,sP,sa⟩ : ∃ start∈R, start∈P ∧ start≠a := by
      by_cases same : u=a
      · exact ⟨v,(mem_inter.mp vp).1,(mem_inter.mp vp).2,by rintro rfl; exact ne same⟩
      · exact ⟨u,(mem_inter.mp up).1,(mem_inter.mp up).2,same⟩
    have bsz:=wide sides.swap
    letI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
    let b' : T := ⟨b,bT⟩
    obtain ⟨end_,ne⟩ := exists_ne b'
    obtain ⟨p,hp⟩ := complete sides ⟨start,sR⟩ ⟨a,aR⟩ (fun eq => sa (congrArg Subtype.val eq))
    obtain ⟨r,hr⟩ := complete sides.swap b' end_ ne.symm
    let f := (Embedding.induce (G:=G) (R:Set V)).toHom
    let g := (Embedding.induce (G:=G) (T:Set V)).toHom
    let p' := p.map f
    let r' := r.map g
    have onL {v : V} (h : v∈p'.support) : v∈R := by
      rw [show p'.support=p.support.map f from Walk.support_map _ _] at h
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp h
      exact t.property
    have onR {v : V} (h : v∈r'.support) : v∈T := by
      rw [show r'.support=r.support.map g from Walk.support_map _ _] at h
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp h
      exact t.property
    have spansR {v : V} (vT : v∈T) : v∈r'.support := by
      rw [show r'.support=r.support.map g from Walk.support_map _ _]
      exact List.mem_map.mpr ⟨⟨v,vT⟩,hr.mem_support _,rfl⟩
    have spansL {v : V} (vR : v∈R) : v∈p'.support := by
      rw [show p'.support=p.support.map f from Walk.support_map _ _]
      exact List.mem_map.mpr ⟨⟨v,vR⟩,hp.mem_support _,rfl⟩
    have notZ : z∉r'.support := fun h => Finset.disjoint_left.mp sides.right_cut (onR h) (mem_singleton_self _)
    let tail : G.Walk z (g end_) := r'.cons bz.symm
    have ht : tail.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hr.isPath.map Subtype.val_injective,notZ⟩
    obtain ⟨q,hq,qs⟩ := Graph189TwoCutSingleton.joined p' (hp.isPath.map Subtype.val_injective) tail ht az (by
      apply List.disjoint_left.mpr
      intro v vl vt
      rcases List.mem_cons.mp (show v∈z::r'.support from vt) with rfl|vr
      · exact Finset.disjoint_left.mp sides.left_cut (onL vl) (mem_singleton_self _)
      · exact Finset.disjoint_left.mp sides.apart (onL vl) (onR vr))
    refine ⟨start,sP,_,q,hq.isHamiltonian_of_mem fun v => ?_⟩
    rw [qs]
    change v∈p'.support++(z::r'.support)
    rcases sides.cover v with vR|vT|vz
    · exact List.mem_append_left _ (spansL vR)
    · exact List.mem_append_right _ (List.mem_cons_of_mem z (spansR vT))
    · apply List.mem_append_right
      exact List.mem_cons.mpr (Or.inl (mem_singleton.mp vz))
  have cover : P.erase z⊆(A∩P)∪(B∩P) := by
    intro v hv
    rcases l.cover v with ha|hb|hz
    · exact mem_union_left _ (mem_inter.mpr ⟨ha,(mem_erase.mp hv).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hb,(mem_erase.mp hv).2⟩)
    · exact False.elim ((mem_erase.mp hv).1 (mem_singleton.mp hz))
  have count := (card_le_card cover).trans (card_union_le _ _)
  by_cases large : 2≤(A∩P).card
  · exact route l large
  · exact route l.swap (by omega)

#print axioms of_cut
end Graph189MarkedLowCut
