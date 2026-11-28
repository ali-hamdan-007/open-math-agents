import Graph189OrdinaryRotationWindow

open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189SevenRotation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Any high omission in an ordinary longest path is impossible in a
two-connected qualifying graph of order at most twenty-three and k=7. -/
theorem no_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) (order : Fintype.card V≤23)
    (original : G.secondSmallestDegree=7) (minimum : ∀ v, 3≤G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤7)
    {highVertex : V} (omitted : highVertex∉p.support) (large : 7≤G.degree highVertex) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique (a b : V) (aLow : G.degree a<7) (bLow : G.degree b<7) : a=b := by
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
    omega
  obtain ⟨degree,B,R,rank,sub,width,neighbor⟩ := Graph189OrdinaryRotationWindow.of_high p hp mx conn
    (d:=4) (L:=5) original (by decide) (by decide) (by decide) (by omega) minimum quota omitted large
  let D := R.filter (fun v => 7≤G.degree v.val)
  have few : (R \ D).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    apply Subtype.ext
    apply unique
    · by_contra! high
      exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,high⟩)
    · by_contra! high
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,high⟩)
  have split := card_sdiff_add_card_eq_card (show D⊆R from filter_subset _ _)
  have many : 3≤D.card := by omega
  have full (a : E) (ha : a∈D) : J.neighborFinset a=B.erase a ∧ B.card=5 := by
    have ar := (mem_filter.mp ha).1
    have degreeA : 4≤J.degree a := degree a (mem_filter.mp ha).2
    have inc : J.neighborFinset a⊆B.erase a := by
      intro v hv
      exact mem_erase.mpr ⟨((J.mem_neighborFinset _ _).mp hv).ne.symm,neighbor a ar hv⟩
    have size := card_le_card inc
    rw [J.card_neighborFinset_eq_degree,card_erase_of_mem (sub ar)] at size
    exact ⟨eq_of_subset_of_card_le inc (by
      rw [J.card_neighborFinset_eq_degree,card_erase_of_mem (sub ar)]
      omega),by omega⟩
  obtain ⟨d,hd⟩ := card_pos.mp (show 0<D.card by omega)
  let f : E ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have ord := Graph189OrdinaryRotationWindow.full_ports p hp mx (B.map f) (D.map f)
    (by rw [card_map,(full d hd).2]; decide) (by rw [card_map,(full d hd).2])
    (by rwa [card_map]) (map_subset_map.mpr ((filter_subset _ _).trans sub))
    (fun v hv => by obtain ⟨v,_,rfl⟩ := mem_map.mp hv; exact off v)
    (by
      intro a ha b hb diff
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hb
      apply (J.mem_neighborFinset u v).mp
      rw [(full u hu).1]
      exact mem_erase.mpr ⟨fun eq => diff (congrArg f eq.symm),hv⟩)
    (by
      intro a ha v step no
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      by_contra offV
      let w : E := ⟨v,mem_compl.mpr fun mem => offV (List.mem_toFinset.mp mem)⟩
      have e : J.Adj u w := step
      exact no (mem_map.mpr ⟨w,neighbor u (mem_filter.mp hu).1 ((J.mem_neighborFinset _ _).mpr e),rfl⟩))
    (by
      intro a ha
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      rw [card_map,(full d hd).2]
      exact (mem_filter.mp hu).2)
  rw [card_map,(full d hd).2] at ord
  omega

end Graph189SevenRotation
#print axioms Graph189SevenRotation.no_high
