import Graph189LeafRemainder

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem short_routes {C D : Finset V} {w : V} (L : Limb G C D w)
    (dense : ∀x∈D,D.card+3≤2*(G.neighborFinset x∩C).card) :
    ∀x y : D,x≠y → ∃q : (G.induce (D:Set V)).Walk x y,q.IsHamiltonian := by
  classical
  let H := G.induce (D:Set V)
  have localDegree (v : D) : D.card+1≤2*H.degree v := by
    have cover : G.neighborFinset v.val∩C⊆insert w (G.neighborFinset v.val∩D) := by
      intro z hz
      obtain ⟨adj,zc⟩ := mem_inter.mp hz
      exact mem_insert.mpr ((L.exits _ v.property _ zc ((G.mem_neighborFinset _ _).mp adj)).elim
        (fun zd => Or.inr (mem_inter.mpr ⟨adj,zd⟩)) Or.inl)
    have count := (card_le_card cover).trans (card_insert_le _ _)
    have eq : H.degree v=(G.neighborFinset v.val∩D).card := by
      rw [show H.degree v=_ from Graph189ExteriorDegreeCycle.degree_induce_filter (D:Set V) v]
      congr 1
    have deg := dense _ v.property
    omega
  intro x y ne
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
    (Graph189TerminalLeafClosure.complete_prescribed x y ne)
  intro i j _ _
  change Fintype.card D+1≤H.degree i+H.degree j
  rw [Fintype.card_coe]
  have := localDegree i
  have := localDegree j
  omega

/-- From any leaf port the tail spans its interior, crosses the articulation,
and follows an actual path on a further ceil(k/2) vertices of the remainder. -/
theorem extended_tails {a b : V} {p : G.Walk a b} {C D : Finset V} {w : V} {k : ℕ}
    (h : Chosen p C k) (L : Limb G C D w)
    (noncut : ∀x∈D,(G.induce ((insert w D).erase x:Set V)).Preconnected)
    (wide : 1<D.card) (routes : ∀u v : D,u≠v → ∃q : (G.induce (D:Set V)).Walk u v,q.IsHamiltonian)
    (four : 4≤k) (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    ∀x∈D,∃y,ExteriorRoute p y x (D.card+(1+(k+1)/2)) := by
  classical
  let R := C \ insert w D
  obtain ⟨_,r,rr,wr,z,Q,hQ,len,inside⟩ := remainder_route h L four quota minimum uniqueLow
  intro x xd
  have wx : w≠x := fun eq => L.fresh (eq ▸ xd)
  obtain ⟨v,vd,vx⟩ := Finset.exists_mem_ne wide x
  have vw : v≠w := fun eq => L.fresh (eq ▸ vd)
  let B := (insert w D).erase x
  have wb : w∈B := mem_erase.mpr ⟨wx,mem_insert_self _ _⟩
  have vb : v∈B := mem_erase.mpr ⟨vx,mem_insert_of_mem vd⟩
  obtain ⟨s,sw,u,ub,uw,e⟩ := crossing (noncut x xd) (singleton_subset_iff.mpr wb)
    (singleton_nonempty w) vb (by simpa using vw)
  have se : s=w := mem_singleton.mp sw
  subst s
  have ud : u∈D := (mem_insert.mp (mem_erase.mp ub).2).resolve_left (fun eq => uw (mem_singleton.mpr eq))
  obtain ⟨A,ha⟩ := routes ⟨x,xd⟩ ⟨u,ud⟩ (fun eq => (mem_erase.mp ub).1 (congrArg (fun i:D => i.val) eq).symm)
  let emb := (Embedding.induce (G:=G) (D:Set V)).toHom
  let path : G.Walk x u := A.map emb
  have simple : path.IsPath := ha.isPath.map Subtype.val_injective
  have pathD {v : V} (vP : v∈path.support) : v∈D := by
    rw [show path.support=A.support.map emb from Walk.support_map _ _] at vP
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp vP
    exact d.property
  let tail : G.Walk x z := path.append (Walk.cons e.symm (Walk.cons wr Q))
  have support : tail.support=path.support++w::Q.support := by
    rw [show tail=path.append _ from rfl,Walk.support_append]
    rfl
  have wrOff : w∉Q.support := fun hv => (mem_sdiff.mp (inside _ hv)).2 (mem_insert_self _ _)
  have nt : tail.IsPath := Walk.IsPath.mk' (by
    rw [support]
    apply List.Nodup.append simple.support_nodup (List.nodup_cons.mpr ⟨wrOff,hQ.support_nodup⟩)
    apply List.disjoint_left.mpr
    intro v hv ht
    rcases List.mem_cons.mp ht with eq|qv
    · exact L.fresh (eq ▸ pathD hv)
    exact (mem_sdiff.mp (inside _ qv)).2 (mem_insert_of_mem (pathD hv)))
  have tailC {v : V} (vt : v∈tail.support) : v∈C := by
    rw [support] at vt
    rcases List.mem_append.mp vt with pv|tv
    · exact L.sub (pathD pv)
    rcases List.mem_cons.mp tv with eq|qv
    · exact eq ▸ L.gate
    exact (mem_sdiff.mp (inside _ qv)).1
  have off : List.Disjoint tail.support p.support := List.disjoint_left.mpr (fun _ ht => h.outside _ (tailC ht))
  have length : path.support.length=D.card := by
    rw [show path.support=A.support.map emb from Walk.support_map _ _,List.length_map,ha.length_support]
    simp
  have total : D.card+(1+(k+1)/2)≤tail.support.length := by
    rw [support,List.length_append,List.length_cons,length]
    omega
  exact ⟨z,tail.reverse,nt.reverse,by simpa using off,by simpa using total⟩

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.extended_tails
