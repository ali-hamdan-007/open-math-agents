import Graph189TwoConnectedCoreOrder
import Graph189ExceptionalNeighbors
import Graph189OneExceptionalPair

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap Graph189TerminalLeafClosure
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Paths between prescribed component vertices, with at most one exceptional
unordered pair costing one vertex. The outside endpoints are actual vertices
of the original graph. -/
structure ComponentRoutes {a b : V} (p : G.Walk a b) (C : Finset V) where
  first : V
  second : V
  tails : ∀x∈C,∃y,ExteriorRoute p y x C.card
  short : ∀x y : C,x≠y → ExteriorRoute p x.val y.val (C.card-1)
  full : ∀x y : C,x≠y → ¬(x.val=first ∧ y.val=second ∨ x.val=second ∧ y.val=first) →
    ExteriorRoute p x.val y.val C.card

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
private theorem weaken {a b i j : V} {p : G.Walk a b} {m : ℕ} (route : ExteriorRoute p i j m) :
    ExteriorRoute p i j (m-1) := by
  obtain ⟨q,hq,off,len⟩ := route
  exact ⟨q,hq,off,by omega⟩

theorem dense_component_routes {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (lo : 7≤k) (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (dense : ∀v∈C,k≤G.degree v → C.card+1≤2*(G.neighborFinset v∩C).card) :
    Nonempty (ComponentRoutes p C) := by
  classical
  let J := G.induce (C:Set V)
  have calcDegree (v : C) : J.degree v=(G.neighborFinset v.val∩C).card := by
    rw [show J.degree v=_ from Graph189ExteriorDegreeCycle.degree_induce_filter (C:Set V) v]
    congr 1
  obtain ⟨x,xc,xhigh⟩ := h.high
  have half := xhigh.trans (internal_half h xc xhigh (quota _) minimum uniqueLow)
  have lim := J.degree_lt_card_verts (⟨x,xc⟩ : C)
  change J.degree ⟨x,xc⟩<Fintype.card C at lim
  rw [Fintype.card_coe,calcDegree] at lim
  change (G.neighborFinset x∩C).card<C.card at lim
  have many : 4≤C.card := by omega
  obtain ⟨z,others⟩ : ∃z : C,∀v : C,v≠z → Fintype.card C+1≤2*J.degree v := by
    by_cases low : ∃z∈C,G.degree z<k
    · obtain ⟨z,zc,zlow⟩ := low
      refine ⟨⟨z,zc⟩,fun v ne => ?_⟩
      rw [Fintype.card_coe,calcDegree]
      apply dense _ v.property
      by_contra! miss
      exact ne (Subtype.ext (uniqueLow _ _ miss zlow))
    refine ⟨⟨x,xc⟩,fun v _ => ?_⟩
    rw [Fintype.card_coe,calcDegree]
    exact dense _ v.property (Nat.le_of_not_lt (fun m => low ⟨_,v.property,m⟩))
  have dz : 2≤J.degree z := by
    rw [calcDegree]; exact two_internal h z.property (by omega) quota minimum uniqueLow
  have tail (v : C) : ∃w,ExteriorRoute p w v.val C.card := by
    by_cases eq : v=z
    · subst v
      obtain ⟨u,hu⟩ := card_pos.mp (show 0<(J.neighborFinset z).card by change 0<J.degree z; omega)
      have e := (J.mem_neighborFinset _ _).mp hu
      obtain ⟨q,hq⟩ := prescribed_avoiding_low_neighbors z u z e.ne.symm dz others (fun t => J.irrefl t.2)
      exact ⟨u.val,route_of_induced_hamilton p C h.outside hq⟩
    obtain ⟨q,hq⟩ := prescribed_avoiding_low_neighbors z z v (Ne.symm eq) dz others (fun t => J.irrefl t.1)
    exact ⟨z.val,route_of_induced_hamilton p C h.outside hq⟩
  by_cases three : 3≤J.degree z
  · have all (u v : C) (ne : u≠v) : ExteriorRoute p u.val v.val C.card := by
      obtain ⟨q,hq⟩ := exterior_one_low (G:=J) z u v ne (by
        intro i
        by_cases eq : i=z
        · exact eq ▸ three
        have o := others i eq
        rw [Fintype.card_coe] at o
        omega) others
      exact route_of_induced_hamilton p C h.outside hq
    exact ⟨⟨z.val,z.val,fun u uc => tail ⟨u,uc⟩,fun u v ne => weaken (all u v ne),fun u v ne _ => all u v ne⟩⟩
  have two : J.degree z=2 := by omega
  obtain ⟨s,t,st,pair⟩ := card_eq_two.mp (show (J.neighborFinset z).card=2 from two)
  have special (u v : C) (ne : u≠v) (zu : J.Adj z u) (zv : J.Adj z v) :
      u.val=s.val ∧ v.val=t.val ∨ u.val=t.val ∧ v.val=s.val := by
    have us := (J.mem_neighborFinset _ _).mpr zu
    have vs := (J.mem_neighborFinset _ _).mpr zv
    rw [pair] at us vs
    simp only [mem_insert,mem_singleton] at us vs
    rcases us with rfl|rfl <;> rcases vs with rfl|rfl <;> simp_all
  refine ⟨⟨s.val,t.val,fun v vc => tail ⟨v,vc⟩,?_,?_⟩⟩
  · intro u v ne
    by_cases both : J.Adj z u ∧ J.Adj z v
    · obtain ⟨q,hq,len,_⟩ := prescribed_between_low_neighbors z u v ne two others both.1 both.2
      let emb := (Embedding.induce (G:=G) (C:Set V)).toHom
      refine ⟨q.map emb,hq.map Subtype.val_injective,?_,?_⟩
      · rw [List.disjoint_left]
        intro w hit
        change w∈(q.map emb).support at hit
        rw [Walk.support_map] at hit
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hit
        exact h.outside _ v.property
      change q.support.length+1=Fintype.card C at len
      rw [Fintype.card_coe] at len
      change C.card-1≤(q.map emb).support.length
      rw [Walk.support_map,List.length_map]
      omega
    obtain ⟨q,hq⟩ := prescribed_avoiding_low_neighbors z u v ne dz others both
    exact weaken (route_of_induced_hamilton p C h.outside hq)
  intro u v ne good
  obtain ⟨q,hq⟩ := prescribed_avoiding_low_neighbors z u v ne dz others (fun both => good (special u v ne both.1 both.2))
  exact route_of_induced_hamilton p C h.outside hq

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.dense_component_routes
