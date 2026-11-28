import Graph189LongLeafCycle

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- From each prescribed port of a proper Hamilton-connected core, route
through the core and one further vertex without repeating the port. -/
theorem bonus_vertex {a b : V} {p : G.Walk a b} {C H : Finset V} {k : ℕ}
    (h : Chosen p C k) (two : ∀v∈C,(G.induce (C.erase v:Set V)).Preconnected)
    (sub : H⊆C) (proper : H.card<C.card) (wide : 1<H.card)
    (routes : ∀u v : H,u≠v → ∃q : (G.induce (H:Set V)).Walk u v,q.IsHamiltonian) :
    ∀x∈H,∃y,ExteriorRoute p y x (H.card+1) := by
  classical
  intro x xh
  obtain ⟨v,vc,vh⟩ := Finset.exists_mem_notMem_of_card_lt_card proper
  obtain ⟨u,uh,ux⟩ := Finset.exists_mem_ne wide x
  have vx : v≠x := fun eq => vh (eq ▸ xh)
  obtain ⟨i,ih,z,zc,zh,edge⟩ := crossing (two x (sub xh))
    (show H.erase x⊆C.erase x from erase_subset_erase _ sub)
    ⟨u,mem_erase.mpr ⟨ux,uh⟩⟩ (mem_erase.mpr ⟨vx,vc⟩) (fun m => vh (mem_erase.mp m).2)
  have iz : i≠x := (mem_erase.mp ih).1
  have zo : z∉H := fun m => zh (mem_erase.mpr ⟨(mem_erase.mp zc).1,m⟩)
  obtain ⟨q,hq⟩ := routes ⟨x,xh⟩ ⟨i,(mem_erase.mp ih).2⟩ (fun eq => iz (congrArg (fun t:H => t.val) eq).symm)
  let emb := (Embedding.induce (G:=G) (H:Set V)).toHom
  let s : G.Walk x i := q.map emb
  have inside {v : V} (vs : v∈s.support) : v∈H := by
    rw [show s.support=q.support.map emb from Walk.support_map _ _] at vs
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp vs
    exact u.property
  have path : s.IsPath := hq.isPath.map Subtype.val_injective
  have route := path.concat (fun mem => zo (inside mem)) edge
  have off : List.Disjoint (s.concat edge).support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [Walk.support_concat] at hv
    rcases List.mem_append.mp hv with m|m
    · exact h.outside _ (sub (inside m))
    exact (List.mem_singleton.mp m) ▸ h.outside _ (mem_erase.mp zc).2
  have len : (s.concat edge).support.length=H.card+1 := by
    rw [Walk.support_concat,List.length_append,show s.support=q.support.map emb from Walk.support_map _ _,
      List.length_map,hq.length_support]
    simp
  exact ⟨z,(s.concat edge).reverse,route.reverse,by
    rw [Walk.support_reverse]
    exact List.disjoint_left.mpr (fun _ hv => List.disjoint_left.mp off (List.mem_reverse.mp hv)),by simpa using len.ge⟩

private theorem arithmetic {k q m n c : ℕ} (lo : 7≤k) (hi : k≤21) (half : k≤2*q)
    (large : 2*q≤m) (cy : 2*q≤c) (span : m+2*c+2*((c+1)/2)+5≤n) (ord : n≤5*k-5)
    (core : 3*q+3≤2*k → ∃e≤1,
      let t := 2*k-(3*q+1)+e
      m+t+(t+1)*(q+1-e)+2≤n) : False := by
  have table : (List.range 15).all (fun j => let k := 7+j
    (List.range (k+1)).all (fun q => decide (k≤2*q → 5*k-5<8*q+5 ∨
      3*q+3≤2*k ∧ ∀e : Fin 2,let t := 2*k-(3*q+1)+e.val
        5*k-5<2*q+t+(t+1)*(q+1-e.val)+2)))=true := by decide
  have row := List.all_eq_true.mp table (k-7) (List.mem_range.mpr (by omega))
  rw [show 7+(k-7)=k by omega] at row
  have test := of_decide_eq_true (List.all_eq_true.mp row q (List.mem_range.mpr (by omega))) half
  rcases test with no|⟨dense,tiny⟩
  · omega
  obtain ⟨e,small,bound⟩ := core dense
  have bad := tiny ⟨e,by omega⟩
  change 5*k-5<2*q+(2*k-(3*q+1)+e)+(2*k-(3*q+1)+e+1)*(q+1-e)+2 at bad
  omega

/-- The large two-connected exterior is impossible once its Fan cycle is
available. The finite original degree range needs just one extra tail vertex. -/
theorem no_large_component {a b x z : V} {p : G.Walk a b} {C : Finset V} {k : ℕ}
    (h : Chosen p C k) (conn : 3≤G.vertexConnectivity)
    (two : ∀v∈C,(G.induce (C.erase v:Set V)).Preconnected)
    (xc : x∈C) (high : k≤G.degree x) (large : 2*(G.neighborFinset x∩C).card≤C.card)
    (Z : G.Walk z z) (cycle : Z.IsCycle) (inside : ∀v∈Z.support,v∈C)
    (long : 2*(G.neighborFinset x∩C).card≤Z.length)
    (lo : 7≤k) (hi : k≤21) (order : Fintype.card V≤5*k-5)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) : False := by
  classical
  let N := G.neighborFinset x∩C
  let q := N.card
  let X := insert x N
  let H := X.filter (fun v => k≤G.degree v)
  let e := (X \ H).card
  let r := (C.filter (fun v => G.dist x v=2)).card
  have half := high.trans (internal_half h xc high (quota _) minimum uniqueLow)
  change k≤2*q at half
  change 2*q≤C.card at large
  apply arithmetic lo hi half large long (cycle_span h conn Z cycle inside) order
  intro dense
  obtain ⟨wide,sub,radius,rows,routes⟩ := high_core h xc high (two x xc) minimum uniqueLow (quota _) dense
  change q≤H.card at wide
  change r+k+e≤2*q+1 at radius
  have sum := card_sdiff_add_card_eq_card (show H⊆X from filter_subset _ _)
  change e+H.card=X.card at sum
  have nox : x∉N := fun m => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_inter.mp m).1)
  have sz : X.card=q+1 := card_insert_of_notMem nox
  let t := 2*k-(3*q+1)+e
  have tpos : 0<t := by dsimp [t]; omega
  have enough : t≤H.card := by dsimp [t]; omega
  have contact (y : V) (yh : y∈H) : t≤(contactPositions p y).card := by
    have bound := rows y yh
    change k≤(contactPositions p y).card+q+r at bound
    dsimp [t]; omega
  have tail := bonus_vertex (H:=H) h two sub (show H.card<C.card by omega) (show 1<H.card by omega) routes
  have bound := core_ports h H sub tpos enough contact routes tail
  have hs : q+1-e=H.card := by omega
  refine ⟨e,by omega,?_⟩
  change C.card+t+(t+1)*(q+1-e)+2≤Fintype.card V
  simpa only [hs,Nat.mul_one] using bound

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.no_large_component
