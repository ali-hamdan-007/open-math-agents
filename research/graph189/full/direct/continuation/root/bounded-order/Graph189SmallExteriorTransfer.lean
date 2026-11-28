import Graph189SmallExteriorComponent

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] in
theorem Saturated.transfer {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (sat : Saturated p C k)
    {u v x : V} (uc : u∈C) (vc : v∈C) (vh : k≤G.degree v) (on : x∈p.support)
    (edge : G.Adj x u) : G.Adj x v := by
  obtain ⟨A,_,rows,cover⟩ := sat.marks
  obtain ⟨i,valid,eq⟩ := List.mem_iff_getElem.mp on
  let j : Fin p.support.length := ⟨i,valid⟩
  have mem := cover _ uc j (by simpa [j,eq] using edge)
  have hit := (rows v vc vh j).mpr mem
  simpa [j,eq] using hit

theorem small_exterior_transfer {a b u v x : V} {p : G.Walk a b} (hp : p.IsPath)
    (mx : ∀{i j},∀q : G.Walk i j,q.IsPath → q.length≤p.length) {k : ℕ}
    (size : p.support.toFinsetᶜ.card+1≤k) (uo : u∉p.support) (vo : v∉p.support) (vh : k≤G.degree v)
    (joined : ∃y,y∉p.support ∧ G.Adj u y) (on : x∈p.support) (edge : G.Adj x u)
    (lo : 7≤k) (upper : Fintype.card V≤5*k-5) (conn : 3≤G.vertexConnectivity)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (gap : p.support.length+(k+1)/2+1<Fintype.card V) : G.Adj x v := by
  obtain ⟨C,h,vc,all⟩ := chosen_of_small_exterior hp mx size vo vh quota minimum uniqueLow
  have sub : C⊆p.support.toFinsetᶜ := fun z zc => mem_compl.mpr
    (fun on => h.outside _ zc (List.mem_toFinset.mp on))
  have small := card_le_card sub
  have dense (z : V) (zc : z∈C) (high : k≤G.degree z) : C.card+1≤2*(G.neighborFinset z∩C).card := by
    have half := internal_half h zc high (quota _) minimum uniqueLow
    omega
  have sat := dense_clique h dense lo upper conn quota minimum uniqueLow gap
  apply sat.transfer (u:=u) ?_ vc vh on edge
  by_cases high : k≤G.degree u
  · exact all u uo high
  obtain ⟨y,yo,uy⟩ := joined
  have yh : k≤G.degree y := by by_contra! low; exact uy.ne (uniqueLow _ _ (by omega) low)
  exact h.closed y (all y yo yh) u uy.symm uo

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.small_exterior_transfer
