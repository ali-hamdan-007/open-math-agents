import Graph189OrdinaryOmission

open SimpleGraph Finset Graph189ExteriorDegreeCycle
namespace Graph189PairLinearGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At qualifying orders strictly below 5k−11, a path missing at most k−3 vertices
suffices. The minimum degree and low location are unrestricted. -/
theorem traceable_under_five (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : 2≤G.vertexConnectivity) (large : 10≤G.secondSmallestDegree)
    (order : Fintype.card V+11<5*G.secondSmallestDegree) {a b : V} (r : G.Walk a b) (hr : r.IsPath)
    (near : Fintype.card V+3≤r.support.length+G.secondSmallestDegree) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have connect := Graph189CutSides.connectivity_le_degree (G:=G) z
  by_cases degree : G.degree z=2
  · exact Graph189DegreeTwoOriginal.traceable hc cap conn z degree (by omega)
  have min (v : V) : 3≤G.degree v := by have := G.minDegree_le_degree v; omega
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_contra bad
  have noLow (v : V) (low : G.degree v<G.secondSmallestDegree)
      (del : ∃x y,∃q : (G.induce {w : V | w≠v}).Walk x y,q.IsHamiltonian) : False := by
    obtain ⟨x,y,q,hq⟩ := del
    by_cases four : 4≤G.degree v
    · have bound := Graph189ExteriorGap.order_of_traceable_low_deletion v low point bad q hq
        (s:=4) (by decide) (by omega) four
      omega
    exact bad (Graph189ExteriorGap.traceable_of_low_deletion hc v point q hq (min v) (by omega))
  obtain ⟨x,y,p,hp,maximal⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let m := (p.support.toFinsetᶜ : Finset V).card
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+m=Fintype.card V at total
  have floor := gap_of_no_hamiltonian_low_deletion bad (by omega) point min noLow x y p hp
  have longest := maximal r hr
  have rlen := r.length_support
  have plen := p.length_support
  let k := G.secondSmallestDegree
  have room : m+3≤k := by change m+3≤G.secondSmallestDegree; omega
  obtain ⟨size,product⟩ := Graph189OrdinaryOmission.small_exterior_order p hp maximal point min (m:=m) rfl
    (by omega) room
  change (k+1)/2+1≤m at size
  change m*(k+3-m)≤Fintype.card V+2 at product
  change 10≤k at large
  change Fintype.card V+11<5*k at order
  have step : 6*(k-3)≤m*(k+3-m) := by
    zify [show 3≤k by omega,show m≤k+3 by omega]
    nlinarith only [mul_nonneg (show 0≤(m:ℤ)-6 by omega) (show 0≤(k:ℤ)-3-m by omega)]
  omega

/-- The four-times-degree range is automatic from two sole-nearest sides. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : 2≤G.vertexConnectivity) (large : 10≤G.secondSmallestDegree)
    (order : Fintype.card V+3≤4*G.secondSmallestDegree) {a b : V} (r : G.Walk a b) (hr : r.IsPath)
    (near : Fintype.card V+3≤r.support.length+G.secondSmallestDegree) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian :=
  traceable_under_five hc cap conn large (by omega) r hr near

#print axioms traceable_under_five
#print axioms traceable
end Graph189PairLinearGap
