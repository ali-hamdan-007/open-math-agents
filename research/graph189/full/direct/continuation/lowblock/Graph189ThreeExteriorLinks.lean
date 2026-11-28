import Graph189TwoExteriorLinks

open SimpleGraph Finset Graph189ExteriorGap Graph189TwoExteriorLinks
namespace Graph189ThreeExteriorLinks
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three independent trimmed links give two interior gaps and two tails.
Every tail and both prescribed routes consist of actual exterior vertices. -/
theorem order_of_routes {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length≤p.length)
    (conn : 3≤G.vertexConnectivity) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (wide : 3≤W.card) (long : 3≤p.support.length) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m≤q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t≤q.support.length ∧ ∀ v∈q.support,v∈W) :
    W.card+2*m+2*t+3≤Fintype.card V := by
  obtain ⟨A,inj,apart⟩ := arms p hp W outside 3 conn wide long
  have count := card_outside_add_path p hp W outside
  have bound (i j k : Fin 3) (h : (A i).mark<(A j).mark) (g : (A j).mark<(A k).mark) :
      W.card+2*m+2*t+3≤Fintype.card V := by
    have d : i≠j := fun e => h.ne (congrArg (fun t => (A t).mark) e)
    have e : j≠k := fun e => g.ne (congrArg (fun t => (A t).mark) e)
    obtain ⟨l₁,g₁,_⟩ := ordered_positions hp mx outside _ _ h (apart i j d) start join
    obtain ⟨_,g₂,r₂⟩ := ordered_positions hp mx outside _ _ g (apart j k e) start join
    omega
  have diff (i j : Fin 3) (ne : i≠j) : (A i).mark≠(A j).mark := fun e => ne (inj e)
  rcases lt_or_gt_of_ne (diff 0 1 (by decide)) with h|h
  · rcases lt_or_gt_of_ne (diff 1 2 (by decide)) with g|g
    · exact bound 0 1 2 h g
    rcases lt_or_gt_of_ne (diff 0 2 (by decide)) with f|f
    · exact bound 0 2 1 f g
    · exact bound 2 0 1 f h
  · rcases lt_or_gt_of_ne (diff 0 2 (by decide)) with g|g
    · exact bound 1 0 2 h g
    rcases lt_or_gt_of_ne (diff 1 2 (by decide)) with f|f
    · exact bound 1 2 0 f g
    · exact bound 2 1 0 f h

/-- In a three-connected graph, an exterior five-cycle of an ordinary
longest path already forces at least twenty-six ambient vertices. -/
theorem order_of_cycle {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length≤p.length)
    (conn : 3≤G.vertexConnectivity) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (outside : ∀ v∈C.support,v∉p.support) :
    3*C.length+2*((C.length+1)/2)+5≤Fintype.card V := by
  classical
  obtain ⟨width,start,pair⟩ := cycle_routes C hc
  obtain ⟨_,q,hq,ql,_⟩ := start r (List.mem_toFinset.mpr C.start_mem_support)
  have maximal := mx q hq
  have left := q.length_support
  have right := p.length_support
  have three := hc.three_le_length
  have ord := order_of_routes p hp mx conn C.support.toFinset (fun v hv => outside v (List.mem_toFinset.mp hv))
    (by omega) (by omega) start pair
  omega

#print axioms order_of_cycle
end Graph189ThreeExteriorLinks
