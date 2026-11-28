import Graph189DenseComponentRoutes
import Graph189BoundaryMatching

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] in
/-- A matching on actual positions incurs at most one lost exterior vertex
over all its gaps, even when its exceptional port pair is used. -/
theorem near_match_with_omissions {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (r : ComponentRoutes p C) (W : Finset V) (outside : ∀v∈W,v∉p.support) (M : Finset (Fin p.support.length)) (nonempty : M.Nonempty)
    (f : M ↪ C) (edges : ∀i : M,G.Adj p.support[i.val.val] (f i).val) :
    W.card+(M.card+1)*C.card+M.card≤Fintype.card V+1 := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ,M.card=j+1 := ⟨M.card-1,by have := card_pos.mpr nonempty; omega⟩
  let iso := M.orderIsoOfFin hj
  let mark := M.orderEmbOfFin hj
  let port := iso.toEquiv.toEmbedding.trans f
  let lift : C ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let assigned := port.trans lift
  have adj (i : Fin (j+1)) : G.Adj p.support[(mark i).val] (assigned i) := edges (iso i)
  have ne (i : Fin j) : port i.castSucc≠port i.succ := port.injective.ne (ne_of_lt i.castSucc_lt_succ)
  obtain ⟨w,q,hq,off,len⟩ := r.tails (port (Fin.last j)).val (port (Fin.last j)).property
  have after : ExteriorRoute p (port (Fin.last j)).val w C.card :=
    ⟨q.reverse,hq.reverse,by simpa using off,by simpa using len⟩
  have bound := exterior_order_one_exceptional_pair p h.path h.longest W outside mark assigned adj
    r.first r.second (fun i => r.short _ _ (ne i)) (fun i good => r.full _ _ (ne i) good)
    (r.tails (port 0).val (port 0).property) ⟨w,after⟩
  rw [hj]
  simp only [Nat.add_mul,Nat.one_mul] at bound ⊢
  omega

omit [Nontrivial V] in
theorem near_match_order {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (r : ComponentRoutes p C) (M : Finset (Fin p.support.length)) (nonempty : M.Nonempty)
    (f : M ↪ C) (edges : ∀i : M,G.Adj p.support[i.val.val] (f i).val) :
    (M.card+2)*C.card+M.card≤Fintype.card V+1 := by
  have bound := near_match_with_omissions h r C h.outside M nonempty f edges
  simp only [Nat.add_mul,Nat.one_mul] at bound ⊢
  omega

omit [Nontrivial V] in
/-- Three-connectivity supplies the matching. In the checked residual order
window even the exceptional pair cannot permit a component of order k−1. -/
theorem dense_component_size {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (r : ComponentRoutes p C) (many : 3≤C.card) (upper : Fintype.card V≤5*k-5) (lo : 7≤k)
    (conn : ∀cut : Finset V,cut.card<3 → (G.induce {z : V|z∉cut}).Connected) :
    C.card+2≤k := by
  classical
  obtain ⟨x,xc,_⟩ := h.high
  obtain ⟨w,q,hq,_,len⟩ := r.tails x xc
  have longest := h.longest q hq
  rw [Walk.length_support] at len
  have smallP : 3≤p.support.toFinset.card := by
    rw [List.toFinset_card_of_nodup h.path.support_nodup,Walk.length_support]
    omega
  obtain ⟨A,inP,wide,f,edge⟩ := matching_at_component_boundary p.support.toFinset C
    (disjoint_left.mpr (fun v vp vc => h.outside v vc (List.mem_toFinset.mp vp)))
    (fun v vc u out e => List.mem_toFinset.mpr (by by_contra miss; exact out (h.closed v vc u e miss)))
    smallP many conn
  obtain ⟨M,eq,eval⟩ := vertex_positions_equiv p A (fun v hv => List.mem_toFinset.mp (inP hv))
  have size : M.card=A.card := by simpa using Fintype.card_congr eq
  have bound := near_match_order h r M (card_pos.mp (by omega)) (eq.toEmbedding.trans f) (by
    intro i
    rw [eval]
    exact edge (eq i))
  have product := Nat.mul_le_mul_right C.card (show 5≤M.card+2 by omega)
  omega

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.near_match_order
#print axioms Graph189ExteriorLeaf.dense_component_size
