import Graph189ContactIntervals

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- A route uses actual vertices disjoint from the given path. -/
def ExteriorRoute (p : G.Walk x y) (a b : V) (k : ℕ) : Prop :=
  ∃ q : G.Walk a b, q.IsPath ∧ List.Disjoint q.support p.support ∧ k≤q.support.length

/-- Distinct ordered marks on an arbitrary longest path, with arbitrary actual exterior
routes between successive ports, give the full two-tail length inequality. -/
theorem longest_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {j middle left right : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) middle)
    (before : ∃ a, ExteriorRoute p a (port 0) left)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b right) :
    left + j*(middle+1) + 1 + right ≤ p.support.length := by
  obtain ⟨a,q,hq,hdis,hlen⟩ := before
  have hfirst := prefix_of_detour p hp longest (mark 0) q hq hdis (contacts 0).symm
  obtain ⟨b,r,hr,hother,hend⟩ := after
  have hlast := suffix_of_detour p hp longest (mark (Fin.last j)) r hr hother (contacts _)
  have spread (i : Fin j) : (mark i.castSucc).val + 1 + middle ≤ (mark i.succ).val := by
    obtain ⟨t,ht,hd,hm⟩ := inner i
    have bound := interval_of_detour p hp longest _ _ (mark.strictMono i.castSucc_lt_succ)
      t ht hd (contacts _) (contacts _).symm
    omega
  have positions : ∀ i : Fin (j+1), left+i.val*(middle+1) ≤ (mark i).val := by
    intro i
    induction i using Fin.induction with
    | zero => simpa using hlen.trans hfirst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have last := positions (Fin.last j)
  simp only [Fin.val_last] at last
  omega

/-- A population disjoint from a path contributes its full size to the ambient order. -/
theorem card_outside_add_path [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support) :
    W.card+p.support.length ≤ Fintype.card V := by
  have dis : Disjoint W p.support.toFinset := Finset.disjoint_left.mpr (by
    intro z hz h
    exact outside z hz (List.mem_toFinset.mp h))
  have bound := (W ∪ p.support.toFinset).card_le_univ
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup hp.support_nodup] at bound
  exact bound

/-- This is the direct graph bound m0+J+(J+1)N+2A used by the finite exterior test.
Its assumptions are actual paths and adjacencies; marks may be any matching of these ports. -/
theorem exterior_order_with_tails [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support)
    {j N A : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length) (port : Fin (j+1) → V)
    (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) N)
    (before : ∃ a, ExteriorRoute p a (port 0) (N+A))
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b (N+A)) :
    W.card + (j+1) + (j+2)*N + 2*A ≤ Fintype.card V := by
  have lengths := longest_matched_route_order p hp longest mark port contacts inner before after
  have total := card_outside_add_path p hp W outside
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at lengths ⊢
  omega

#print axioms longest_matched_route_order
#print axioms card_outside_add_path
#print axioms exterior_order_with_tails
end Graph189ExteriorGap
