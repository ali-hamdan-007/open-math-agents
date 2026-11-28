import Graph189MatchedOrder
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open SimpleGraph Finset
open scoped BigOperators
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- Individual gap lengths can be added; the routes need not be disjoint from one
another because each route is spliced into the original longest path separately. -/
theorem longest_variable_route_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {j left right : ℕ} (sizes : ℕ → ℕ) (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) (sizes i.val))
    (before : ∃ a, ExteriorRoute p a (port 0) left)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b right) :
    left + j + (∑ i∈Finset.range j, sizes i) + 1 + right ≤ p.support.length := by
  obtain ⟨a,q,hq,hdis,hlen⟩ := before
  have hfirst := prefix_of_detour p hp longest (mark 0) q hq hdis (contacts 0).symm
  obtain ⟨b,r,hr,hother,hend⟩ := after
  have hlast := suffix_of_detour p hp longest (mark (Fin.last j)) r hr hother (contacts _)
  have spread (i : Fin j) : (mark i.castSucc).val+1+sizes i.val ≤ (mark i.succ).val := by
    obtain ⟨t,ht,hd,hm⟩ := inner i
    have bound := interval_of_detour p hp longest _ _ (mark.strictMono i.castSucc_lt_succ)
      t ht hd (contacts _) (contacts _).symm
    omega
  have positions : ∀ i : Fin (j+1), left+i.val+(∑ h∈Finset.range i.val, sizes h) ≤ (mark i).val := by
    intro i
    induction i using Fin.induction with
    | zero => simpa using hlen.trans hfirst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_succ,Fin.val_castSucc,Finset.sum_range_succ] at ih ⊢
      omega
  have h := positions (Fin.last j)
  simp only [Fin.val_last] at h
  omega

/-- One short interval loses at most one vertex in the final ambient order. -/
theorem near_core_order [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ v∈W, v∉p.support)
    {j m : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length) (port : Fin (j+1) → V)
    (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (exception : ℕ) (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ)
      (if i.val=exception then m-1 else m))
    (before : ∃ a, ExteriorRoute p a (port 0) m)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b m) :
    W.card+(j+1)+(j+2)*m ≤ Fintype.card V+1 := by
  let cost := fun i : ℕ => if i=exception then m-1 else m
  have plen := longest_variable_route_order p hp longest cost mark port contacts inner before after
  have total := card_outside_add_path p hp W outside
  have parts : (∑ _i∈Finset.range j, m) ≤
      ∑ i∈Finset.range j, (cost i + (if i=exception then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases eq : i=exception
    · simp [cost,eq]
      omega
    · simp [cost,eq]
  rw [Finset.sum_add_distrib] at parts
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,Finset.sum_ite_eq',
    Finset.mem_range] at parts
  split at parts <;> simp only [Nat.succ_mul] <;> omega

#print axioms near_core_order
end Graph189ExteriorGap
