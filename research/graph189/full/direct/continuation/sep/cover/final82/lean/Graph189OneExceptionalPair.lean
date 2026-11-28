import Graph189AlmostSpanningGaps

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

omit [Fintype V] [DecidableEq V] in
private theorem bad_indices_eq {j : ℕ} (f : Fin (j+1) ↪ V) (u v : V) {i l : Fin j}
    (hi : f i.castSucc=u ∧ f i.succ=v ∨ f i.castSucc=v ∧ f i.succ=u)
    (hl : f l.castSucc=u ∧ f l.succ=v ∨ f l.castSucc=v ∧ f l.succ=u) : i=l := by
  have parallel (h : f i.castSucc=f l.castSucc) : i=l :=
    Fin.ext (congrArg (fun k : Fin (j+1) => k.val) (f.injective h))
  have cross (h₁ : f i.castSucc=f l.succ) (h₂ : f i.succ=f l.castSucc) : False := by
    have e₁ := congrArg Fin.val (f.injective h₁)
    have e₂ := congrArg Fin.val (f.injective h₂)
    simp only [Fin.val_succ,Fin.val_castSucc] at e₁ e₂
    omega
  rcases hi with h | h <;> rcases hl with k | k
  · exact parallel (h.1.trans k.1.symm)
  · exact (cross (h.1.trans k.2.symm) (h.2.trans k.1.symm)).elim
  · exact (cross (h.1.trans k.2.symm) (h.2.trans k.1.symm)).elim
  · exact parallel (h.1.trans k.1.symm)

/-- A single exceptional unordered terminal pair costs at most one vertex in
the near-Hamilton-connected exterior estimate, for an actual contact matching. -/
theorem exterior_order_one_exceptional_pair (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ v∈W, v∉p.support)
    {j m : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length) (port : Fin (j+1) ↪ V)
    (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i)) (u v : V)
    (fallback : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) (m-1))
    (regular : ∀ i : Fin j, ¬(port i.castSucc=u ∧ port i.succ=v ∨ port i.castSucc=v ∧ port i.succ=u) →
      ExteriorRoute p (port i.castSucc) (port i.succ) m)
    (before : ∃ a, ExteriorRoute p a (port 0) m)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b m) :
    W.card+(j+1)+(j+2)*m ≤ Fintype.card V+1 := by
  classical
  let bad := fun i : Fin j => port i.castSucc=u ∧ port i.succ=v ∨ port i.castSucc=v ∧ port i.succ=u
  have one : ∃ t : ℕ, ∀ i : Fin j, bad i → i.val=t := by
    by_cases ex : ∃ i, bad i
    · obtain ⟨i,hi⟩ := ex
      exact ⟨i.val,fun l hl => congrArg Fin.val (bad_indices_eq port u v hl hi)⟩
    · exact ⟨j,fun i hi => (ex ⟨i,hi⟩).elim⟩
  obtain ⟨t,unique⟩ := one
  apply near_core_order p hp longest W outside mark port contacts t _ before after
  intro i
  by_cases eq : i.val=t
  · simpa [eq] using fallback i
  · simpa [eq] using regular i (fun h => eq (unique i h))

#print axioms exterior_order_one_exceptional_pair
end Graph189ExteriorGap
