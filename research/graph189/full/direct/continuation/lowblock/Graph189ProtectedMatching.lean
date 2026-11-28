import Graph189ProtectedIntervals
import Graph189ExteriorMatching
import Graph189ExteriorAttachment

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- Distinct matched contacts on a longest path through one prescribed
vertex. Exactly one of its two tails and internal gaps can lose its detour
bound when the prescribed vertex is required to stay on the path. -/
theorem protected_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    {j m : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) m)
    (before : ∃ a, ExteriorRoute p a (port 0) m)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b m) :
    (j+1)*(m+1) ≤ p.support.length := by
  let pos (i : Fin (j+1)) := (mark i).val + if t < mark i then m else 0
  have first : m ≤ pos 0 := by
    by_cases h : t < mark 0
    · simp [pos,h]
    obtain ⟨a,q,hq,dis,order⟩ := before
    have bound := protected_prefix_of_detour p hp t longest (mark 0) (le_of_not_gt h)
      q hq dis (contacts 0).symm
    simpa [pos,h] using order.trans bound
  have step (i : Fin j) : pos i.castSucc + (m+1) ≤ pos i.succ := by
    have lt := mark.strictMono i.castSucc_lt_succ
    by_cases left : t < mark i.castSucc
    · obtain ⟨q,hq,dis,order⟩ := inner i
      have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inr left.le)
        q hq dis (contacts _) (contacts _).symm
      simp only [pos,if_pos left,if_pos (left.trans lt)]
      omega
    by_cases right : t < mark i.succ
    · simp only [pos,if_neg left,if_pos right]
      change (mark i.castSucc).val < (mark i.succ).val at lt
      omega
    obtain ⟨q,hq,dis,order⟩ := inner i
    have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inl (le_of_not_gt right))
      q hq dis (contacts _) (contacts _).symm
    simp only [pos,if_neg left,if_neg right]
    omega
  have positions (i : Fin (j+1)) : m+i.val*(m+1) ≤ pos i := by
    induction i using Fin.induction with
    | zero => simpa using first
    | succ i ih =>
      have hs := step i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have finish : pos (Fin.last j)+1 ≤ p.support.length := by
    by_cases h : t < mark (Fin.last j)
    · obtain ⟨b,q,hq,dis,order⟩ := after
      have bound := protected_suffix_of_detour p hp t longest _ h.le q hq dis (contacts _)
      simp only [pos,if_pos h]
      omega
    · simpa [pos,h] using (mark (Fin.last j)).isLt
  have last := positions (Fin.last j)
  simp only [Fin.val_last,Nat.succ_mul] at last ⊢
  omega

/-- The protected bound for an actual matching to a Hamilton-connected exterior. -/
theorem protected_hamilton_connected_matching [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+1)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := protected_matched_route_order p hp t longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul] at bound ⊢
  omega

/-- A Hamilton-connected exterior whose vertices have many path contacts
forces an order lower bound even when every competing path must contain z. -/
theorem protected_order_of_contacts [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath) {z : V} (zp : z ∈ p.support)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → z ∈ r.support → r.length ≤ p.length)
    (W : Finset V) (size : 1 < W.card) (outside : ∀ a ∈ W, a ∉ p.support)
    (hconn : ∀ a b : W, a ≠ b → ∃ q : (G.induce (W : Set V)).Walk a b, q.IsHamiltonian)
    {u : ℕ} (nonzero : 0 < u) (enough : u ≤ W.card)
    (rows : ∀ w ∈ W, u ≤ ((Finset.univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card) :
    (u+1)*W.card+u ≤ Fintype.card V := by
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp zp
  let t : Fin p.support.length := ⟨i,hi⟩
  obtain ⟨marks,card,attach,contacts⟩ :=
    Graph189ExteriorAttachment.marks_of_many_neighbors p W u enough rows
  have bound := protected_hamilton_connected_matching p hp t
    (fun r hr member => longest r hr (e ▸ member)) W size outside hconn marks
      (card_pos.mp (by omega)) attach contacts
  rwa [card] at bound

#print axioms protected_matched_route_order
#print axioms protected_hamilton_connected_matching
#print axioms protected_order_of_contacts
end Graph189ExteriorGap
