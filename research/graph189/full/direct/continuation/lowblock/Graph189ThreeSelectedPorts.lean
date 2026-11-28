import Graph189ProtectedMatching

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}

/-- Three selected exterior vertices with three contacts each already
give the order bound if every pair of selected ports spans the whole
exterior. No routing property is required for the other exterior vertices. -/
theorem order_of_three_selected (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (maximal : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (E W : Finset V) (outside : ∀ a∈E, a∉p.support)
    (many : 3 ≤ W.card)
    (contacts : ∀ a∈W, 3 ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] a)).card)
    (paths : ∀ a b : W, a≠b → ExteriorRoute p a.val b.val E.card) :
    4*E.card+3 ≤ Fintype.card V := by
  classical
  obtain ⟨M,sz,f,attached⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p W 3 many contacts
  let A := M.orderEmbOfFin (show M.card=2+1 from sz)
  let B := M.orderIsoOfFin sz
  let T (i : Fin 3) := f (B i)
  have inj : Function.Injective T := f.injective.comp B.injective
  have touch (i : Fin 3) : G.Adj p.support[(A i).val] (T i).val := attached (B i)
  have inner (i : Fin 2) : ExteriorRoute p (T i.castSucc).val (T i.succ).val E.card :=
    paths _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  have before := paths (T 1) (T 0) (inj.ne (by decide))
  have after := paths (T (Fin.last 2)) (T 0) (inj.ne (by decide))
  have bound := protected_matched_route_order p hp t maximal A (fun i => (T i).val) touch inner
    ⟨_,before⟩ ⟨_,after⟩
  have total := card_outside_add_path p hp E outside
  change 3*(E.card+1) ≤ p.support.length at bound
  omega

#print axioms order_of_three_selected
end Graph189ExteriorGap
