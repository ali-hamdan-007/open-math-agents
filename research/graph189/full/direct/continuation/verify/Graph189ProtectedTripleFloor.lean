import Graph189ThreeSelectedPorts

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189ProtectedTripleFloor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}

/-- Every gap has a vertex. In a protected three-port matching the one gap
without an exterior detour bound therefore contributes one extra vertex. -/
theorem order (p : G.Walk x y) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (E : Finset V) (outside : ∀ v∈E, v∉p.support) (three : 3≤E.card)
    (routes : ∀ u v : E, u≠v → ∃ q : (G.induce (E : Set V)).Walk u v, q.IsHamiltonian)
    (rows : ∀ u∈E, 3≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] u)).card) : 4*E.card+4≤Fintype.card V := by
  classical
  obtain ⟨M,count,f,touching⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p E 3 three rows
  let A := M.orderEmbOfFin count
  let T := fun i : Fin 3 => f (M.orderIsoOfFin count i)
  have inj : Function.Injective T := f.injective.comp (M.orderIsoOfFin count).injective
  have touch (i : Fin 3) : G.Adj p.support[(A i).val] (T i).val := touching (M.orderIsoOfFin count i)
  have path (i j : Fin 3) (ne : i≠j) : ExteriorRoute p (T i).val (T j).val E.card := by
    obtain ⟨q,hq⟩ := routes _ _ (inj.ne ne)
    exact route_of_induced_hamilton p E outside hq
  have pre (safe : (A 0).val≤t.val) : E.card≤(A 0).val := by
    obtain ⟨q,hq,dis,len⟩ := path 1 0 (by decide)
    exact len.trans (protected_prefix_of_detour p hp t mx _ safe q hq dis (touch 0).symm)
  have post (safe : t.val≤(A 2).val) : (A 2).val+1+E.card≤p.support.length := by
    obtain ⟨q,hq,dis,len⟩ := path 2 0 (by decide)
    have bound := protected_suffix_of_detour p hp t mx _ safe q hq dis (touch 2)
    omega
  have inner (i j : Fin 3) (ij : i<j) (safe : (A j).val≤t.val ∨ t.val≤(A i).val) :
      (A i).val+1+E.card≤(A j).val := by
    obtain ⟨q,hq,dis,len⟩ := path i j ij.ne
    have bound := protected_interval_of_detour p hp t mx _ _ (A.strictMono ij) safe q hq dis (touch i) (touch j).symm
    omega
  have first := inner 0 1 (by decide)
  have last := inner 1 2 (by decide)
  have ab : (A 0).val < (A 1).val := A.strictMono (by decide : (0:Fin 3)<1)
  have bc : (A 1).val < (A 2).val := A.strictMono (by decide : (1:Fin 3)<2)
  have tail := (A 2).isLt
  have tpos := t.isLt
  have total := card_outside_add_path p hp E outside
  omega

#print axioms order
end Graph189ProtectedTripleFloor
