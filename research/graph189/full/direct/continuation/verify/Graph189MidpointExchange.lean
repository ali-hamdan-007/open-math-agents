import Graph189ContactColumns
import Mathlib.Logic.Equiv.Basic

open SimpleGraph Graph189ExteriorGap
namespace Graph189MidpointExchange
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Exchange an omitted vertex with the middle vertex of a two-edge segment. -/
theorem exchange {a b z : V} (p : G.Walk a b) (hp : p.IsPath)
    (out : z ∉ p.support) (i : ℕ) (ri : i+2 < p.support.length)
    (first : G.Adj (p.getVert i) z) (last : G.Adj (p.getVert (i+2)) z) :
    ∃ u v, ∃ r : G.Walk u v, r.IsPath ∧ r.length = p.length ∧ p.getVert (i+1) ∉ r.support ∧
      ∀ t, t ≠ p.getVert (i+1) → t = z ∨ t ∈ p.support → t ∈ r.support := by
  classical
  let m := p.getVert (i+1)
  let f := Equiv.swap m z
  let L := p.support.map f
  have length := p.length_support
  have fixed (j : ℕ) (rj : j < p.support.length) (different : j ≠ i+1) :
      f (p.getVert j) = p.getVert j := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq
      exact different (hp.getVert_injOn (by change j ≤ p.length; omega)
        (by change i+1 ≤ p.length; omega) eq)
    · intro eq
      exact out (eq ▸ p.getVert_mem_support j)
  have exchanged : f (p.getVert (i+1)) = z := Equiv.swap_apply_left m z
  have chain : L.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro j hj
    have bound : j+1 < p.support.length := by simpa [L] using hj
    simp only [L,List.getElem_map]
    rw [get_at p (by omega : j<p.support.length),get_at p bound]
    by_cases eq : j=i
    · subst j
      rw [exchanged,fixed _ (by omega) (by omega)]
      exact first
    by_cases eq' : j=i+1
    · subst j
      rw [exchanged,fixed _ (by omega) (by omega)]
      exact last.symm
    rw [fixed _ (by omega) eq',fixed _ bound (by omega)]
    exact p.adj_getVert_succ (by omega)
  have nd : L.Nodup := hp.support_nodup.map f.injective
  have nonempty : L ≠ [] := by simp [L,p.support_ne_nil]
  let r := Walk.ofSupport L nonempty chain
  have support : r.support = L := Walk.support_ofSupport nonempty chain
  refine ⟨_,_,r,Walk.IsPath.mk' (by rwa [support]),?_,?_,?_⟩
  · have len := r.length_support
    rw [support] at len
    simp only [L,List.length_map] at len
    omega
  · rw [support]
    intro h
    obtain ⟨v,hv,he⟩ := List.mem_map.mp h
    have fz : f z = m := Equiv.swap_apply_right m z
    exact out ((f.injective (he.trans fz.symm)) ▸ hv)

  · intro t diff h
    rw [support]
    rcases h with hz | ht
    · exact List.mem_map.mpr ⟨m,p.getVert_mem_support _,(Equiv.swap_apply_left m z).trans hz.symm⟩
    · exact List.mem_map.mpr ⟨t,ht,Equiv.swap_apply_of_ne_of_ne diff
        (fun e => out (e ▸ ht))⟩

end Graph189MidpointExchange
#print axioms Graph189MidpointExchange.exchange
