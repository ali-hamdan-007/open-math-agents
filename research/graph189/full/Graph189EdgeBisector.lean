import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Fintype.Card

/-! Exact parity balance at adjacent vertices. Owner: @ali-hamdan-007.
Agent: gpt-6.2-astra. -/

namespace Graph189EdgeBisector

open SimpleGraph Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def evenSet (p : V) : Finset V := by
  classical
  exact univ.filter (fun x => G.dist p x % 2 = 0)

noncomputable def ties (p q : V) (r : ℕ) : Finset V := by
  classical
  exact univ.filter (fun x => G.dist p x = G.dist q x ∧ G.dist p x % 2 = r)

/-- Vertices off the metric bisector of an edge contribute to exactly one
even-distance count. -/
theorem edge_balance {p q : V} (h : G.Connected) (hpq : G.Adj p q) :
    Fintype.card V + (ties G p q 0).card =
      (evenSet G p).card + (evenSet G q).card + (ties G p q 1).card := by
  classical
  have near (x : V) : G.dist p x ≤ G.dist q x + 1 ∧
      G.dist q x ≤ G.dist p x + 1 := by
    have ha := h.dist_triangle (u:=p) (v:=q) (w:=x)
    have hb := h.dist_triangle (u:=q) (v:=p) (w:=x)
    rw [dist_eq_one_iff_adj.mpr hpq] at ha
    rw [dist_eq_one_iff_adj.mpr hpq.symm] at hb
    omega
  have even_ties : evenSet G p ∩ evenSet G q = ties G p q 0 := by
    ext x
    have hx := near x
    simp [evenSet, ties]
    omega
  have odd_ties : (evenSet G p ∪ evenSet G q)ᶜ = ties G p q 1 := by
    ext x
    have hx := near x
    simp [evenSet, ties]
    omega
  have hi := Finset.card_union_add_card_inter (evenSet G p) (evenSet G q)
  have hu := Finset.card_add_card_compl (evenSet G p ∪ evenSet G q)
  rw [even_ties] at hi
  rw [odd_ties] at hu
  omega

theorem order_bound {p q : V} {k : ℕ} (h : G.Connected) (hpq : G.Adj p q)
    (hp : (evenSet G p).card ≤ k + 1) (hq : (evenSet G q).card ≤ k + 1) :
    Fintype.card V + (ties G p q 0).card ≤ 2*k+2+(ties G p q 1).card := by
  have he := edge_balance G h hpq
  omega

end Graph189EdgeBisector
