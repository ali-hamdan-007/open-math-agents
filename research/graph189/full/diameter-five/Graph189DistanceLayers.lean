import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Graph189LowDegreeTwo
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem two_edges {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hne : a ≠ c) (hn : ¬ G.Adj a c) : G.dist a c = 2 := by
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  have hp : G.dist a c ≤ 2 := by simpa [p] using G.dist_le p
  have hpos : 0 < G.dist a c := Nat.pos_of_ne_zero
    (fun h => hne (p.reachable.dist_eq_zero_iff.mp h))
  have hone : G.dist a c ≠ 1 := fun h => hn (dist_eq_one_iff_adj.mp h)
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem split_two (h : G.Connected) {a c : V} (hd : G.dist a c = 2) :
    ∃ b, G.Adj a b ∧ G.Adj b c := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a c
  rw [hd] at hp
  have h1 := p.adj_getVert_succ (i := 0) (by omega)
  have h2 := p.adj_getVert_succ (i := 1) (by omega)
  rw [Walk.getVert_zero] at h1
  rw [show 1+1 = p.length by omega, Walk.getVert_length] at h2
  exact ⟨p.getVert 1,h1,h2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem split_three (h : G.Connected) {a c : V} (hd : G.dist a c = 3) :
    ∃ b, G.dist a b = 2 ∧ G.Adj b c := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a c
  rw [hd] at hp
  let b := p.getVert 2
  have hstep := p.adj_getVert_succ (i := 2) (by omega)
  rw [show 2+1 = p.length by omega, Walk.getVert_length] at hstep
  have hle : G.dist a b ≤ 2 := (G.dist_le (p.take 2)).trans (by simp [Walk.take_length])
  have htri := h.dist_triangle (u := a) (v := b) (w := c)
  rw [hd,dist_eq_one_iff_adj.mpr hstep] at htri
  exact ⟨b,by omega,hstep⟩

end Graph189LowDegreeTwo
