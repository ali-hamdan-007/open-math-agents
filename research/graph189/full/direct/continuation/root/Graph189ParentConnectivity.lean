import Graph189DegreeTwoOriginal

open SimpleGraph Finset
namespace Graph189ParentConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The parent's connected-deletion formulation gives vertex connectivity
at least two at every order where a two-connected obligation is used. -/
theorem two_of_deletions (hc : G.Connected) (order : 3≤Fintype.card V)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected) : 2≤G.vertexConnectivity := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card=j ∧
    (¬(G.induce ((S : Set V)ᶜ)).Connected ∨ S.card=Fintype.card V-1)}
  have h : G.vertexConnectivity=sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬Fintype.card V≤1)]
  obtain ⟨z⟩ := hc.nonempty
  have ex : M.Nonempty := ⟨_,univ.erase z,rfl,Or.inr (by simp)⟩
  rw [h]
  obtain ⟨T,sz,bad|full⟩ := Nat.sInf_mem ex
  · by_contra! small
    apply bad
    change (G.induce {v : V | v∉T}).Connected
    by_cases empty : T=∅
    · subst T
      rw [show {v : V | v∉(∅ : Finset V)}=Set.univ by ext; simp]
      exact hc.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
    obtain ⟨v,rfl⟩ := card_eq_one.mp (show T.card=1 by
      have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
      omega)
    rw [show {w : V | w∉({v} : Finset V)}={w : V | w≠v} by ext; simp]
    exact deletion v
  · omega

/-- The first parent obligation at k≥12, retaining its original pointwise
even bound and the exact assumption on deletion of any one vertex. -/
theorem moderate (hc : G.Connected)
    (cap : ∀ x, G.distEven x ≤ 1+G.secondSmallestDegree)
    (order : 2*G.secondSmallestDegree+3 ≤ Fintype.card V)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected)
    (moderate : Fintype.card V ≤ 3*G.secondSmallestDegree+2) (large : 12≤G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have full : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree := by
    apply max'_le
    intro _ mem
    obtain ⟨v,_,rfl⟩ := mem_image.mp mem
    exact cap v
  exact Graph189DegreeTwoOriginal.traceable_moderate hc full large (two_of_deletions hc (by omega) deletion) moderate

#print axioms moderate
end Graph189ParentConnectivity
