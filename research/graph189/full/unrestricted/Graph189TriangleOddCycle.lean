module
public import Graph189TriangleTransversalPublic

public section
namespace Graph189TriangleTransversal

open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An indexed odd cycle entirely outside a triangle transversal cannot have at most
one index of degree below k. The distinguished index can occupy any position. -/
theorem no_odd_cycle_one_low (X : Finset V) {k : ℕ} (ht : MeetsEveryTriangle G X)
    (cap : ∀ a, (Finset.univ.filter (fun u => G.dist a u = 2)).card ≤ k)
    (hk : 3 * X.card + 3 ≤ k) (p : ℕ → V) {m : ℕ} (hm : 0 < m)
    {q : ℕ} (hq : q ≤ 2*m) (outside : ∀ i ≤ 2*m, p i ∉ X)
    (high : ∀ i ≤ 2*m, i ≠ q → k ≤ G.degree (p i))
    (edges : ∀ i < 2*m, G.Adj (p i) (p (i+1))) : ¬G.Adj (p (2*m)) (p 0) := by
  intro closes
  let s := if q = 0 then 2*m else q-1
  have hs : s ≤ 2*m := by dsimp [s]; split <;> omega
  let idx := fun i : ℕ => if s+i ≤ 2*m then s+i else s+i-(2*m+1)
  have bound (i : ℕ) (hi : i ≤ 2*m) : idx i ≤ 2*m := by dsimp [idx]; split <;> omega
  have tall (j : ℕ) (hj : j ≤ m) : k ≤ G.degree (p (idx (2*j))) := by
    apply high _ (bound _ (by omega))
    dsimp [idx, s]
    split <;> split <;> omega
  have consecutive (i : ℕ) (hi : i < 2*m) : G.Adj (p (idx i)) (p (idx (i+1))) := by
    by_cases hbefore : s+i < 2*m
    · simpa [idx, show s+i ≤ 2*m by omega, show s+(i+1) ≤ 2*m by omega, Nat.add_assoc] using edges (s+i) hbefore
    · by_cases hat : s+i = 2*m
      · simpa [idx, hat, show ¬s+(i+1) ≤ 2*m by omega, show s+(i+1)-(2*m+1) = 0 by omega] using closes
      · have h₁ : ¬s+i ≤ 2*m := by omega
        have h₂ : ¬s+(i+1) ≤ 2*m := by omega
        have step : s+(i+1)-(2*m+1) = (s+i-(2*m+1))+1 := by omega
        simpa [idx, h₁, h₂, step] using edges (s+i-(2*m+1)) (by omega)
  have blocked := no_closing_edge G X ht cap hk (fun i => p (idx i)) hm
    (fun i hi => outside _ (bound i hi)) tall consecutive
  apply blocked
  by_cases hz : s = 0
  · simpa [idx, hz] using closes.symm
  · have last : s+2*m-(2*m+1) = s-1 := by omega
    have step : s-1+1=s := by omega
    have hh := (edges (s-1) (by omega)).symm
    rw [step] at hh
    simpa [idx, hs, show ¬ s+2*m ≤ 2*m by omega, last] using hh

end Graph189TriangleTransversal
