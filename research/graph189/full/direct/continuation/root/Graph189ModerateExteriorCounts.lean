import Lean.Elab.Tactic.Omega

namespace Graph189ModerateExteriorCounts

/-- For a long cycle, two disjoint links give either an immediate contradiction
or equality in every vertex count. Equality is impossible if adjacent vertices
on the exterior cycle have distinct direct contacts on the path. -/
theorem large_cycle {n k q outside : Nat} (degree : 9≤k) (large : k-2≤q)
    (moderate : n≤3*k+2) (twoLinks : 3*q+(q+1)/2+4+outside≤n) :
    q=k-2 ∧ outside=0 ∧ n=3*k+2 ∧ n<4*q+3 := by
  omega

/-- Four matched contacts suffice throughout the shorter block range.
In a five-vertex leaf all nonarticulation vertices attain full block degree.
At the one remaining size three matched contacts suffice. -/
theorem short_block {n k m : Nat} (degree : 9≤k) (moderate : n≤3*k+2)
    (size : (k+1)/2≤m) (small : m≤k-3) :
    (m≤k-4 ∧ 4≤k-m ∧ (m=5 ∨ 4≤m-2) ∧ n<6*m+5) ∨
    (m=k-3 ∧ 3≤k-m ∧ 3≤m-2 ∧ n<5*m+4) := by
  omega

#print axioms large_cycle
#print axioms short_block
end Graph189ModerateExteriorCounts
