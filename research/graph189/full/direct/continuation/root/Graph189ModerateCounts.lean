import Lean.Elab.Tactic.Omega

namespace Graph189ModerateCounts

/-- Exact two-component arithmetic. The optional omitted low vertex is
either in the smaller side or a singleton outside the two chosen sides.
At the largest admissible size of the larger side neither costs a vertex. -/
theorem two_sides {s k n a b extra : Nat}
    (hs : 2≤s) (hk : 3*s+3≤k) (hh : 6*s≤k+5)
    (all : n=s+a+b+extra) (order : n≤3*k+2) (left : k-s+1≤a) (ab : a≤b) :
    a≤2*(k-s)-1 ∧ b≤2*k+1 ∧
    (b=2*k+1 → a=k-s+1 ∧ extra=0) ∧
    (b=2*k+1 → s-1+(b-(2*(k-s)+1))≤(k+1)/2+1) ∧
    (b≤2*k → s+(b-(2*(k-s)+1))≤(k+1)/2+1) := by
  omega

/-- Three high-containing components force the degree thresholds for a
Hamilton-connected middle and Hamiltonian high cores at the ends. A fourth
high-containing component cannot fit below the moderate upper order. -/
theorem component_sizes {s k n m : Nat} (hk : 3*s+3≤k) (order : n≤3*k+2)
    (three : s+m+2*(k-s+1)≤n) :
    m≤k+s ∧ m+1≤2*(k-s-1) ∧ n<s+4*(k-s+1) := by
  omega

#print axioms two_sides
#print axioms component_sizes
end Graph189ModerateCounts
