import Lean.Elab.Tactic.Omega

namespace Graph189ModerateBorder

/-- Two links leave at most one further exterior vertex in the two borderline degrees. -/
theorem long_cycle {n k q e : Nat} (hk : k=7 ∨ k=8) (moderate : n≤3*k+2)
    (long : k-2≤q) (count : 3*q+(q+1)/2+4+e≤n) :
    q=k-2 ∧ e≤1 ∧ n<4*q+4 ∧
    (4*q+3≤n → k=7 ∧ q=5 ∧ n=23) := by
  omega

/-- Every pair of marks realizing the length bound on the 17-vertex path
at degree seven uses exactly the same two positions. -/
theorem fixed_marks {i j : Nat} (left : 5≤i) (middle : i+6≤j)
    (right : j+6≤17) : i=5 ∧ j=11 := by omega

/-- A non-singleton exceptional small side at connectivity two can only
reach the upper boundary in the indicated two configurations. -/
theorem boundary_side {n k a b e : Nat} (hk : k=7 ∨ k=8) (moderate : n≤3*k+2)
    (order : n=2+a+b+e) (ab : a≤b) (large : 2*(k-2)≤a) :
    a=2*(k-2) ∧ b≤2*(k-2)+1 ∧ (k=8 → a=12 ∧ b=12 ∧ e=0) := by
  omega

#print axioms long_cycle
#print axioms fixed_marks
#print axioms boundary_side
end Graph189ModerateBorder
