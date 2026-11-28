import Graph189ThreeCutThresholds

namespace Graph189ThreeNearArithmetic

private theorem row_bound {k a b u v m t : ℕ}
    (aCap : a+t≤m) (bCap : b≤m) (budget : u+v≤k) :
    a*v+b*u+t*v≤k*m := by
  have debit := Nat.mul_le_mul_right v aCap
  have second := Nat.mul_le_mul_right u bCap
  have layers := Nat.mul_le_mul_right m budget
  nlinarith only [debit,second,layers]

/-- A 33-by-72 row of the k=24 three-cut certificate. In decreasing
opposite-column order, the three graph-side hypotheses express the
required number of opposite second-layer entries and the exceptional
contact sum bound when both near labels have degree one. -/
theorem impossible {g : ℕ} (sizes : g=20 ∨ g=22)
    {a1 a2 a3 b1 b2 b3 u1 u2 u3 v1 v2 v3 : ℕ}
    (aFirst : a1≤g) (aSecond : a2≤g) (aThird : a3≤g)
    (bFirst : b1≤(g+1)) (ordered : b3≤b2 ∧ b2≤b1)
    (budget1 : u1+v1≤(g+2)) (budget2 : u2+v2≤(g+2)) (budget3 : u3+v3≤(g+2))
    (charge : ((3*g/2)*(2*(g+2)+3))≤a1+a2+a3+(a1*v1+b1*u1)+(a2*v2+b2*u2)+(a3*v3+b3*u3))
    (near : b1=(g+1) → (g+3)≤v1+v2+v3)
    (allNear : b3=(g+1) → (2*g+3)≤v1+v2+v3)
    (twoNear : b2=(g+1) → b3<(g+1) → a3=g →
      (2*g+3)≤v1+v2+v3 ∨ a1+a2+a3≤(2*g)) : False := by
  have bSecond : b2≤(g+1) := by omega
  have bThird : b3≤(g+1) := by omega
  by_cases two : b2=(g+1)
  · have one : b1=(g+1) := by omega
    have h1 := row_bound (m:=(g+1)) (t:=1) (by omega : a1+1≤(g+1)) bFirst budget1
    have h2 := row_bound (m:=(g+1)) (t:=1) (by omega : a2+1≤(g+1)) bSecond budget2
    by_cases three : b3=(g+1)
    · have h3 := row_bound (m:=(g+1)) (t:=1) (by omega : a3+1≤(g+1)) bThird budget3
      have count := allNear three
      rcases sizes with rfl|rfl <;> omega
    · have small : b3≤g := by omega
      by_cases lastFull : a3=g
      · have h3 := row_bound (m:=g) (t:=0) (by omega : a3+0≤g) small budget3
        rcases twoNear two (by omega) lastFull with count|light <;> rcases sizes with rfl|rfl <;> omega
      · have h3 := row_bound (m:=g) (t:=1) (by omega : a3+1≤g) small budget3
        have count := near one
        rcases sizes with rfl|rfl <;> omega
  · have h1 := row_bound (m:=(g+1)) (t:=0) (by omega : a1+0≤(g+1)) bFirst budget1
    have h2 := row_bound (m:=g) (t:=0) (by omega : a2+0≤g) (by omega : b2≤g) budget2
    have h3 := row_bound (m:=g) (t:=0) (by omega : a3+0≤g) (by omega : b3≤g) budget3
    rcases sizes with rfl|rfl <;> omega

#print axioms impossible
end Graph189ThreeNearArithmetic
