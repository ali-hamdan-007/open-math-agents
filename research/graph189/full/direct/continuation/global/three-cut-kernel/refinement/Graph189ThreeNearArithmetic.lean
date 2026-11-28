import Graph189ThreeCutThresholds

namespace Graph189ThreeNearArithmetic

private theorem row_bound {a b u v m t : ℕ}
    (aCap : a+t≤m) (bCap : b≤m) (budget : u+v≤24) :
    a*v+b*u+t*v≤24*m := by
  have debit := Nat.mul_le_mul_right v aCap
  have second := Nat.mul_le_mul_right u bCap
  have layers := Nat.mul_le_mul_right m budget
  nlinarith only [debit,second,layers]

/-- A 33-by-72 row of the k=24 three-cut certificate. In decreasing
opposite-column order, the three graph-side hypotheses express the
required number of opposite second-layer entries and the exceptional
contact sum bound when both near labels have degree one. -/
theorem impossible
    {a1 a2 a3 b1 b2 b3 u1 u2 u3 v1 v2 v3 : ℕ}
    (aFirst : a1≤22) (aSecond : a2≤22) (aThird : a3≤22)
    (bFirst : b1≤23) (ordered : b3≤b2 ∧ b2≤b1)
    (budget1 : u1+v1≤24) (budget2 : u2+v2≤24) (budget3 : u3+v3≤24)
    (charge : 1683≤a1+a2+a3+(a1*v1+b1*u1)+(a2*v2+b2*u2)+(a3*v3+b3*u3))
    (near : b1=23 → 25≤v1+v2+v3)
    (allNear : b3=23 → 47≤v1+v2+v3)
    (twoNear : b2=23 → b3<23 → a3=22 →
      47≤v1+v2+v3 ∨ a1+a2+a3≤44) : False := by
  have bSecond : b2≤23 := by omega
  have bThird : b3≤23 := by omega
  by_cases two : b2=23
  · have one : b1=23 := by omega
    have h1 := row_bound (m:=23) (t:=1) (by omega : a1+1≤23) bFirst budget1
    have h2 := row_bound (m:=23) (t:=1) (by omega : a2+1≤23) bSecond budget2
    by_cases three : b3=23
    · have h3 := row_bound (m:=23) (t:=1) (by omega : a3+1≤23) bThird budget3
      have count := allNear three
      omega
    · have small : b3≤22 := by omega
      by_cases lastFull : a3=22
      · have h3 := row_bound (m:=22) (t:=0) (by omega : a3+0≤22) small budget3
        rcases twoNear two (by omega) lastFull with count|light <;> omega
      · have h3 := row_bound (m:=22) (t:=1) (by omega : a3+1≤22) small budget3
        have count := near one
        omega
  · have h1 := row_bound (m:=23) (t:=0) (by omega : a1+0≤23) bFirst budget1
    have h2 := row_bound (m:=22) (t:=0) (by omega : a2+0≤22) (by omega : b2≤22) budget2
    have h3 := row_bound (m:=22) (t:=0) (by omega : a3+0≤22) (by omega : b3≤22) budget3
    omega

#print axioms impossible
end Graph189ThreeNearArithmetic
