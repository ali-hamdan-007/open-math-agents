import Graph189LayerCutoff

namespace Graph189ProtectedRigidity

/-- In the low-degree equality case, the order cap at the low root forces
exactly its degree many distinct prescribed contacts in a tight matching. -/
theorem saturated {k n s m u : ℕ} (positive : 3 ≤ s) (ratio : 3*s < k)
    (sum : m+u=k+1) (su : s ≤ u) (um : u ≤ m)
    (lower : (u+1)*m+u ≤ n) (upper : n ≤ 1+s+k+s*(k+1-s)) :
    u=s ∧ m=k+1-s ∧ s<m ∧ n < (s+2)*m+(s+1) := by
  have sk : s ≤ k+1 := by omega
  have value : u=s := by
    by_contra! ne
    have su1 : s+1 ≤ u := by omega
    have sm1 : s+1 ≤ m := by omega
    zify [sk] at lower upper sum ⊢
    have am : 0 ≤ (m:ℤ)-s-1 := by omega
    have au : 0 ≤ (u:ℤ)-s-1 := by omega
    have times := congrArg (fun a : ℤ => (s:ℤ)*a) sum
    nlinarith only [mul_nonneg am au, lower, upper, sum, times, (show 3*(s:ℤ)<k by omega)]
  subst u
  have measure : m = k+1-s := by omega
  refine ⟨rfl,measure,by omega,?_⟩
  rw [←measure] at upper
  nlinarith only [upper,sum,(show s<m by omega)]

#print axioms saturated
end Graph189ProtectedRigidity
