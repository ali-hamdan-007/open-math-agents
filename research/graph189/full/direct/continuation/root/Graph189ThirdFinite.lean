import Graph189ThirdWidth

namespace Graph189ThirdWidth

private def F (k m e : ℤ) : ℤ :=
  (m-2*k-e-2)*(2*(m-2*k)+k*e)-k*(k+1)*(k+e)

/-- A lower bound already fails the two endpoint tests for the concave
quadratic in e, so it cannot be the order of a qualifying graph. -/
private theorem of_endpoints {k m n e w : ℤ} (degree : 0≤k)
    (room : 4*k+2≤m) (order : m≤n) (left : 0<F k m 0) (right : 0<F k m (2*k))
    (e0 : 0≤e) (e2 : e≤2*k)
    (lower : 2*(n-2*k)+k*e≤(k+1)*w)
    (upper : w*(n-2*k-e-2)≤k*(k+e)) : False := by
  have ka := mul_nonneg degree e0
  have first : 0≤n-2*k-e-2 := by omega
  have W1 := mul_le_mul_of_nonneg_right lower first
  have W2 := mul_le_mul_of_nonneg_left upper (show 0≤k+1 by omega)
  have lo : 0≤2*(m-2*k)+k*e := by omega
  have transfer := mul_le_mul (show m-2*k-e-2≤n-2*k-e-2 by omega)
    (show 2*(m-2*k)+k*e≤2*(n-2*k)+k*e by omega) lo first
  have val : F k m e≤0 := by unfold F; nlinarith only [W1,W2,transfer]
  let A := (k-2)*m-5*k*k+k
  have curve := mul_nonneg ka (sub_nonneg.mpr e2)
  unfold F at left right val
  by_cases slope : 0≤A
  · have rise := mul_nonneg e0 slope
    dsimp [A] at rise
    nlinarith only [rise,curve,left,val]
  · have fall := mul_nonneg (sub_nonneg.mpr e2) (show 0≤-A by omega)
    dsimp [A] at fall
    nlinarith only [fall,curve,right,val]

private theorem endpoint_values {k l : ℤ} (k0 : 19≤k) (k1 : k≤25)
    (l0 : k≤3*l) (l1 : 3*l≤k+2) :
    let m := (l+1)*(k-l+2)-1
    4*k+2≤m ∧ 0<F k m 0 ∧ 0<F k m (2*k) := by
  have cases : (k=19 ∧ l=7) ∨ (k=20 ∧ l=7) ∨ (k=21 ∧ l=7) ∨ (k=22 ∧ l=8) ∨
      (k=23 ∧ l=8) ∨ (k=24 ∧ l=8) ∨ (k=25 ∧ l=9) := by omega
  rcases cases with h|h|h|h|h|h|h <;> obtain ⟨rfl,rfl⟩ := h <;> decide

theorem room_at_third {k l n : ℤ} (degree : 19≤k) (ll : k≤3*l) (lu : 3*l≤k+2)
    (order : (l+1)*(k-l+2)-1≤n) : 4*k+2≤n := by
  by_cases big : 26≤k
  · have quad := quadratic big ll lu order
    nlinarith only [mul_nonneg (show 0≤k by omega) (show 0≤k-25 by omega),quad,big]
  · exact (endpoint_values degree (by omega) ll lu).1.trans order

theorem impossible_at_third {k l n e w : ℤ} (degree : 19≤k) (ll : k≤3*l) (lu : 3*l≤k+2)
    (order : (l+1)*(k-l+2)-1≤n) (e0 : 0≤e) (e2 : e≤2*k)
    (lower : 2*(n-2*k)+k*e≤(k+1)*w)
    (upper : w*(n-2*k-e-2)≤k*(k+e)) : False := by
  by_cases big : 26≤k
  · exact incompatible big (quadratic big ll lu order) e0 e2 lower upper
  · obtain ⟨room,left,right⟩ := endpoint_values degree (by omega) ll lu
    exact of_endpoints (by omega) room order left right e0 e2 lower upper

#print axioms impossible_at_third
end Graph189ThirdWidth
