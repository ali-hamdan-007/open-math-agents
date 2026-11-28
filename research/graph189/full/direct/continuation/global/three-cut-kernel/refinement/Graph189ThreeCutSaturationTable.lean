import Graph189ThreeCutThresholds

namespace Graph189ThreeCutSaturationTable

/-- First-neighborhood size in the source side of a three-cut. -/
def level (k x y : ℕ) : ℕ :=
  if 2*k+1<y then k-2 else
  if 2*k<y ∨ (k<y ∧ 7*k<x+3*y) then k-1 else k

theorem level_order {k x y : ℕ} (xy : x≤y) : level k x y≤level k y x := by
  unfold level
  split_ifs <;> omega

def Charge (k x y : ℕ) : Prop :=
  let u := level k x y
  let v := level k y x
  x*y+3*x≤k*x+x+3*k*v ∨
    x*y+3*x+(v-u)*(y-k-v)≤k*x+3*u+3*k*v

def Good (k x y : ℕ) : Prop :=
  3*k<y ∧ (9*k+x<3*y+15 ∨ (x+1<2*k ∧ 12*k<2*x+3*y+12)) ∧
    (x≤k-2 → 6*k+x<2*y)

instance (k x y : ℕ) : Decidable (Charge k x y) := by unfold Charge; infer_instance
instance (k x y : ℕ) : Decidable (Good k x y) := by unfold Good; infer_instance

private def start (k x : ℕ) := max x (5*k-15-x)
private def row (k x : ℕ) : Bool :=
  (List.range (3*k+x/2+1-start k x)).all fun j =>
    let y := start k x+j
    decide ((k<x → Charge k x y) → Good k x y)
private def valid (k : ℕ) := (List.range (3*k+1)).all (row k)

/-- Every row starts at both the orientation and order floors. At the
upper endpoint all three terminal inequalities hold without charges. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem table : (List.range 12).all (fun i => valid (25+i))=true := by decide

theorem quotas {k x y : ℕ} (lo : 25≤k) (hi : k≤36) (xy : x≤y)
    (order : 5*k≤x+y+15) (base : x*(y+3)≤k*x+3*k*(k+1))
    (charge : k<x → Charge k x y) : Good k x y := by
  have bound : x≤3*k := by
    by_contra! high
    have a := Nat.mul_le_mul_left x (show 3*k+1≤y by omega)
    have b := Nat.mul_le_mul_left k (show 3*k+1≤x by omega)
    nlinarith only [a,b,base,high,Nat.zero_le (k*k)]
  by_cases large : 3*k+x/2<y
  · unfold Good
    omega
  have h := List.all_eq_true.mp table (k-25) (List.mem_range.mpr (by omega))
  rw [show 25+(k-25)=k by omega] at h
  have hx := List.all_eq_true.mp h x (List.mem_range.mpr (by omega))
  have floor : start k x≤y := max_le xy (by omega)
  have iy : y-start k x<3*k+x/2+1-start k x := by omega
  have hy := List.all_eq_true.mp hx (y-start k x) (List.mem_range.mpr iy)
  have e : start k x+(y-start k x)=y := by omega
  simp only [e,decide_eq_true_eq] at hy
  exact hy charge

#print axioms quotas
end Graph189ThreeCutSaturationTable
