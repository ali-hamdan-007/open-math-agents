import Graph189FourCutSaturationTable

namespace Graph189FourDegreeTable
open Graph189FourCutSaturationTable

def maxDeg (k : ℕ) := if k=31 then 34 else 36
def rowCap (k : ℕ) := if k=31 then 970 else 1035

theorem single {k a b u v : ℕ} (lo : 31≤k) (hi : k≤32)
    (aMax : a+2≤k) (bMax : b+2≤k) (both : a+b≤maxDeg k) (room : u+v≤k) :
    a+(a*v+u*b)+(2*b+(if a+4≤k+1 then 2 else 1)*v)≤rowCap k := by
  let w : ℕ := if a+4≤k+1 then 2 else 1
  change a+(a*v+u*b)+(2*b+w*v)≤rowCap k
  have h : a*v+u*b+w*v≤k*max (a+w) b := by
    have one := Nat.mul_le_mul_right v (le_max_left (a+w) b)
    have two := Nat.mul_le_mul_left u (le_max_right (a+w) b)
    have three := Nat.mul_le_mul_right (max (a+w) b) room
    nlinarith only [one,two,three]
  have range : k=31 ∨ k=32 := by omega
  rcases range with rfl|rfl <;> norm_num [maxDeg,rowCap] at both ⊢ <;>
    dsimp only [w] at * <;> split_ifs at * <;> omega

def Necessary (k x y : ℕ) := maxDeg k+2<x → x*(y+4)+2*y≤k*x+4*rowCap k
instance (k x y : ℕ) : Decidable (Necessary k x y) := by unfold Necessary; infer_instance

private def floor (k x : ℕ) := max x (6*k-24-x)
private def row (k x : ℕ) : Bool :=
  (List.range (4*k+x/2+1-floor k x)).all fun j =>
    let y := floor k x+j
    decide (x*(y+4)≤k*x+4*k*(k+1) → (k<x → Charge k x y) → Necessary k x y → Good k x y)
private def valid (k : ℕ) := (List.range (4*k+1)).all (row k)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem table : valid 31=true ∧ valid 32=true := by decide

theorem quotas {k x y : ℕ} (lo : 31≤k) (hi : k≤32) (xy : x≤y)
    (order : 6*k≤x+y+24) (base : x*(y+4)≤k*x+4*k*(k+1))
    (charge : k<x → Charge k x y) (extra : Necessary k x y) : Good k x y := by
  have bound : x≤4*k := by
    by_contra! high
    have a := Nat.mul_le_mul_left x (show 4*k+1≤y by omega)
    have b := Nat.mul_le_mul_left k (show 4*k+1≤x by omega)
    nlinarith only [a,b,base,high,Nat.zero_le (k*k)]
  by_cases large : 4*k+x/2<y
  · unfold Good
    omega
  have h : valid k=true := by rcases (show k=31 ∨ k=32 by omega) with rfl|rfl; exact table.1; exact table.2
  have hx := List.all_eq_true.mp h x (List.mem_range.mpr (by omega))
  have start : floor k x≤y := max_le xy (by omega)
  have iy : y-floor k x<4*k+x/2+1-floor k x := by omega
  have hy := List.all_eq_true.mp hx (y-floor k x) (List.mem_range.mpr iy)
  have e : floor k x+(y-floor k x)=y := by omega
  simp only [e,decide_eq_true_eq] at hy
  exact hy base charge extra

#print axioms quotas
end Graph189FourDegreeTable
