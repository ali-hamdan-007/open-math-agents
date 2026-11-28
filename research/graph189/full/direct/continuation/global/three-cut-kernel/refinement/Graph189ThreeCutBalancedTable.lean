import Graph189ThreeCutThresholds

namespace Graph189ThreeCutBalancedTable
open Graph189ThreeCutThresholds

def windows : List Window := [
  ⟨29,134,42⟩, ⟨30,139,42⟩, ⟨31,144,43⟩, ⟨32,149,44⟩,
  ⟨33,154,44⟩, ⟨34,159,45⟩, ⟨35,164,46⟩, ⟨36,169,47⟩, ⟨37,174,47⟩]

private def row (w : Window) (x : ℕ) : Bool :=
  let y := max x (w.n-4-x)
  let q := if 2*w.k+1<x then w.k-2 else w.k
  decide (x*(y+3)≤w.k*x+3*q*(w.k+1) → x≤w.cap)

private def valid (w : Window) : Bool :=
  (List.range (3*w.k+1)).all (row w) &&
    decide (4*w.k+4<w.n ∧ w.cap+1<2*w.k ∧
      3*w.k+w.cap+4<w.n ∧ 12*w.k+w.cap<3*w.n ∧
      6*w.k+3*(w.k-2)+8<2*w.n)

private theorem checked : windows.all valid=true := by decide

def Certified (k n : ℕ) : Prop := ∃ w∈windows,w.k=k ∧ w.n≤n

theorem order_room {k n : ℕ} (region : Certified k n) : 4*k+4<n := by
  obtain ⟨w,hw,rfl,order⟩ := region
  have v := List.all_eq_true.mp checked w hw
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at v
  exact v.2.1.trans_le order

theorem degree {k n : ℕ} (region : Certified k n) : 29≤k := by
  obtain ⟨w,hw,rfl,_⟩ := region
  have all : windows.all (fun p => decide (29≤p.k))=true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp all w hw)

/-- The two cross-product estimates reduce all populations throughout
the finite windows to the private-density or common-label alternatives. -/
theorem quotas {x y k n : ℕ} (region : Certified k n) (orient : x≤y)
    (total : n≤x+y+4)
    (base : x*(y+3)≤k*x+3*k*(k+1))
    (balanced : 2*k+1<x → x*(y+3)≤k*x+3*(k-2)*(k+1)) :
    4*k+4<n ∧ 3*k<y ∧ x+1<2*k ∧ 12*k<2*x+3*y+12 ∧
      (x≤k-2 → 6*k+x<2*y) := by
  obtain ⟨w,hw,rfl,order⟩ := region
  have validW := List.all_eq_true.mp checked w hw
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at validW
  obtain ⟨each,room,dense,big,privateBound,common⟩ := validW
  have bounded : x≤3*w.k := by
    by_contra! high
    have a := Nat.mul_le_mul_left x (show 3*w.k+1≤y by omega)
    have b := Nat.mul_le_mul_left w.k (show 3*w.k+1≤x by omega)
    nlinarith only [a,b,base,high,Nat.zero_le (w.k*w.k)]
  have checkedX := List.all_eq_true.mp each x (List.mem_range.mpr (by omega))
  simp only [row,decide_eq_true_eq] at checkedX
  have small : x≤w.cap := by
    apply checkedX
    have y0 : max x (w.n-4-x)≤y := max_le orient (by omega)
    have mult := Nat.mul_le_mul_left x (Nat.add_le_add_right y0 3)
    by_cases regime : 2*w.k+1<x
    · simpa [regime] using mult.trans (balanced regime)
    · simpa [regime] using mult.trans base
  omega

#print axioms quotas
end Graph189ThreeCutBalancedTable
