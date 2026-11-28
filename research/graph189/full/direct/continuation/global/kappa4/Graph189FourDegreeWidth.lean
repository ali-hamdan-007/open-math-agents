import Graph189FourDegreeTable
import Graph189ActualScalarWidth
import Graph189ThirdLayerDegreeCeiling

open SimpleGraph Finset Graph189FourDegreeTable
namespace Graph189FourDegreeWidth

private theorem narrow {k n e w : ℤ} (lo : 31≤k) (hi : k≤32) (floor : 6*k-19≤n)
    (ep : 0≤e) (em : e+3≤2*k) (width : 2*(n-2*k)+k*e≤(k+1)*w)
    (budget : w*(n-2*k-e-2)≤k*(k+e)) :
    (k=31 → e≤3) ∧ (k=32 → e≤4) := by
  have wp : 0≤w := by
    by_contra! neg
    have := mul_neg_of_pos_of_neg (by omega : 0<k+1) neg
    have := mul_nonneg (by omega : 0≤k) ep
    omega
  let b := 6*k-19
  have reduced := (mul_le_mul_of_nonneg_left (by dsimp [b]; omega : b-2*k-e-2≤n-2*k-e-2) wp).trans budget
  have witness : 2*(b-2*k)+k*e≤(k+1)*w := by dsimp [b]; omega
  dsimp [b] at reduced witness
  have top : e≤61 := by omega
  clear width budget floor b n
  interval_cases k <;> norm_num at em reduced witness ⊢ <;> interval_cases e <;> omega

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem max_degree (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (bad : ¬∃ a b,∃ p : G.Walk a b,p.IsHamiltonian) (lo : 31≤G.secondSmallestDegree)
    (hi : G.secondSmallestDegree≤32) (floor : 6*G.secondSmallestDegree≤Fintype.card V+19) :
    G.maxDegree≤maxDeg G.secondSmallestDegree := by
  obtain ⟨ep,_,_,width,budget⟩ := Graph189ActualScalarWidth.bounds hc cap bad (by omega)
  have ceil := Graph189ThirdLayerDegreeCeiling.max_degree hc cap (by omega)
  have h := narrow (k:=(G.secondSmallestDegree:ℤ)) (n:=(Fintype.card V:ℤ))
    (by exact_mod_cast lo) (by exact_mod_cast hi) (by omega) ep
    (by change ((G.maxDegree-G.secondSmallestDegree : ℕ):ℤ)+3≤2*(G.secondSmallestDegree:ℤ); omega)
    width budget
  unfold maxDeg
  split <;> omega

#print axioms max_degree
end Graph189FourDegreeWidth
