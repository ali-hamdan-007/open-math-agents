import Graph189RotationMinOrder
import Graph189ActualScalarWidth
import Graph189ThirdLayerDegreeCeiling

open SimpleGraph Finset
namespace Graph189SevenIndexTraceable
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Rounding the width and applying the third-layer degree ceiling at the
least allowed order excludes both finite parameter ranges. -/
private theorem no_width {k l n e w : ℤ}
    (sector : (l=7 ∧ 15≤k ∧ k≤18) ∨ (l=6 ∧ 17≤k ∧ k≤18))
    (lower : (l+1)*(k-l+2)-1≤n) (room : 5*k+2<n) (ep : 0≤e) (em : e+3≤2*k)
    (width : 2*(n-2*k)+k*e≤(k+1)*w)
    (budget : w*(n-2*k-e-2)≤k*(k+e)) : False := by
  let b := (l+1)*(k-l+2)-1
  have kpos : 0<k := by rcases sector with h|h <;> omega
  have wp : 0≤w := by
    by_contra! neg
    have := mul_neg_of_pos_of_neg (by omega : 0<k+1) neg
    have := mul_nonneg kpos.le ep
    omega
  have cap := (mul_le_mul_of_nonneg_left
    (by dsimp [b]; omega : b-2*k-e-2≤n-2*k-e-2) wp).trans budget
  have wit : 2*(b-2*k)+k*e≤(k+1)*w := by dsimp [b]; omega
  dsimp [b] at cap wit
  clear width budget wp lower room b n
  have ehi : e≤2*k-3 := by omega
  rcases sector with ⟨rfl,lo,hi⟩ | ⟨rfl,lo,hi⟩ <;>
    interval_cases k <;> norm_num at ehi cap wit <;> interval_cases e <;> omega

/-- At second degree fifteen or sixteen, index seven suffices. At second
degree seventeen or eighteen, index six already forces a Hamiltonian path. -/
theorem traceable_sector (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree) {l : ℕ}
    (sector : (l=7 ∧ 15≤G.secondSmallestDegree ∧ G.secondSmallestDegree≤18) ∨
      (l=6 ∧ 17≤G.secondSmallestDegree ∧ G.secondSmallestDegree≤18))
    (conn : l≤G.vertexConnectivity) : ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  change (l=7 ∧ 15≤k ∧ k≤18) ∨ (l=6 ∧ 17≤k ∧ k≤18) at sector
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have lower := Graph189RotationLinked.base_order nontrace point (l:=l)
    (by rcases sector with h|h <;> omega) conn (by change 2*l+1≤k; rcases sector with h|h <;> omega)
  change (l+1)*(k-l+2)≤n+1 at lower
  have room : 5*k+2<n := by rcases sector with ⟨rfl,_,_⟩|⟨rfl,_,_⟩ <;> omega
  have deficit := Graph189ThirdLayerDegreeCeiling.max_degree hc cap room
  change G.maxDegree+3≤3*k at deficit
  have width := Graph189ActualScalarWidth.bounds hc cap nontrace (by change 4*k+2≤n; omega)
  have zsector : (((l:ℤ)=7 ∧ 15≤(k:ℤ) ∧ (k:ℤ)≤18) ∨ ((l:ℤ)=6 ∧ 17≤(k:ℤ) ∧ (k:ℤ)≤18)) := by
    rcases sector with ⟨rfl,_,_⟩|⟨rfl,_,_⟩
    · left; omega
    · right; omega
  have zn : ((l:ℤ)+1)*((k:ℤ)-l+2)-1≤(n:ℤ) := by
    rcases sector with ⟨rfl,_,_⟩|⟨rfl,_,_⟩ <;> norm_num <;> omega
  exact no_width zsector zn (by exact_mod_cast room) width.1
    (by change ((G.maxDegree-k : ℕ):ℤ)+3≤2*(k:ℤ); omega)
    width.2.2.2.1 width.2.2.2.2

theorem traceable_from_sixteen (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (lo : 16 ≤ G.secondSmallestDegree) (hi : G.secondSmallestDegree ≤ 18)
    (conn : 7 ≤ G.vertexConnectivity) : ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian :=
  traceable_sector hc cap (Or.inl ⟨rfl,by omega,hi⟩) conn

theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (lo : 17 ≤ G.secondSmallestDegree) (hi : G.secondSmallestDegree ≤ 18)
    (conn : 7 ≤ G.vertexConnectivity) : ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian :=
  traceable_sector hc cap (Or.inr ⟨rfl,lo,hi⟩) (by omega)

end Graph189SevenIndexTraceable
#print axioms Graph189SevenIndexTraceable.traceable_sector
