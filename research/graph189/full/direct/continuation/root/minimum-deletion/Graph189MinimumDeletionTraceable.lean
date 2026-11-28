import Graph189StrictMinimumDeletion
import Graph189ThirdFinite
import Graph189ActualScalarWidth

open SimpleGraph Finset

namespace Graph189RootedSplice

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At second-smallest degree at least nineteen, a Hamiltonian minimum
deletion gives an actual Hamiltonian path if the minimum degree is at least
three, for every graph order and connectivity. -/
theorem traceable_of_hamiltonian_minimum_deletion (connected : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (degree : 19≤G.secondSmallestDegree) (z : V) (least : G.degree z=G.minDegree)
    (three : 3≤G.degree z)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b) (hr : r.IsHamiltonian) :
    ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let l := (k+2)/3
  change 19≤k at degree
  have point (w : V) : G.distEven w≤k+1 := by
    simpa only [k,Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ w))).trans cap
  by_cases small : 3*G.degree z<k
  · exact traceable_of_small_degree_hamiltonian_deletion connected z least three small point r hr
  by_contra nontrace
  have ll : k≤3*l := by dsimp [l]; omega
  have lu : 3*l≤k+2 := by dsimp [l]; omega
  have lc : l≤G.degree z+1 := by dsimp [l]; omega
  have lower := order_of_hamiltonian_deletion_up_to_succ_degree connected z least three
    (by change 5≤k; omega) nontrace point r hr l lc
  have zord : ((l:ℤ)+1)*((k:ℤ)-l+2)-1≤n := by
    have b : (l+1)*(k-l+2)≤n+1 := by change (l+1)*(k-l+2)-1≤n at lower; omega
    have c : ((l:ℤ)+1)*((↑(k-l) : ℤ)+2)≤(n:ℤ)+1 := by exact_mod_cast b
    rw [Nat.cast_sub (by omega : l≤k)] at c
    omega
  have degreeZ : (19:ℤ)≤k := by exact_mod_cast degree
  have llZ : (k:ℤ)≤3*l := by exact_mod_cast ll
  have luZ : 3*(l:ℤ)≤k+2 := by exact_mod_cast lu
  have strong := Graph189ThirdWidth.room_at_third degreeZ llZ luZ zord
  have order : 4*k+2≤n := by exact_mod_cast strong
  obtain ⟨e0,e2,_,lo,hi⟩ := Graph189ActualScalarWidth.bounds connected cap nontrace order
  exact Graph189ThirdWidth.impossible_at_third degreeZ llZ luZ zord e0 e2 lo hi

#print axioms traceable_of_hamiltonian_minimum_deletion

end Graph189RootedSplice
