import Graph189ConeLinkedOrder
import Graph189NearFinal
import Graph189ThirdFinite
import Graph189ActualScalarWidth

namespace Graph189ThirdConnectivity
open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- With connectivity at least one third of the second-smallest degree, both
minimum-deletion alternatives give the same lower order, contradicting width. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (hk : 19≤G.secondSmallestDegree) (high : G.secondSmallestDegree≤3*G.vertexConnectivity) :
    ∃ a b : V, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
  by_contra fail
  let k := G.secondSmallestDegree
  let l := (k+2)/3
  let n := Fintype.card V
  change 19≤k at hk
  change k≤3*G.vertexConnectivity at high
  have ll : k≤3*l := by dsimp [l]; omega
  have lu : 3*l≤k+2 := by dsimp [l]; omega
  have lc : l≤G.vertexConnectivity := by omega
  have point (w : V) : G.distEven w≤G.secondSmallestDegree+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ w))).trans cap
    omega
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have least : G.degree z=G.minDegree := hz.symm
  have order : (l+1)*(k-l+2)-1≤n := by
    by_cases near : ∃ a b, ∃ p : (G.induce {w : V | w≠z}).Walk a b,p.IsHamiltonian
    · obtain ⟨a,b,p,hp⟩ := near
      obtain ⟨x,y,q,hq,on,maximal⟩ := Graph189RootedSplice.exists_longest_containing G z
      have sd : G.vertexConnectivity≤G.degree z := Graph189RootedSplice.connectivity_le_degree z
      obtain ⟨du,_,bound⟩ := Graph189RootedSplice.rooted_matching_cone_order hc z least
        (by omega) (by change 5≤k; omega) fail point p hp q hq on maximal
      exact bound l (lc.trans (sd.trans du))
    · apply Graph189ConeLinkedOrder.order (completeAt G z) z (by omega : 2≤l) (by omega : l≤k)
        (secondDegree_le_completeAt_minDegree (G:=G) z least) (lc.trans (completeAt_connectivity z))
      intro a C hC longest
      exact Graph189CompletionLinked.minimum_fixed z least C hC longest fail near point
        (by omega : 3≤l) lu (by omega : 2*l+2≤k) (by omega : 6≤k)
  have zord : ((l:ℤ)+1)*((k:ℤ)-l+2)-1≤n := by
    have b : (l+1)*(k-l+2)≤n+1 := by omega
    have c : ((l:ℤ)+1)*((↑(k-l) : ℤ)+2)≤(n:ℤ)+1 := by exact_mod_cast b
    rw [Nat.cast_sub (by omega : l≤k)] at c
    omega
  have degree : (19:ℤ)≤k := by exact_mod_cast hk
  have llZ : (k:ℤ)≤3*l := by exact_mod_cast ll
  have luZ : 3*(l:ℤ)≤k+2 := by exact_mod_cast lu
  have strong := Graph189ThirdWidth.room_at_third degree llZ luZ zord
  have har : 4*k+2≤n := by exact_mod_cast strong
  obtain ⟨e0,e2,_,lo,hi⟩ := Graph189ActualScalarWidth.bounds hc cap fail har
  exact Graph189ThirdWidth.impossible_at_third degree llZ luZ zord e0 e2 lo hi

#print axioms traceable
end Graph189ThirdConnectivity
