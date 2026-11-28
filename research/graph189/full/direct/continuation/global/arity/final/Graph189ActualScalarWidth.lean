import Graph189RootWidth
import Graph189RootedTrace
import Graph189MaximumDegree

namespace Graph189ActualScalarWidth
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- All signed scalar width and degree inputs follow at the actual
maximum-degree root of the original nontraceable graph. -/
theorem bounds (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hn : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian)
    (har : 4*G.secondSmallestDegree+2≤Fintype.card V) :
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    let e : ℤ := (G.maxDegree-G.secondSmallestDegree : ℕ)
    let w : ℤ := Graph189RootWidth.width (Fintype.card V) G.secondSmallestDegree G.maxDegree
    0≤e ∧ e≤2*k ∧ n≤3*k+1+k*e ∧
      2*(n-2*k)+k*e≤(k+1)*w ∧ w*(n-2*k-e-2)≤k*(k+e) := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let Δ := G.maxDegree
  let e := Δ-k
  let w := Graph189RootWidth.width n k Δ
  let l := n-Δ-k-2
  have cap' (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have dmax : Δ≤3*k := Graph189DegreeCeiling.maxDegree_le_three_mul_secondSmallestDegree hc cap'
  have dmin : k≤Δ := by
    obtain ⟨a,b,ne⟩ := exists_pair_ne V
    rcases degree_pair (G:=G) a b ne with h|h
    · exact h.trans (G.degree_le_maxDegree a)
    · exact h.trans (G.degree_le_maxDegree b)
  have ore : n≤(3+e)*k+1 := by
    by_contra! h
    obtain ⟨z,_,v,path,hp⟩ := Graph189RootedTrace.of_order hc cap h
    exact hn ⟨z,v,path,hp⟩
  change 4*k+2≤n at har
  have de : k+e=Δ := by dsimp [e]; omega
  have dl : l+Δ+k+2=n := by dsimp [l]; omega
  have root := Graph189RootWidth.root_width_bound hc cap
  change w*l≤k*Δ at root
  let a := 2*n+k*Δ-(4*k+k*k)
  have hr := Nat.div_add_mod (a+k) (k+1)
  have hm := Nat.mod_lt (a+k) (by omega : 0<k+1)
  change (k+1)*w+(a+k)%(k+1)=a+k at hr
  have kh := Nat.mul_le_mul_left k dmin
  have big : 4*k+k*k≤2*n+k*Δ := by omega
  have round : 2*n+k*Δ≤(k+1)*w+4*k+k*k := by dsimp [a] at hr hm; omega
  rw [← de] at round root dl
  have roundZ : 2*(n:ℤ)+(k:ℤ)*(k+e)≤(k+1:ℤ)*w+4*(k:ℤ)+k*k := by exact_mod_cast round
  have rootZ : (w:ℤ)*l≤(k:ℤ)*(k+e) := by exact_mod_cast root
  have oreZ : (n:ℤ)≤(3+(e:ℤ))*(k:ℤ)+1 := by exact_mod_cast ore
  have lz : (l:ℤ)+(k+e:ℤ)+k+2=n := by exact_mod_cast dl
  have left : (n:ℤ)-2*k-e-2=l := by omega
  change 0≤(e:ℤ) ∧ (e:ℤ)≤2*k ∧ (n:ℤ)≤3*k+1+k*e ∧
    2*((n:ℤ)-2*k)+k*e≤(k+1:ℤ)*w ∧ (w:ℤ)*((n:ℤ)-2*k-e-2)≤k*(k+e)
  refine ⟨by positivity,?_,by nlinarith only [oreZ],by nlinarith only [roundZ],?_⟩
  · exact_mod_cast (show e≤2*k by omega)
  · rwa [left]

end Graph189ActualScalarWidth
#print axioms Graph189ActualScalarWidth.bounds
