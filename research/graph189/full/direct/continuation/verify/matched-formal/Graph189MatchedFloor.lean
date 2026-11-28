import Graph189MatchedRootWidth
import Graph189MatchedRooted
import Graph189MaximumDegree

open SimpleGraph Finset
namespace Graph189MatchedFloor

private theorem mono {b n k d : ℕ} (hn : b≤n) :
    Graph189MatchedRootWidth.width b k d ≤ Graph189MatchedRootWidth.width n k d := by
  apply Graph189MatchedRootWidth.width_le_admissible
  obtain ⟨linear,h⟩ := Graph189MatchedRootWidth.width_admissible n k d
  refine ⟨le_trans ?_ linear,?_⟩
  · unfold Graph189RootWidth.width
    exact Nat.div_le_div_right (by omega)
  rcases h with h|⟨enough,h⟩
  · exact Or.inl h
  exact Or.inr ⟨enough,by omega⟩

/-- A decidable necessary condition at an arbitrary lower bound on the graph order. -/
def Fits (b k e : ℕ) : Prop :=
  let d := k+e
  let w := Graph189MatchedRootWidth.width b k d
  let L := b-d-k-2
  w*L≤k*d ∧ (w-k)*L≤k*k ∧
    ((b:ℤ)≤3*(k:ℤ)+1+((k:ℤ)-2)*e) ∧
    (2*e+1≤k → (b:ℤ)≤3*(k:ℤ)+1+Graph189MatchedPack.score k e)
instance (b k e : ℕ) : Decidable (Fits b k e) := by unfold Fits; infer_instance

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem necessary (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (bad : ¬∃ a b,∃p : G.Walk a b,p.IsHamiltonian)
    {b : ℕ} (floor : b≤Fintype.card V) (hk : 3≤G.secondSmallestDegree) :
    Fits b G.secondSmallestDegree (G.maxDegree-G.secondSmallestDegree) := by
  let k := G.secondSmallestDegree
  let d := G.maxDegree
  let n := Fintype.card V
  let e := d-k
  have min : k≤d := by
    obtain ⟨a,v,ne⟩ := exists_pair_ne V
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a v ne with h|h
    · exact h.trans (G.degree_le_maxDegree a)
    · exact h.trans (G.degree_le_maxDegree v)
  have de : k+e=d := by dsimp [e]; omega
  have w := mono (k:=k) (d:=d) floor
  have l : b-d-k-2≤n-d-k-2 := by dsimp [n]; omega
  have bounds := Graph189MatchedRootWidth.root_matched_width_bounds hc cap
  change Graph189MatchedRootWidth.width n k d*(n-d-k-2)≤k*d ∧
    (Graph189MatchedRootWidth.width n k d-k)*(n-d-k-2)≤k*k at bounds
  change Fits b k e
  unfold Fits
  rw [de]
  refine ⟨(Nat.mul_le_mul w l).trans bounds.1,
    (Nat.mul_le_mul (Nat.sub_le_sub_right w k) l).trans bounds.2,?_,?_⟩
  · by_contra! h
    obtain ⟨x,_,y,p,hp⟩ := Graph189MatchedRooted.of_linear_order hc cap hk
      (by change 3*(k:ℤ)+1+((k:ℤ)-2)*(e:ℤ)<(n:ℤ); dsimp only [n]; omega)
    exact bad ⟨x,y,p,hp⟩
  · intro small
    by_contra! h
    obtain ⟨x,_,y,p,hp⟩ := Graph189MatchedRooted.of_matched_order hc cap small
      (by change 3*(k:ℤ)+1+Graph189MatchedPack.score k e<(n:ℤ); dsimp only [n]; omega)
    exact bad ⟨x,y,p,hp⟩

end Graph189MatchedFloor
#print axioms Graph189MatchedFloor.necessary
