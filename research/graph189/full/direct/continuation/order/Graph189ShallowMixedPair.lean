import Graph189BalancedPair
import Graph189ShallowMixedCensus

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ShallowMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- A shallow side containing a common port and both private types,
opposite a common-free side, forces an original Hamiltonian path at k≥12. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 12≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (ne : p≠q) (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x)
    (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q)) (common : ∃x∈A,∀i∈S,G.Adj x i)
    (privateP : ∃x∈A,G.Adj x p ∧ ¬G.Adj x q) (privateQ : ∃x∈A,G.Adj x q ∧ ¬G.Adj x p) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have sz : S.card=2 := by simp [pair,ne]
  have conn : 2≤G.vertexConnectivity := by omega
  by_cases adj : G.Adj p q
  · exact Graph189AdjacentDeepPair.unrestricted hc cap sides sc pair adj (by omega)
  by_cases con : (G.induce (A:Set V)).Connected
  swap
  · obtain ⟨three⟩ := Graph189SeparatedSideComponents.three_of_disconnected_side sides con
    exact Graph189AnySingletonCut.of_three_components hc cap S sc (by omega) (by omega) (by omega) three
  by_cases big : 2*k≤B.card
  · have pop := census hc sides pair ne adj sc con point big shallow free common privateP privateQ
    apply Graph189OnePortCover.below_four hc cap conn (by omega)
    omega
  let R := A.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)
  have small : R.card≤1 := card_le_one.mpr (by
    intro x hx y hy
    by_contra diff
    have low {w : V} (hr : w∈R) (hi : k≤G.degree w) : False := by
      obtain ⟨wa,wp,wq⟩ := mem_filter.mp hr
      obtain ⟨i,si,iw⟩ := shallow w wa hi
      have d := dist_eq_one_iff_adj.mpr iw
      rcases (show i=p ∨ i=q by simpa [pair] using si) with eq|eq
      · exact wp (eq ▸ d)
      · exact wq (eq ▸ d)
    exact (degree_pair (G:=G) x y diff).elim (low hx) (low hy))
  obtain ⟨_,other⟩ := Graph189PrivateContactProfile.population hc sides.swap pair ne sc point free
  change A.card≤2*k-2+R.card at other
  apply Graph189BalancedPair.traceable hc cap large sides sc pair ne
  · change A.card+1≤2*k
    change 12≤k at large
    omega
  · change B.card+1≤2*k
    omega

#print axioms traceable
end Graph189ShallowMixedPair
