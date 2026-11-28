import Graph189ThreeLowMinimum
import Graph189ParentFocused

open SimpleGraph Finset
namespace Graph189ThreeOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every registered graph whose second-smallest degree is three has a
Hamiltonian path, including the exceptional degree-two case. -/
theorem traceable_three (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (hk : G.secondSmallestDegree = 3) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  have localCap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V ≤ 2*G.secondSmallestDegree + 2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc localCap short
  by_cases uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected
  · have minimum := Graph189CutBounds.two_le_degree hc localCap (by omega)
    have pair (u v : V) (ne : u ≠ v) : 3 ≤ G.degree u ∨ 3 ≤ G.degree v := by
      rw [←hk]
      exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair u v ne
    have upper := Graph189OrderBound.order_le hc cap
    rw [hk] at upper
    have smallDegree : G.minDegree ≤ 3 := by
      let ds := G.degreeSequence
      have len : 1 < ds.length := by simpa [ds,degreeSequence] using Fintype.one_lt_card (α := V)
      have mem : G.secondSmallestDegree ∈ ds := by
        change ds.getD 1 0 ∈ ds
        cases e : ds with
        | nil => simp [e] at len
        | cons a t =>
          cases f : t with
          | nil => simp [e,f] at len
          | cons b r => simp
      have hm : G.secondSmallestDegree ∈ univ.val.map (fun v : V => G.degree v) := by
        simpa [ds,degreeSequence] using mem
      obtain ⟨z,_,hz⟩ := Multiset.mem_map.mp hm
      have := G.minDegree_le_degree z
      omega
    by_cases tie : G.minDegree = 3
    · exact Graph189ThreeRegularMinimum.traceable_tied_three hc uncut cap tie hk
    apply Graph189ThreeLowMinimum.traceable_ten hc uncut minimum pair _ (by norm_num at upper; omega)
    exact Graph189ThreeRegularMinimum.exact_two_quota cap hk
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc localCap (by omega) uncut

#print axioms traceable_three
end Graph189ThreeOriginal
