import Graph189ThreeConnectivity
import Graph189ThreeCutSaturationFacts

open SimpleGraph Finset OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ThreeConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem traceable_ge25 (connected : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (degree : 25≤G.secondSmallestDegree) (three : G.vertexConnectivity=3) :
    ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
  by_cases prev : 33≤G.secondSmallestDegree
  · exact Graph189ThreeConnectivity.traceable_ge33 connected cap prev three
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have least : G.degree z=G.minDegree := hz.symm
  obtain ⟨u,ne⟩ := exists_ne z
  have size : G.secondSmallestDegree<Fintype.card V := by
    rcases degree_pair (G:=G) u z ne with h|h
    · exact lt_of_le_of_lt h (G.degree_lt_card_verts u)
    · exact lt_of_le_of_lt h (G.degree_lt_card_verts z)
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  by_contra fail
  by_cases near : ∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := near
    have delta := Graph189RootedSplice.connectivity_le_degree (G:=G) z
    exact fail (Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion connected cap
      (by omega) z least (by omega) p hp)
  · have lower := Graph189LowConnectivityLift.minimum_deletion connected z least
      (by omega) (by omega) (by omega) (Or.inl three) point (by omega) fail near
    rw [three] at lower
    apply Graph189ThreeCut.excludes_from_quotas connected cap three (by omega)
    intro A B S cut sm orient
    let k := G.secondSmallestDegree
    let X := A.filter (fun a => k≤G.degree a)
    let Y := B.filter (fun b => k≤G.degree b)
    have sz := sm.trans three
    have bound := Graph189ThreeCutSaturationFacts.quotas connected cut sm sz
      (fun v => by have h := point v; omega) degree (by omega) (by omega) orient
    change Graph189ThreeCutSaturationTable.Good k X.card Y.card at bound
    obtain ⟨big,privateBound,last⟩ := bound
    have one : (A \ X).card≤1 := by
      apply card_le_one.mpr
      intro x hx y hy
      by_contra ne
      rcases degree_pair (G:=G) x y ne with h|h
      · exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,h⟩)
      · exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨(mem_sdiff.mp hy).1,h⟩)
    have allCard := card_sdiff_add_card_eq_card (show X⊆A from filter_subset _ _)
    change 3*(k:ℤ)<Y.card ∧ (9*(k:ℤ)-15+X.card<3*(Y.card:ℤ) ∨
      ((A.card:ℤ)<2*k ∧ 12*(k:ℤ)<2*X.card+3*Y.card+12)) ∧
      ∀i∈S,(∀a∈A,k≤G.degree a → G.Adj a i) → 6*(k:ℤ)+X.card<2*(Y.card:ℤ)
    refine ⟨by omega,?_,?_⟩
    · rcases privateBound with loose|⟨dense,strict⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega,by omega⟩
    · intro i si common
      have smaller (T : Finset V) (lt : T.card<S.card) :=
        Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq sm)
      have lowerDegree : 25≤k := degree
      have limited := Graph189CutColumnCaps.common_below_threshold connected cut smaller point
        (X:=X) (Y:=Y) (filter_subset _ _) (filter_subset _ _) (t:=1) (by omega) (by omega) si
        (fun a ha => common a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
      have residual := last (by omega)
      omega

#print axioms traceable_ge25
end Graph189ThreeConnectivity
