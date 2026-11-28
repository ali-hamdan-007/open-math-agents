import Graph189ThreeCutJoint
import Graph189LowConnectivityLift
import Graph189MinimumDeletionReplay

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ThreeConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At vertex connectivity three and second-smallest degree at least
38, every graph satisfying the original even-distance cap is traceable. -/
theorem traceable (connected : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (degree : 38≤G.secondSmallestDegree) (three : G.vertexConnectivity=3) :
    ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
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
    exact Graph189ThreeCut.excludes_high connected cap three (by omega)
      (Or.inr (Or.inl ⟨degree,by omega⟩))

theorem traceable_ge37 (connected : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (degree : 37≤G.secondSmallestDegree) (three : G.vertexConnectivity=3) :
    ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
  by_cases big : 38≤G.secondSmallestDegree
  · exact traceable connected cap big three
  have eq : G.secondSmallestDegree=37 := by omega
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
    apply Graph189ThreeCut.excludes_supported connected cap three
    apply Or.inr
    apply Exists.intro (⟨37,174,47⟩ : Graph189ThreeCutThresholds.Window)
    exact ⟨by decide,eq.symm,by change 174≤Fintype.card V; omega⟩

theorem traceable_ge33 (connected : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (degree : 33≤G.secondSmallestDegree) (three : G.vertexConnectivity=3) :
    ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
  by_cases prev : 37≤G.secondSmallestDegree
  · exact traceable_ge37 connected cap prev three
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
    apply Graph189ThreeCut.excludes_covered connected cap three
    exact Or.inr ⟨degree,by omega,by omega⟩

#print axioms traceable_ge33
#print axioms traceable_ge37
#print axioms traceable
end Graph189ThreeConnectivity
