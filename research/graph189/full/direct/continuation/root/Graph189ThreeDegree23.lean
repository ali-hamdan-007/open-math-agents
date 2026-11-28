import Graph189ThreeStrictFloor
import Graph189ThreeOrderWindows
import Graph189LowConnectivityLift

open SimpleGraph Finset OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ThreeConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem traceable_ge22 (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (lo : 22≤G.secondSmallestDegree) (three : G.vertexConnectivity=3) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  by_cases high : 24≤G.secondSmallestDegree
  · exact traceable_ge24 hc cap high three
  have eq : G.secondSmallestDegree=22 ∨ G.secondSmallestDegree=23 := by omega
  by_contra bad
  obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have deg := Graph189CutSides.connectivity_le_degree (G:=G) z
  have del : ¬∃a b,∃p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian := by
    rintro ⟨a,b,p,hp⟩
    exact bad (Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion_unrestricted hc z least.symm
      (by omega) (by omega) point p hp)
  obtain ⟨u,ne⟩ := exists_ne z
  have count : G.secondSmallestDegree<Fintype.card V := by
    rcases degree_pair (G:=G) u z ne with h|h
    · exact lt_of_le_of_lt h (G.degree_lt_card_verts u)
    · exact lt_of_le_of_lt h (G.degree_lt_card_verts z)
  have lower := Graph189LowConnectivityLift.minimum_deletion hc z least.symm (by omega) (by omega) (by omega)
    (Or.inl three) point (by omega) bad del
  rw [three] at lower
  have old : 5*G.secondSmallestDegree≤Fintype.card V+11 := by rcases eq with h|h <;> rw [h] at lower ⊢ <;> omega
  have strict := Graph189ThreeStrictFloor.strict hc cap bad three (by omega) old
  apply bad (Graph189ThreeOrderWindows.traceable hc cap three (by omega) (by omega) ?_)
  rcases eq with h|h <;> rw [h] at strict ⊢ <;> norm_num [Graph189ThreeOrderWindows.cutoff] <;> omega

theorem traceable_ge23 (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (lo : 23≤G.secondSmallestDegree) (three : G.vertexConnectivity=3) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian :=
  traceable_ge22 hc cap (by omega) three

end Graph189ThreeConnectivity
#print axioms Graph189ThreeConnectivity.traceable_ge22
#print axioms Graph189ThreeConnectivity.traceable_ge23
