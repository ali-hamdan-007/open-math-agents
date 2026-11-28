import Graph189SixRotation
import Graph189SixProtected
import Graph189HighMinimumGap
import Graph189ThreeRegularMinimum

open SimpleGraph Finset
namespace Graph189SixMinimumThree
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The moderate case at degree six, whenever every vertex has degree
at least three. Both ordinary and protected paths are built in G. -/
theorem traceable (conn : 2≤G.vertexConnectivity) (six : G.secondSmallestDegree=6)
    (minimum : 3≤G.minDegree) (small : Fintype.card V≤20)
    (localCap : ∀v,G.distEven v≤G.secondSmallestDegree+1) :
    ∃a b,∃p : G.Walk a b,p.IsHamiltonian := by
  classical
  have min (v : V) : 3≤G.degree v := minimum.trans (G.minDegree_le_degree v)
  obtain ⟨z⟩ := (inferInstance : Nonempty V)
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let E := p.support.toFinsetᶜ
  have low (v : V) (hv : v∈E) : G.degree v<6 :=
    Graph189SixRotation.omitted_low p hp mx conn small six (by omega) localCap (by simpa [E] using hv)
  have few : E.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    have l1 := low u hu
    have l2 := low v hv
    omega
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  by_contra nontrace
  obtain ⟨w,lw,_,_,r,hr⟩ := Graph189ExteriorDegreeCycle.near_longest_has_hamiltonian_low_deletion
    p hp mx (by omega) nontrace (by omega) localCap min
  have high (x : V) (ne : x≠w) : G.secondSmallestDegree≤G.degree x :=
    (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x w ne).resolve_right
      (not_le.mpr lw)
  exact nontrace (Graph189SixProtected.traceable w (min w) six high localCap (by omega) r hr)

#print axioms traceable
end Graph189SixMinimumThree
