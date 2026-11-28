import Graph189Removable
import Graph189R1Metric

open Finset SimpleGraph
namespace Graph189ModeratePort
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

omit [Nontrivial V] in
/-- In a tight side every high vertex has *all* the available neighbors,
both on its own side and in the cut. -/
theorem tight_neighbors (sides : Graph189CutSides.CutSides G A B S)
    (tight : A.card+S.card ≤ G.secondSmallestDegree+1)
    {a : V} (ha : a∈A) (high : G.secondSmallestDegree≤G.degree a) :
    G.neighborFinset a = A.erase a ∪ S := by
  have sub : G.neighborFinset a ⊆ A.erase a ∪ S := by
    intro x hx
    have edge := (G.mem_neighborFinset _ _).mp hx
    rcases sides.cover x with ax|bx|sx
    · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,ax⟩)
    · exact (sides.no_cross a ha x bx edge).elim
    · exact mem_union_right _ sx
  apply eq_of_subset_of_card_le sub
  have upper := card_union_le (A.erase a) S
  have erase := card_erase_add_one ha
  rw [G.card_neighborFinset_eq_degree]
  omega

/-- Even the unique possible low vertex is adjacent to every other vertex
in a tight side. -/
theorem tight_clique (sides : Graph189CutSides.CutSides G A B S)
    (tight : A.card+S.card ≤ G.secondSmallestDegree+1)
    {x y : V} (hx : x∈A) (hy : y∈A) (ne : x≠y) : G.Adj x y := by
  rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x y ne with h|h
  · apply (G.mem_neighborFinset _ _).mp
    rw [tight_neighbors sides tight hx h]
    exact mem_union_left _ (mem_erase.mpr ⟨ne.symm,hy⟩)
  · apply SimpleGraph.Adj.symm
    apply (G.mem_neighborFinset _ _).mp
    rw [tight_neighbors sides tight hy h]
    exact mem_union_left _ (mem_erase.mpr ⟨ne,hx⟩)

omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
/-- For a possible middle component, two distinct labels can be routed to
distinct contacts as soon as both sides have at least two incident vertices. -/
theorem distinct_contacts
    (labels : ∃ r∈S, ∃ t∈S, r≠t)
    (allLabels : ∀ r∈S, ∃ a∈A, G.Adj r a)
    (ports : ∃ u∈A, ∃ v∈A, u≠v ∧ (∃ r∈S,G.Adj r u) ∧ (∃ t∈S,G.Adj t v)) :
    ∃ r∈S, ∃ t∈S, ∃ a∈A, ∃ b∈A, r≠t ∧ a≠b ∧ G.Adj r a ∧ G.Adj t b := by
  obtain ⟨r,hr,t,ht,rt⟩ := labels
  obtain ⟨a,ha,ra⟩ := allLabels r hr
  obtain ⟨b,hb,tb⟩ := allLabels t ht
  by_cases ab : a=b
  · subst b
    obtain ⟨u,hu,v,hv,uv,pu,pv⟩ := ports
    obtain ⟨q,hq,qv⟩ := pv
    have pair : ∃ w∈A, w≠a ∧ ∃ j∈S, G.Adj j w := by
      by_cases ua : u=a
      · exact ⟨v,hv,fun va => uv (ua.trans va.symm),q,hq,qv⟩
      · exact ⟨u,hu,ua,pu⟩
    obtain ⟨w,hw,wa,j,hj,jw⟩ := pair
    by_cases jr : j=r
    · exact ⟨r,hr,t,ht,w,hw,a,ha,rt,wa,jr ▸ jw,tb⟩
    · exact ⟨j,hj,r,hr,w,hw,a,ha,jr,wa,jw,ra⟩
  · exact ⟨r,hr,t,ht,a,ha,b,hb,rt,ab,ra,tb⟩

#print axioms tight_clique
#print axioms distinct_contacts
end Graph189ModeratePort
