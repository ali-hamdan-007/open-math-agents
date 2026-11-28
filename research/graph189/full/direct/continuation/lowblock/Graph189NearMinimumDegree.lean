import Graph189HighMinimumGap

open SimpleGraph
namespace Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A nontraceable graph with a Hamilton path after deleting a minimum
vertex must have that vertex strictly below the second-smallest degree. -/
theorem low_of_traceable_minimum_deletion (hk : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (nontrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian) (z : V)
    (minimum : G.degree z=G.minDegree) {x y : {v : V | v ≠ z}}
    (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian) :
    G.degree z < G.secondSmallestDegree := by
  classical
  by_contra! high
  have all (v : V) : G.secondSmallestDegree < 2*G.degree v := by
    have h := G.minDegree_le_degree v
    rw [←minimum] at h
    omega
  let inc := (Embedding.induce (G:=G) {v : V | v ≠ z}).toHom
  have gap := high_min_all_paths_gap nontrace hk cap all _ _ (p.map inc) (hp.isPath.map Subtype.val_injective)
  rw [Walk.support_map,List.length_map,hp.length_support] at gap
  have one : Fintype.card {v : V | v ≠ z}=Fintype.card V-1 := by
    change Fintype.card {v : V // ¬ v=z} = _
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [one] at gap
  omega

#print axioms low_of_traceable_minimum_deletion
end Graph189ExteriorDegreeCycle
