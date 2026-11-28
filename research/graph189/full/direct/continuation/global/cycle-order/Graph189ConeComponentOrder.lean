import Graph189ActualExteriorComponent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Graph189ConeComponentOrder
open SimpleGraph Finset Graph189ExteriorGap

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A degree lower bound on an exterior set produces disjoint contact edges,
without requiring connectivity as large as the number of edges sought. -/
theorem matching_of_exterior_degree (P K : Finset V)
    (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈P)
    {j : ℕ} (enough : j ≤ K.card) (degree : ∀ u∈K, j+K.card ≤ G.degree u+1) :
    ∃ M : Finset V, M ⊆ P ∧ M.card = j ∧ ∃ f : M ↪ K, ∀ u, G.Adj u.val (f u).val := by
  classical
  obtain ⟨T,subT,sizeT⟩ := Finset.exists_subset_card_eq enough
  let links (u : T) := G.neighborFinset u.val ∩ P
  have wide (u : T) : j ≤ (links u).card := by
    have member := subT u.property
    have cover : G.neighborFinset u.val ⊆ K.erase u.val ∪ links u := by
      intro v hv
      have edge := (G.mem_neighborFinset _ _).mp hv
      by_cases vk : v∈K
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨edge.ne.symm,vk⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv,boundary _ member _ vk edge⟩)
    have count := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
    have erased := Finset.card_erase_add_one member
    have d := degree _ member
    change j + K.card ≤ (G.neighborFinset u.val).card+1 at d
    omega
  have hall (U : Finset T) : U.card ≤ (U.biUnion links).card := by
    by_cases empty : U = ∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have bound : U.card ≤ j := by simpa [sizeT] using U.card_le_univ
    exact bound.trans ((wide u).trans (Finset.card_le_card ((show links u ⊆ U.biUnion links from fun z hz => Finset.mem_biUnion.mpr ⟨u,hu,hz⟩))))
  obtain ⟨f,inj,hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' links).mp hall
  let M := Finset.univ.image f
  have reverse (v : M) : ∃ u : T, f u = v.val := by
    obtain ⟨u,_,eq⟩ := Finset.mem_image.mp v.property
    exact ⟨u,eq⟩
  let pick (v : M) := (reverse v).choose
  have eq (v : M) : f (pick v) = v.val := (reverse v).choose_spec
  let inv (v : M) : K := ⟨(pick v).val,subT (pick v).property⟩
  have invInj : Function.Injective inv := by
    intro v w h
    have h' : pick v = pick w := Subtype.ext (congrArg (fun z : K => z.val) h)
    exact Subtype.ext ((eq v).symm.trans ((congrArg f h').trans (eq w)))
  refine ⟨M,?_,?_,⟨inv,invInj⟩,?_⟩
  · intro v hv
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_inter.mp (hf u)).2
  · simp [M, Finset.card_image_of_injective _ inj,sizeT]
  · intro v
    have edge := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (hf (pick v))).1
    rw [eq v] at edge
    exact edge.symm

/-- A Hamilton-connected component of at least half the degree parameter
outside a longest path forces the full cone order. One vertex of the cone was
deleted, so its order is one more than the order of the ambient graph here. -/
theorem cone_order_of_component {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (outside : ∀ u∈K, u∉p.support)
    (boundary : ∀ u∈K, ∀ v∉K, G.Adj u v → v∈p.support)
    (ham : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    {s k : ℕ} (two : 2 ≤ s) (regime : 2*s ≤ k) (half : k ≤ 2*K.card)
    (degree : ∀ u∈K, k ≤ G.degree u+1) (pathSize : s-1 ≤ p.support.length)
    (connected : ∀ cut : Finset V, cut.card < s-1 → (G.induce {u : V | u∉cut}).Connected) :
    (s+1)*(k-s+2)-1 ≤ Fintype.card V+1 := by
  classical
  have size : 1 < K.card := by omega
  by_cases large : k-s+1 ≤ K.card
  · have ob := whole_core_order_of_connectivity p hp longest K outside size boundary ham
      (s:=s-1) (by omega) pathSize (by omega) connected
    have factor : s-1+2 = s+1 := by omega
    rw [factor] at ob
    have mul := Nat.mul_le_mul_left (s+1) large
    have e : (s+1)*(k-s+2) = (s+1)*(k-s+1) + (s+1) := by ring
    omega
  · have mk : K.card ≤ k := by omega
    obtain ⟨M,inside,card,f,edges⟩ := matching_of_exterior_degree (G:=G) p.support.toFinset K
      (fun u hu v hv e => List.mem_toFinset.mpr (boundary u hu v hv e))
      (j:=k-K.card) (by omega) (by intro u hu; have d := degree u hu; omega)
    have ob := exterior_vertex_matching_order p hp longest K size outside ham M
      (Finset.card_pos.mp (by omega)) (fun u hu => List.mem_toFinset.mp (inside hu)) f edges
    rw [card] at ob
    have a : s ≤ K.card := by omega
    have b : s ≤ k-K.card+1 := by omega
    have product {a b s : ℕ} :
        (s+1)*(s+a+b+1) ≤ (s+b+1)*(s+a)+(s+b)+1 := by
      nlinarith [Nat.zero_le (a*b)]
    have replace : k-s+2 = s+(K.card-s)+(k-K.card+1-s)+1 := by omega
    have mEq : s+(K.card-s)=K.card := by omega
    have bEq : s+(k-K.card+1-s)=k-K.card+1 := by omega
    have rank := product (a:=K.card-s) (b:=k-K.card+1-s) (s:=s)
    rw [← replace,bEq,mEq,show k-K.card+1+1=k-K.card+2 by omega] at rank
    omega

#print axioms matching_of_exterior_degree
#print axioms cone_order_of_component
end Graph189ConeComponentOrder
