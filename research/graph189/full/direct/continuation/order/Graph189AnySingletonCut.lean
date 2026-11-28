import Graph189TwoCutSingleton
import Graph189RotationMinOrder

open SimpleGraph Finset
namespace Graph189AnySingletonCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A singleton component of a minimum cut yields traceability if the
other vertices outside the separator still separate into two nonempty sides. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (z : V) (sc : G.degree z≤G.vertexConnectivity) (two : 2≤G.degree z)
    (large : 8≤G.secondSmallestDegree) (wide : 2*G.degree z≤G.secondSmallestDegree+1)
    (disc : ¬(G.induce {u : V | u∉insert z (G.neighborFinset z)}).Connected) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases three : 3≤G.degree z
  · obtain ⟨W,split⟩ := Graph189TwoCutSingleton.split_of_disconnected_complement z sc (by omega) disc
    have bounds := Graph189SingletonCutOrder.population hc point z (G.neighborFinset z) W split
      (by rwa [G.card_neighborFinset_eq_degree]) (by rwa [G.card_neighborFinset_eq_degree])
    by_contra bad
    have lo := Graph189RotationLinked.base_order bad point (l:=3) (by decide) (three.trans sc) (by omega)
    have upper := bounds.1
    omega
  · exact Graph189TwoCutSingleton.of_disconnected_complement hc point (two.trans sc) z (by omega) large disc

/-- When k>6(s−1), deleting s=κ vertices and obtaining any three
distinct components is enough to construct a Hamiltonian path. -/
theorem of_three_components (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (S : Finset V) (sc : S.card≤G.vertexConnectivity) (two : 2≤S.card)
    (large : 8≤G.secondSmallestDegree) (wide : 6*(S.card-1)<G.secondSmallestDegree)
    (c : Fin 3 ↪ (G.induce {u : V | u∉S}).ConnectedComponent) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let H := G.induce {u : V | u∉S}
  let F (i : Fin 3) := Graph189ThreeLargeComponents.vertices S (c i)
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨i,tiny⟩ : ∃ i : Fin 3, (F i).card≤1 := by
    by_contra! many
    exact Graph189ThreeLargeComponents.no_three_nonsingleton S two sc wide point c many
  have members (j : Fin 3) : ∃ v, H.connectedComponentMk v=c j := (c j).exists_rep
  choose x rep using members
  let z := (x i).val
  have mem (j : Fin 3) (v : {u : V | u∉S}) (eq : H.connectedComponentMk v=c j) : v.val∈F j := by
    change v.val∈Graph189ThreeLargeComponents.vertices S (c j)
    exact mem_filter.mpr ⟨mem_univ _,v.property,eq⟩
  have sub : G.neighborFinset z⊆S := by
    intro v hv
    have e := (G.mem_neighborFinset _ _).mp hv
    by_contra outside
    let w : {u : V | u∉S} := ⟨v,outside⟩
    have edge : H.Adj (x i) w := e
    have wC := (ConnectedComponent.connectedComponentMk_eq_of_adj edge).symm.trans (rep i)
    have same := card_le_one_iff.mp tiny (mem i (x i) (rep i)) (mem i w wC)
    exact e.ne same
  have size : S.card≤(G.neighborFinset z).card := by
    rw [G.card_neighborFinset_eq_degree]
    exact sc.trans (Graph189CutSides.connectivity_le_degree z)
  have ns : G.neighborFinset z=S := eq_of_subset_of_card_le sub size
  have dz : G.degree z=S.card := by rw [←ns,G.card_neighborFinset_eq_degree]
  apply traceable hc cap z (by rwa [dz]) (by rwa [dz]) large (by omega)
  rw [ns]
  intro con
  obtain ⟨j,l,ji,li,jl⟩ : ∃ j l : Fin 3, j≠i ∧ l≠i ∧ j≠l := by
    fin_cases i
    · exact ⟨1,2,by decide,by decide,by decide⟩
    · exact ⟨0,2,by decide,by decide,by decide⟩
    · exact ⟨0,1,by decide,by decide,by decide⟩
  let U : Set V := {u | u∉insert z S}
  have outside (t : Fin 3) (ne : t≠i) : (x t).val∈U := by
    intro bad
    rcases mem_insert.mp bad with eq|inside
    · have same : x t=x i := Subtype.ext eq
      exact ne (c.injective ((rep t).symm.trans ((congrArg H.connectedComponentMk same).trans (rep i))))
    · exact (x t).property inside
  let inclusion : G.induce U →g H :=
    ⟨fun v => ⟨v.val,fun h => v.property (mem_insert_of_mem h)⟩,fun e => e⟩
  obtain ⟨p⟩ := con (⟨(x j).val,outside j ji⟩ : U) (⟨(x l).val,outside l li⟩ : U)
  have reaches : H.Reachable (x j) (x l) := (p.map inclusion).reachable
  exact jl (c.injective ((rep j).symm.trans ((ConnectedComponent.eq.mpr reaches).trans (rep l))))

#print axioms traceable
#print axioms of_three_components
end Graph189AnySingletonCut
