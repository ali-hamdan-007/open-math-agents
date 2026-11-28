import Graph189QuadraticOrder
import Graph189NativeCycleLinked
import Graph189TightCutJoint
import Graph189TwoStructuralRanges

open SimpleGraph Finset Graph189CutSides Graph189UniversalCycle
namespace Graph189TightTwoCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a nontraceable graph with vertex connectivity two, any subthreshold
vertex is absent from every minimum separating pair. -/
theorem free_of_low (hc : G.Connected) (k5 : 5≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (fail : ¬∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian)
    (two : G.vertexConnectivity=2) (z : V) (low : G.degree z<G.secondSmallestDegree)
    (T : Finset V) (size : T.card=G.vertexConnectivity) (inside : z∈T) :
    (G.induce {u : V | u∉T}).Connected := by
  classical
  by_contra no
  have remaining : (T.erase z).card=1 := by rw [card_erase_of_mem inside,size,two]
  obtain ⟨t,ht⟩ := card_eq_one.mp remaining
  have zt : z≠t := by
    intro eq
    have h : z∉T.erase z := notMem_erase z T
    rw [ht,eq] at h
    simp at h
  have pair : T={z,t} := by rw [← insert_erase inside,ht]
  have hz' := G.degree_lt_card_verts z
  have large : 2<Fintype.card V := by
    have bound := Graph189RootedSplice.connectivity_le_degree (G:=G) z
    omega
  have rest : ∃ v, v∉T := by
    by_contra! all
    have eq := eq_univ_iff_forall.mpr all
    rw [eq,card_univ] at size
    omega
  obtain ⟨A,B,sides⟩ := exists_cutSides_of_disconnected T rest no
  have smaller : ∀ U : Finset V, U.card<T.card → (G.induce {v : V | v∉U}).Connected :=
    fun U h => Graph189CutSides.connected_after_smaller_deletion U (h.trans_eq size)
  have cap' (v : V) : G.distEven v≤1+G.secondSmallestDegree := by simpa [Nat.add_comm] using cap v
  have anch := sides.anchor_degree smaller cap' inside
  obtain ⟨⟨a,ha,az⟩,⟨b,hb,bz⟩⟩ := sides.contacts_of_minimum smaller inside
  rw [pair] at sides
  exact fail (traceable hc sides zt (by omega) k5 cap ha hb az.symm bz.symm)

#print axioms free_of_low
end Graph189TightTwoCut




open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
namespace Graph189TightTwoCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At a tied minimum, parity yields a four-vertex exterior cycle already
at k=7, for a completion centered at any vertex. -/
private theorem tied_exterior (w : V) {z : V} (C : (completeAt G w).Walk z z) (hc : C.IsCycle)
    (longest : ∀ u (R : (completeAt G w).Walk u u), R.IsCycle → R.length≤C.length)
    (k7 : 7≤G.secondSmallestDegree) (tied : G.minDegree=G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (fail : ¬∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian) :
    ∃ a, ∃ Q : ((completeAt G w).induce {t : V | t∉C.support}).Walk a a, Q.IsCycle ∧ 4≤Q.length := by
  classical
  let H := G.induce {u : V | u≠w}
  obtain ⟨u,v,p,hp,_,support,maxp⟩ := longest_in_deletion G w C hc longest
  have paths := high_min_all_paths_gap fail (by omega) cap (fun v => by
    have := G.minDegree_le_degree v
    omega)
  have gap := deletion_gap w p hp paths
  have edge : ∃ a ∉ p.support, ∃ b ∉ p.support, H.Adj a b := by
    by_contra! indep
    have bound := Graph189ExteriorDegreeCycle.independent_omits_at_most_two w p hp (fun r => maxp _ _ r) indep
      (by omega) cap
    omega
  have deg (v : {x : V | x≠w}) : G.minDegree-1+1≤G.degree v.val := by
    have := G.minDegree_le_degree v.val
    omega
  obtain ⟨a,Q,hQ,len⟩ := nontrivial_deletion_cycle_rounded (d:=3) w p hp
    (fun r => maxp _ _ r) edge cap deg (by decide) (by omega)
  let U := {t : {v : V | v ≠ w} | t ∉ p.support.toFinset}
  let W := {t : V | t ∉ C.support}
  let f : H.induce U →g (completeAt G w).induce W := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := by
    intro i j h
    have values : i.val.val=j.val.val := congrArg (fun z : W => z.val) h
    exact Subtype.ext (Subtype.ext values)
  exact ⟨f a,Q.map f,hQ.map inj,len.trans_eq (Walk.length_map f Q).symm⟩

 /-- Every two-connected counterexample at k≥7 and minimum degree at least
three has at least 4k−5 vertices, including at connectivity exactly two. -/
theorem index_three (hc : G.Connected) (k7 : 7≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (fail : ¬∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian)
    (conn : 2≤G.vertexConnectivity) (high : 3≤G.minDegree)
    :
    4*G.secondSmallestDegree ≤ Fintype.card V+5 := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  let k := G.secondSmallestDegree
  have result (h : (3+1)*(k-3+2)-1≤Fintype.card V) : 4*k≤Fintype.card V+5 := by
    dsimp [k] at *
    omega
  apply result
  have other := Graph189QuadraticOrder.second_attained (G:=G)
  obtain ⟨w,hw⟩ := other
  have dk : G.minDegree≤G.secondSmallestDegree := hw ▸ G.minDegree_le_degree w
  have room2 : 2<Fintype.card V-1 := by have := G.degree_lt_card_verts w; omega
  by_cases near : ∃ u v, ∃ q : (G.induce {x : V | x≠z}).Walk u v, q.IsHamiltonian
  · obtain ⟨u,v,Q,hQ⟩ := near
    obtain ⟨a,b,p,hp,on,maximal⟩ := Graph189RootedSplice.exists_longest_containing G z
    obtain ⟨du,_,bound⟩ := Graph189RootedSplice.rooted_matching_cone_order hc z hz.symm
      (by omega) (by omega) fail cap Q hQ p hp on maximal
    exact bound 3 (by omega)
  have minimum (c3 : 3≤(completeAt G z).vertexConnectivity) :
      (3+1)*(k-3+2)-1≤Fintype.card V := by
    apply Graph189ConeLinkedOrder.order (completeAt G z) z (by decide : 2≤3) (by omega : 3≤G.secondSmallestDegree)
      (secondDegree_le_completeAt_minDegree z hz.symm) c3
    intro a C hC longest
    obtain ⟨b,Q,hQ,len⟩ := minimum_completion_half_cycle z hz.symm C hC longest fail near cap (by omega)
    exact Graph189NativeCycleLinked.of_cycle Q hQ (by omega) (by omega)
  by_cases two : G.vertexConnectivity=2
  · by_cases low : G.minDegree<G.secondSmallestDegree
    · have free := free_of_low hc (by omega) cap fail two z (by omega)
      exact minimum (by have := completeAt_connectivity_add_one z (by omega) free; omega)
    have tied : G.minDegree=G.secondSmallestDegree := by omega
    obtain ⟨t,hconn⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) (by omega) (by omega)
    apply Graph189ConeLinkedOrder.order (completeAt G t) t (by decide : 2≤3) (by omega : 3≤G.secondSmallestDegree)
      (by rw [← tied]; exact minDegree_le_completeAt t) (by omega)
    intro a C hC longest
    obtain ⟨b,Q,hQ,len⟩ := tied_exterior t C hC longest k7 tied cap fail
    exact Graph189NativeCycleLinked.of_cycle Q hQ (by omega) (by omega)
  exact minimum (by have := completeAt_connectivity (G:=G) z; omega)

/-- The full moderate band at k≥8 is traceable whenever the minimum degree is
at least three. The separately verified degree-two theorem covers the last degree. -/
theorem moderate (hc : G.Connected) (k8 : 8≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (conn : 2≤G.vertexConnectivity) (high : 3≤G.minDegree)
    (order : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian := by
  by_contra fail
  have bound := index_three hc (by omega) cap fail conn high
  omega

#print axioms index_three
#print axioms moderate
end Graph189TightTwoCut
