import Graph189OpenEqualityPath
import Graph189AllIndexThree
import Graph189MinimumDeletionReplay

open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
open Arxiv.«2606.03696»
namespace Graph189SevenEquality
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem arbitrary_tied_exterior (w : V) {z : V} (C : (completeAt G w).Walk z z) (hc : C.IsCycle)
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

 
/-- The final interface for turning the verified equality component and
cyclic anchors into a genuine Hamiltonian path by opening the cone cycle. -/
def Gluing (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (w : V) {a : V} (C : (completeAt G w).Walk a a), C.IsCycle →
    (∀ u (Q : (completeAt G w).Walk u u), Q.IsCycle → Q.length≤C.length) →
    (∀ v : V, v≠w → 7≤G.degree v) → Fintype.card V=23 →
    ∀ (H : Finset V) (s : ℕ→ℕ), Graph189BondyEquality.Layout (completeAt G w) C.length 3 7
      (OMA.BondyK.cyc C) H s → ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian

/-- Every remaining obstruction at k=7,n=23 supplies a concrete saturated
five-clique and three cyclic anchors in a genuine longest completion cycle. -/
theorem seven_of_gluing (glue : Gluing G) (hc : G.Connected)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (k : G.secondSmallestDegree=7) (n : Fintype.card V=23)
    (two : 2≤G.vertexConnectivity) (three : 3≤G.minDegree) :
    ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian := by
  classical
  by_contra fail
  have finish (w : V) (room : 3≤(completeAt G w).vertexConnectivity)
      (all : ∀ v, v≠w → 7≤G.degree v) (low : 7≤(completeAt G w).minDegree)
      (outside : ∀ a, ∀ C : (completeAt G w).Walk a a, C.IsCycle →
        (∀ u (Q : (completeAt G w).Walk u u), Q.IsCycle → Q.length≤C.length) →
        ∃ b, ∃ Q : ((completeAt G w).induce (offWalk C)).Walk b b, Q.IsCycle ∧ 4≤Q.length) :
      False := by
    let K := completeAt G w
    obtain ⟨u,R,hR,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide)
      (fun v => (by decide : 2≤7).trans (low.trans (K.minDegree_le_degree v)))
    obtain ⟨a,C,hC,longest⟩ := exists_longest_cycle K ⟨u,R,hR⟩
    obtain ⟨b,Q,hQ,len⟩ := outside a C hC longest
    have linked := Graph189NativeCycleLinked.of_cycle (l:=3) Q hQ (by omega) (by omega)
    obtain ⟨H,s,data⟩ := Graph189BondyEquality.equality_layout_of_linked
      (by decide : 1≤3) (by decide : 3≤7) low n
      (fun T small => Graph189CutSides.connected_after_smaller_deletion T (small.trans_le room))
      C hC longest linked
    exact fail (glue w C hC longest all n H s data)
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have des : ¬∃ a b, ∃ p : (G.induce {x : V | x≠z}).Walk a b, p.IsHamiltonian := by
    rintro ⟨a,b,p,hp⟩
    have bound := Graph189RootedSplice.order_of_hamiltonian_deletion_up_to_succ_degree
      hc z hz.symm (by omega) (by omega) fail cap p hp 4 (by omega)
    omega
  have minimum (c3 : 3≤(completeAt G z).vertexConnectivity) : False := by
    have off (v : V) (ne : v≠z) : 7≤G.degree v := by
      rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) v z ne with h|h
      · omega
      have := G.minDegree_le_degree v
      omega
    apply finish z c3 off (by rw [←k]; exact secondDegree_le_completeAt_minDegree z hz.symm)
    intro a C hC longest
    obtain ⟨b,Q,hQ,len⟩ := minimum_completion_half_cycle z hz.symm C hC longest fail des cap (by omega)
    have half : 4 ≤ (G.secondSmallestDegree + 1) / 2 := by rw [k]
    exact ⟨b,Q,hQ,half.trans len⟩
  by_cases high : 3≤G.vertexConnectivity
  · exact minimum (high.trans (completeAt_connectivity z))
  have eq : G.vertexConnectivity=2 := by omega
  by_cases low : G.minDegree<7
  · have free := Graph189TightTwoCut.free_of_low hc (by omega) cap fail eq z (by omega)
    have lift := completeAt_connectivity_add_one z (by omega) free
    exact minimum (by omega)
  obtain ⟨u,du⟩ := Graph189QuadraticOrder.second_attained (G:=G)
  have tied : G.minDegree=G.secondSmallestDegree := by have := G.minDegree_le_degree u; omega
  obtain ⟨t,conn⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) (by omega) (by omega)
  apply finish t (by omega) (fun v _ => by have := G.minDegree_le_degree v; omega)
    (by have := minDegree_le_completeAt (G:=G) t; omega)
  intro a C hC longest
  exact arbitrary_tied_exterior t C hC longest (by omega) tied cap fail

#print axioms seven_of_gluing
end Graph189SevenEquality

open SimpleGraph Finset Graph189UniversalCycle OMA.BondyK Arxiv.«2606.03696»
namespace Graph189BondyEquality
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At equality in the linked-set order bound for a universal completion, its
longest cycle and linked exterior give a Hamiltonian path in the original
graph at any admissible index. -/
theorem traceable_of_linked_equality (w : V) {k d : ℕ} (two : 2≤k) (kd : k≤d)
    (high : ∀ v, v≠w → d≤G.degree v) (min : d≤(completeAt G w).minDegree)
    (conn : k≤(completeAt G w).vertexConnectivity)
    (order : Fintype.card V=(k+1)*(d-k+2)-1)
    {a : V} (C : (completeAt G w).Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (Q : (completeAt G w).Walk b b), Q.IsCycle → Q.length≤C.length)
    (linked : Graph189LinkedExterior.Linked ((completeAt G w).induce (offWalk C)) k) :
    ∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  obtain ⟨H,s,data⟩ := equality_layout_of_linked (by omega) kd min order
    (fun S small => Graph189CutSides.connected_after_smaller_deletion S (small.trans_le conn))
    C hC longest linked
  let L : Set ℕ := {m | ∃ u, ∃ q : (completeAt G w).Walk u u, q.IsCycle ∧ q.length=m}
  have mem : C.length∈L := ⟨a,C,hC,rfl⟩
  have upper : ∀ m∈L, m≤C.length := by rintro _ ⟨u,q,hq,rfl⟩; exact longest u q hq
  have circ : C.length=(completeAt G w).circumference :=
    (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  have hD := cy_of C hC circ
  have census := cycle_covers_with_exterior hD data two kd order
  have room : d+2≤Fintype.card V := by
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le kd
    rw [he,Nat.add_sub_cancel_left] at order
    rw [he]
    have positive : 1≤(k+1)*(e+2) := Nat.mul_pos (by omega) (by omega)
    have n : Fintype.card V+1=(k+1)*(e+2) := by omega
    nlinarith
  exact traceable_of_equality_census w hD data high kd room census

/-- The exact seven-degree boundary whenever δ≥3. -/
theorem seven (hc : G.Connected) (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (k : G.secondSmallestDegree=7) (n : Fintype.card V=23)
    (two : 2≤G.vertexConnectivity) (three : 3≤G.minDegree) :
    ∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian := by
  apply Graph189SevenEquality.seven_of_gluing _ hc cap k n two three
  intro w a C hC longest high order H s data
  let L : Set ℕ := {m | ∃ u, ∃ q : (completeAt G w).Walk u u, q.IsCycle ∧ q.length=m}
  have mem : C.length∈L := ⟨a,C,hC,rfl⟩
  have upper : ∀ m∈L, m≤C.length := by rintro _ ⟨u,q,hq,rfl⟩; exact longest u q hq
  have circ : C.length=(completeAt G w).circumference :=
    (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  have hD := cy_of C hC circ
  exact traceable_of_equality_census w hD data high (by decide) (by omega)
    (cycle_covers_with_exterior hD data (by decide) (by decide) order)

#print axioms traceable_of_linked_equality
#print axioms seven
end Graph189BondyEquality
