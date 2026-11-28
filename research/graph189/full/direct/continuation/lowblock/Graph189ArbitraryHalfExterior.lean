import Graph189CriticalExterior
import Graph189ExteriorCore

open SimpleGraph Finset
open Graph189ExteriorDegreeCycle Graph189UniversalCycle Graph189ExteriorCore
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ArbitraryHalfExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- After deleting an arbitrary vertex, at most one surviving vertex has
ambient degree below k. Removing that vertex from the nonisolated exterior
leaves a genuine cycle of length at least floor((k−1)/2). -/
theorem deletion_core (w : V) {x y : {v : V | v ≠ w}}
    (p : (G.induce {v : V | v ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : (G.induce {v : V | v ≠ w}).Walk u v, q.IsPath → q.length ≤ p.length)
    (missing : 3 ≤ (univ.filter (fun v => v ∉ p.support)).card)
    (k8 : 8 ≤ G.secondSmallestDegree)
    (enough : G.secondSmallestDegree+6 ≤ 2*G.minDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    Nonempty (Core ((G.induce {u : V | u ≠ w}).induce {v | v ∉ p.support.toFinset})
      ((G.secondSmallestDegree-3)/2)) := by
  classical
  let D := {v : V | v ≠ w}
  let H := G.induce D
  let U := {t : D | t ∉ p.support.toFinset}
  let E := H.induce U
  let k := G.secondSmallestDegree
  have inc (a b : U) (eq : a.val.val=b.val.val) : a=b := Subtype.ext (Subtype.ext eq)
  have out (a : U) : a.val ∉ p.support := fun h => a.property (List.mem_toFinset.mpr h)
  have internal (a : U) : E.degree a = (H.neighborFinset a.val \ p.support.toFinset).card := by
    rw [degree_induce_filter]
    congr 1
    ext v
    simp [U]
  have bound {q : ℕ} (a b : U) (e : E.Adj a b) (da : q+1 ≤ G.degree a.val.val)
      (db : q+1 ≤ G.degree b.val.val) : 2*q ≤ k+2*E.degree a := by
    rw [internal]
    exact deletion_exterior_local_degree w p hp longest (out a) (out b) e (cap _) da db
  have edge : ∃ a b : U, E.Adj a b := by
    by_contra! none
    have independent : ∀ a ∉ p.support, ∀ b ∉ p.support, ¬ H.Adj a b := by
      intro a ha b hb
      exact none ⟨a,fun h => ha (List.mem_toFinset.mp h)⟩ ⟨b,fun h => hb (List.mem_toFinset.mp h)⟩
    have := independent_omits_at_most_two w p hp longest independent (by omega) cap
    omega
  obtain ⟨x,y,xy⟩ := edge
  obtain ⟨low,high⟩ : ∃ low : U, ∀ b : U, b≠low → k ≤ G.degree b.val.val := by
    by_cases bad : ∃ a : U, G.degree a.val.val < k
    · obtain ⟨a,ha⟩ := bad
      refine ⟨a,fun b ne => ?_⟩
      rcases degree_pair (G:=G) b.val.val a.val.val (fun eq => ne (inc b a eq)) with h|h
      · exact h
      · exact (Nat.not_le_of_lt ha h).elim
    · exact ⟨x,fun b _ => le_of_not_gt (fun h => bad ⟨b,h⟩)⟩
  let F := E.induce {t : U | t ≠ low}
  have edgeF : ∃ a b, F.Adj a b := by
    obtain ⟨a,b,diff,e⟩ : ∃ a b : U, a≠low ∧ E.Adj a b := by
      by_cases h : x=low
      · exact ⟨y,x,fun h' => xy.ne (h.trans h'.symm),xy.symm⟩
      · exact ⟨x,y,h,xy⟩
    have minA := G.minDegree_le_degree a.val.val
    have minB := G.minDegree_le_degree b.val.val
    have cmp := bound (q:=G.minDegree-1) a b e (by omega) (by omega)
    have many : 1 < (E.neighborFinset a).card := by
      rw [E.card_neighborFinset_eq_degree]
      change 2*(G.minDegree-1) ≤ G.secondSmallestDegree+2*E.degree a at cmp
      omega
    obtain ⟨c,hc,ne⟩ := exists_mem_ne many low
    exact ⟨⟨a,diff⟩,⟨c,ne⟩,(E.mem_neighborFinset _ _).mp hc⟩
  obtain ⟨core⟩ := of_nonisolated (G:=F) (d:=(k-3)/2) edgeF (by
      intro a b edge
      have ha := high a.val a.property
      have hb := high b.val b.property
      have cmp := bound (q:=k-1) a.val b.val edge (by omega) (by omega)
      have loss := degree_le_deletion_add_one (G:=E) low a
      change E.degree a.val ≤ F.degree a+1 at loss
      omega)
  let emb := (Embedding.induce (G:=E) {t : U | t ≠ low}).toHom
  exact ⟨core.map_into emb Subtype.val_injective⟩

theorem completion_core (w : V) {a : V} (C : (completeAt G w).Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : (completeAt G w).Walk b b), R.IsCycle → R.length ≤ C.length)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian) (k8 : 8 ≤ G.secondSmallestDegree)
    (enough : G.secondSmallestDegree+6 ≤ 2*G.minDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    Nonempty (Core ((completeAt G w).induce {t : V | t ∉ C.support})
      ((G.secondSmallestDegree-3)/2)) := by
  classical
  let H := G.induce {u : V | u ≠ w}
  obtain ⟨u,v,p,hp,_,support,maxp⟩ := longest_in_deletion G w C hC longest
  have gap := high_min_all_paths_gap notTrace (by omega) cap (fun t => by
    have := G.minDegree_le_degree t
    omega)
  obtain ⟨core⟩ := deletion_core w p hp (fun r => maxp _ _ r)
    (deletion_gap w p hp gap) k8 enough cap
  let U := {t : {v : V | v ≠ w} | t ∉ p.support.toFinset}
  let W := {t : V | t ∉ C.support}
  let f : H.induce U →g (completeAt G w).induce W := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := by
    intro i j h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W => z.val) h))
  exact ⟨core.map_into f inj⟩

#print axioms deletion_core
#print axioms completion_core
end Graph189ArbitraryHalfExterior
