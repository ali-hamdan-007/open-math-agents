import Graph189DeletionLinked
import Graph189MinimumDeletionExterior
import Graph189CriticalExterior

namespace Graph189CompletionLinkedFour
open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem completion (w : V) {z : V} (C : (completeAt G w).Walk z z) (hc : C.IsCycle)
    (maximal : ∀ v (R : (completeAt G w).Walk v v), R.IsCycle → R.length ≤ C.length)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) {l d : ℕ}
    (min : ∀ v : {x : V | x ≠ w}, d≤G.degree v.val)
    (three : 3≤l) (ratio : 3*l≤G.secondSmallestDegree+2)
    (low : 2*l+2≤d) (gap : G.secondSmallestDegree+6≤2*d)
    (edge : ∀ {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v), p.IsPath →
      (∀ {a b}, ∀ q : (G.induce {x : V | x ≠ w}).Walk a b, q.IsPath → q.length≤p.length) →
      ∃ a ∉ p.support, ∃ b ∉ p.support, (G.induce {x : V | x ≠ w}).Adj a b) :
    Graph189LinkedExterior.Linked ((completeAt G w).induce {t : V | t∉C.support}) l := by
  classical
  let H := G.induce {x : V | x ≠ w}
  obtain ⟨u,v,p,hp,_,support,longest⟩ := longest_in_deletion G w C hc maximal
  let high (a : {x : V | x ≠ w}) := G.secondSmallestDegree≤G.degree a.val
  have pair (a b : {x : V | x ≠ w}) (ne : a≠b) : high a ∨ high b :=
    degree_pair (G:=G) a.val b.val (fun eq => ne (Subtype.ext eq))
  have hd (a : {x : V | x ≠ w}) (h : high a) : G.secondSmallestDegree≤H.degree a+1 :=
    h.trans (degree_le_deletion_add_one w a)
  have md (a : {x : V | x ≠ w}) : d≤H.degree a+1 := (min a).trans (degree_le_deletion_add_one w a)
  have caps (a : {x : V | x ≠ w}) : (univ.filter (fun z => H.dist a z=2)).card≤G.secondSmallestDegree :=
    induced_second_layer (G:=G) {x : V | x ≠ w} a (cap a.val)
  have linked := Graph189DeletionLinked.exterior p hp (fun q => longest _ _ q)
    (edge p hp (fun q => longest _ _ q)) high pair hd md caps three ratio low gap
  let U := {t : {v : V | v ≠ w} | t∉p.support.toFinset}
  let W := {t : V | t∉C.support}
  let f : H.induce U →g (completeAt G w).induce W := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  apply Graph189LinkedExterior.map f _ linked
  intro a b eq
  exact Subtype.ext (Subtype.ext (congrArg (fun x : W => x.val) eq))

/-- The critical completion may be centered at any vertex. The linking
parameter only enters through the three explicit inequalities. -/
theorem critical_fixed (w : V) {z : V}
    (C : (completeAt G w).Walk z z) (hc : C.IsCycle)
    (maximal : ∀ v (R : (completeAt G w).Walk v v), R.IsCycle → R.length≤C.length)
    (notTrace : ¬∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {l : ℕ} (three : 3≤l) (ratio : 3*l≤G.secondSmallestDegree+2)
    (room : 2*l+2≤G.minDegree)
    (gap : G.secondSmallestDegree+6≤2*G.minDegree) (k5 : 5≤G.secondSmallestDegree) :
    Graph189LinkedExterior.Linked ((completeAt G w).induce {t : V | t∉C.support}) l := by
  have md (a : {x : V | x ≠ w}) : G.minDegree≤G.degree a.val := G.minDegree_le_degree a.val
  apply completion w C hc maximal cap md three ratio room gap
  intro u v p hp longest
  have half (a : V) : G.secondSmallestDegree < 2*G.degree a := by
    have := G.minDegree_le_degree a
    omega
  have paths := high_min_all_paths_gap notTrace (by omega) cap half
  have missing := deletion_gap w p hp paths
  by_contra! independent
  have small := independent_omits_at_most_two w p hp longest independent (by omega) cap
  omega


#print axioms critical_fixed
end Graph189CompletionLinkedFour
