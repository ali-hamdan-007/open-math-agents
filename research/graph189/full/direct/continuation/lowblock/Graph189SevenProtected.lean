import Graph189ProtectedExteriorSize
import Graph189ProtectedOrder

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189SevenProtected
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- With at most twenty-three vertices, a Hamiltonian deletion of the
unique low vertex extends to traceability at second degree seven. -/
theorem traceable (z : V) (low : G.degree z<G.secondSmallestDegree) (three : 3≤G.degree z)
    (seven : G.secondSmallestDegree=7) (order : Fintype.card V≤23)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {u v : {t : V | t≠z}} (r : (G.induce {t : V | t≠z}).Walk u v) (hr : r.IsHamiltonian) :
    ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  obtain ⟨a,b,p,hp,t,atZ,mx⟩ := exists_longest_through G z
  let E := p.support.toFinsetᶜ
  by_cases empty : E=∅
  · refine ⟨a,b,p,hp.isHamiltonian_iff.mpr ?_⟩
    intro w
    by_contra no
    have mem : w∈E := mem_compl.mpr (fun h => no (List.mem_toFinset.mp h))
    simp [empty] at mem
  have size := protected_size_of_traceable_deletion z (by omega) r hr p hp mx
  change 1+G.degree z+(G.degree z+1)*E.card ≤ _ at size
  have scale := Nat.mul_le_mul_right E.card (by omega : 4≤G.degree z+1)
  have small : E.card≤4 := by omega
  have indexed {x y} (q : G.Walk x y) (hq : q.IsPath) (mem : p.support[t.val]∈q.support) :
      q.length≤p.length := mx q hq (atZ ▸ mem)
  obtain ⟨enough,bound,_⟩ := protected_contact_witness p hp t indexed (atZ ▸ low) cap
    (nonempty_iff_ne_empty.mpr empty) (s:=3) (by decide) (by omega) (by change E.card+3≤_; omega)
  change G.secondSmallestDegree+1-E.card≤E.card at enough
  change (G.secondSmallestDegree+1-E.card+1)*E.card + (G.secondSmallestDegree+1-E.card)≤_ at bound
  have exactSize : E.card=4 := by omega
  rw [exactSize,seven] at bound
  omega

end Graph189SevenProtected
#print axioms Graph189SevenProtected.traceable
