import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graph189EndpointCut

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- When every distance-two vertex of a marked endpoint lies in the marked set,
     adjacency to that endpoint cannot change along an edge outside the set. -/
theorem transfer_along_edge {R : Set V} {e b c : V}
    (he : e ∈ R) (hc : c ∉ R) (sat : ∀ w, G.dist e w = 2 → w ∈ R)
    (heb : G.Adj e b) (hbc : G.Adj b c) : G.Adj e c := by
  by_contra missing
  have hne : e ≠ c := fun h => hc (h ▸ he)
  have htwo : G.edist e c = 2 := SimpleGraph.edist_eq_two_iff.mpr
    ⟨hne, missing, b, heb, hbc.symm⟩
  have hdist : G.dist e c = 2 := by simp [SimpleGraph.dist, htwo]
  exact hc (sat c hdist)

/-- A vertex outside the marked set missing all marked neighbors forces a cut
     at the sole possible exception to distance-two saturation. -/
theorem disconnected_delete_of_saturated_endpoints {R : Set V} {z x e : V}
    (hz : z ∈ R) (hx : x ∉ R) (he : e ∈ R) (hez : e ≠ z)
    (absent : ∀ u ∈ R, u ≠ z → ¬ G.Adj u x)
    (sat : ∀ u ∈ R, u ≠ z → ∀ w, G.dist u w = 2 → w ∈ R) :
    ¬ (G.induce {v | v ≠ z}).Connected := by
  intro connected
  let S : Set {v : V // v ≠ z} :=
    {b | b.val ∉ R ∧ ∀ u ∈ R, u ≠ z → ¬ G.Adj u b.val}
  have hxz : x ≠ z := fun h => hx (h ▸ hz)
  let x' : {v : V // v ≠ z} := ⟨x,hxz⟩
  let e' : {v : V // v ≠ z} := ⟨e,hez⟩
  have xin : x' ∈ S := ⟨hx,absent⟩
  have eout : e' ∉ S := fun h => h.1 he
  obtain ⟨P⟩ := connected x' e'
  obtain ⟨d, _, hin, hout⟩ := P.exists_boundary_dart S xin eout
  have hbc : G.Adj d.fst.val d.snd.val := d.adj
  have hnot : d.snd.val ∉ R := fun h => hin.2 _ h d.snd.property hbc.symm
  apply hout
  refine ⟨hnot, ?_⟩
  intro u hu huz hut
  exact hin.2 u hu huz (transfer_along_edge hu hin.1 (sat u hu huz) hut hbc.symm)

#print axioms transfer_along_edge
#print axioms disconnected_delete_of_saturated_endpoints

end Graph189EndpointCut
