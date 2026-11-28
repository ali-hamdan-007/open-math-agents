import Graph189CompletionCertificate

namespace Graph189Completion
open SimpleGraph Finset
open scoped Classical
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transfer a witnessed path without changing its vertex count. -/
theorem HasPath.mapIso {t : ℕ} (path : HasPath G t) (e : G≃g H) : HasPath H t := by
  obtain ⟨a,b,P,hp,hlen⟩ := path
  refine ⟨_,_,P.map e.toHom,hp.map e.injective,?_⟩
  simpa only [Walk.length_support,Walk.length_map] using hlen

/-- Restrict an original vertex labeling after deleting corresponding vertices. -/
def deleteIso (e : G≃g H) (v : V) :
    G.induce {u | u≠v} ≃g H.induce {w | w≠e v} := by
  apply e.induce
  refine ⟨?_,e.injective.injOn,?_⟩
  · intro u hu same
    exact hu (e.injective same)
  · intro w hw
    refine ⟨e.symm w,?_,e.apply_symm_apply w⟩
    intro same
    apply hw
    rw [←same,e.apply_symm_apply]

private theorem edist_map_le (f : G→g H) (a b : V) : H.edist (f a) (f b)≤G.edist a b := by
  change H.edist (f a) (f b)≤⨅ P : G.Walk a b, (P.length : ℕ∞)
  apply le_iInf
  intro P
  simpa only [Walk.length_map] using (P.map f).edist_le

theorem dist_mapIso (e : G≃g H) (a b : V) : H.dist (e a) (e b)=G.dist a b := by
  have fwd := edist_map_le e.toHom a b
  have rev := edist_map_le e.symm.toHom (e a) (e b)
  have eq : H.edist (e a) (e b)=G.edist a b := le_antisymm fwd (by simpa using rev)
  simp only [SimpleGraph.dist,eq]

variable [Fintype V] [Fintype W]

theorem distEven_mapIso (e : G≃g H) (v : V) : H.distEven (e v)=G.distEven v := by
  classical
  simp only [SimpleGraph.distEven,Finset.card_filter]
  rw [←e.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  rw [show H.dist (e v) (e.toEquiv w)=G.dist v w from dist_mapIso e v w]

/-- All four feasibility conditions survive an arbitrary finite relabeling.
The floor correspondence permits different presentations of the low vertex. -/
theorem Feasible.mapIso {z : V} {f d k : ℕ} {floor : V→ℕ} {floor' : W→ℕ}
    (actual : Feasible G z f d k floor) (e : G≃g H)
    (floors : ∀ v, floor' (e v)=floor v) : Feasible H (e z) f d k floor' := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro (long|long)
    · exact actual.short (Or.inl (long.mapIso e.symm))
    · exact actual.short (Or.inr (long.mapIso (deleteIso e z).symm))
  · intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [floors,e.degree_eq]
    exact actual.degrees v
  · intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    exact (deleteIso e v).connected_iff.mp (actual.connected v)
  · intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [distEven_mapIso]
    exact actual.even v

/-- A rejection on finite labels excludes the original graph as soon as
its labeled copy lies between the certified lower and upper graph. -/
theorem Rejection.excludes_isomorphic {L U : SimpleGraph W} {z : V} {f d k : ℕ}
    {floor : V→ℕ} {floor' : W→ℕ} (e : G≃g H) (floors : ∀ v, floor' (e v)=floor v)
    (tree : Rejection (e z) f d k floor' L U) (lower : L≤H) (upper : H≤U) :
    ¬Feasible G z f d k floor := fun actual => tree.sound (actual.mapIso e floors) lower upper

/-- Apply a finite-label certificate directly to G through its chosen
enumeration, without constructing a separate graph isomorphism by hand. -/
theorem Rejection.excludes_relabel {n : ℕ} (label : V≃Fin n) {L U : SimpleGraph (Fin n)}
    {z : V} {f d k : ℕ} {floor : V→ℕ} {floor' : Fin n→ℕ}
    (floors : ∀ v, floor' (label v)=floor v)
    (tree : Rejection (label z) f d k floor' L U) (lower : L≤G.map label)
    (upper : G.map label≤U) : ¬Feasible G z f d k floor :=
  Rejection.excludes_isomorphic (SimpleGraph.Iso.map label G) floors tree lower upper

end Graph189Completion
#print axioms Graph189Completion.Feasible.mapIso
#print axioms Graph189Completion.Rejection.excludes_isomorphic

#print axioms Graph189Completion.Rejection.excludes_relabel
