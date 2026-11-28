import Graph189SixCycleExtra

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189FiveCycleRing
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A subset with no successive vertices on the five-cycle has size
at most two. Its complement contains a successive pair. -/
theorem independent : ∀ S : Finset (Fin 5), (∀ i∈S, i+1∉S) →
    S.card≤2 ∧ ∃ i : Fin 5, i∉S ∧ i+1∉S := by decide

omit [DecidableEq V] in
def seq {r : V} (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) : Fin 5↪V where
  toFun := fun i => C.getVert i.val
  inj' := by
    intro i j eq
    apply Fin.ext
    exact hc.getVert_injOn' (by change i.val≤C.length-1; omega)
      (by change j.val≤C.length-1; omega) eq

omit [DecidableEq V] in
theorem edge {r : V} (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (i : Fin 5) :
    s(seq C hc five i, seq C hc five (i+1))∈C.edges := by
  apply C.mk_mem_edges_iff_exists.mpr
  refine ⟨i.val,by omega,?_⟩
  have mod : (i+1).val=(i.val+1)%5 := rfl
  change s(C.getVert i.val,C.getVert (i.val+1))=s(C.getVert i.val,C.getVert (i+1).val)
  rw [mod]
  by_cases h : i.val+1<5
  · rw [Nat.mod_eq_of_lt h]
  · have eq : i.val+1=5 := by omega
    have last : C.getVert 5=r := five ▸ C.getVert_length
    rw [eq,Nat.mod_self,Walk.getVert_zero,last]

theorem covers {r : V} (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) :
    (univ : Finset (Fin 5)).map (seq C hc five)=C.support.toFinset := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i,_,rfl⟩ := mem_map.mp hv
    exact List.mem_toFinset.mpr (C.getVert_mem_support i.val)
  · rw [card_map,card_univ,Fintype.card_fin,Graph189SixCycleExtra.cycle_card C hc,five]

variable [Fintype V] [Nontrivial V] [DecidableRel G.Adj]

/-- A vertex outside both the longest path and its exterior five-cycle
has at most two cycle neighbors and misses two successive cycle vertices. -/
theorem outside_neighbors (hcG : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) (conn : 2≤G.vertexConnectivity)
    {a b r : V} (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    {w : V} (wp : w∉p.support) (wc : w∉C.support) :
    (G.neighborFinset w∩C.support.toFinset).card≤2 ∧
    ∃ u v, s(u,v)∈C.edges ∧ ¬G.Adj w u ∧ ¬G.Adj w v := by
  classical
  let f := seq C hc five
  let S := (univ : Finset (Fin 5)).filter (fun i => G.Adj w (f i))
  have safe (i : Fin 5) (hi : i∈S) : i+1∉S := by
    intro hj
    obtain ⟨T,hT,sz,inc⟩ := Graph189SixCycleExtra.insert_on_edge C hc (edge C hc five i) wc
      (mem_filter.mp hi).2 (mem_filter.mp hj).2
    have lim := Graph189SixCycleExtra.five_bound hcG cap degree conn p hp mx T hT (by
      intro v hv
      rcases inc _ hv with rfl|h
      · exact wp
      · exact off _ h)
    omega
  obtain ⟨two,i,lo,hi⟩ := independent S safe
  have inside : G.neighborFinset w∩C.support.toFinset⊆S.map f := by
    intro v hv
    obtain ⟨dv,vc⟩ := mem_inter.mp hv
    rw [←covers C hc five] at vc
    obtain ⟨j,_,rfl⟩ := mem_map.mp vc
    exact mem_map.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,(G.mem_neighborFinset _ _).mp dv⟩,rfl⟩
  have bound := card_le_card inside
  rw [card_map] at bound
  exact ⟨bound.trans two,f i,f (i+1),edge C hc five i,
    fun h => lo (mem_filter.mpr ⟨mem_univ _,h⟩),fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)⟩

#print axioms outside_neighbors
end Graph189FiveCycleRing
