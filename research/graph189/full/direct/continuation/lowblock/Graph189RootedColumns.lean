import Graph189RootedSplice
import Graph189SingleExteriorShift
import Graph189ExteriorDegree
namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

private theorem card_cross_rooted (A B : Finset ℕ) (r : ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨
      (i+2=j ∧ i+1=r) ∨ (j+2=i ∧ j+1=r)) :
    A.card+B.card ≤ (crossIndices A B).card+1 := by
  have ov : (A.image (fun i => i-1)) ∩ ((A∩B).image (fun i => i+1)) ⊆ {r} := by
    intro t ht
    obtain ⟨ht,hw⟩ := Finset.mem_inter.mp ht
    apply Finset.mem_singleton.mpr
    obtain ⟨i,hi,ei⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj,ej⟩ := Finset.mem_image.mp hw
    have := positive i hi
    rcases separated i hi j (Finset.mem_inter.mp hj).2 with h | h | h | ⟨h,w⟩ | ⟨h,w⟩ <;> omega
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      rcases separated i hi t hb with h | h | h | ⟨h,w⟩ | ⟨h,w⟩ <;> omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      rcases separated i (Finset.mem_inter.mp hi).1 t hb with h | h | h | ⟨h,w⟩ | ⟨h,w⟩ <;> omega
  have inj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj heq
    change i-1=j-1 at heq
    have := positive i hi
    have := positive j hj
    omega
  have cover : (B \ A) ∪ (A∩B) = B := by ext t; simp; tauto
  have dis : Disjoint (B \ A) (A∩B) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).1)
  have hc := Finset.card_union_of_disjoint dis
  rw [cover] at hc
  have upper : ((A.image (fun i => i-1)) ∩ ((A∩B).image (fun i => i+1))).card ≤ 1 := by
    simpa using Finset.card_le_card ov
  have sum := Finset.card_union_add_card_inter (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1))
  rw [Finset.card_image_of_injOn inj,Finset.card_image_of_injective _
    (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)] at sum
  rw [crossIndices,Finset.card_union_of_disjoint dis₂]
  omega


private theorem own_spacing (p : G.Walk x y) (hp : p.IsPath) {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a : V} (off : a∉p.support) {i j : ℕ} (hi : i∈contactPositions p a) (hj : j∈contactPositions p a)
    (lt : i<j) : i+2≤j := by
  obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
  obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
  have h := rooted_short_detour p hp on longest ri rj lt (Walk.nil : G.Walk a a) (by simp)
    (by simpa [List.disjoint_left] using off) ci cj.symm
  rcases h with yes|no
  · change i+1+1 ≤ j at yes
    omega
  · exact no.1

private theorem cross_spacing (p : G.Walk x y) (hp : p.IsPath) {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) {i j : ℕ}
    (hi : i∈contactPositions p a) (hj : j∈contactPositions p b) (lt : i<j) :
    i+3≤j ∨ (i+2=j ∧ root=p.getVert (i+1)) := by
  obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
  obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have dis : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl|rfl
    · exact ha h
    · exact hb h
  rcases rooted_short_detour p hp on longest ri rj lt q hq dis ci cj.symm with ok|exception
  · exact Or.inl (by simpa [q] using ok)
  · by_cases h : i+3≤j
    · exact Or.inl h
    · have low := exception.1
      have eq : i+2=j := by omega
      exact Or.inr ⟨eq,exception.2 eq.symm⟩

theorem rooted_cross_positions [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card+1 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact rooted_contact_internal p hp on longest ha i hi hc
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j :=
    own_spacing p hp on longest ha hi hj lt
  obtain ⟨index,valid,eqRoot⟩ := List.mem_iff_getElem.mp on
  have pinned : p.getVert index=root := (get_at p valid).symm.trans eqRoot
  have atRoot (i : ℕ) (range : i < p.support.length) (hi : root=p.getVert i) : i=index :=
    hp.getVert_injOn (by change i≤p.length; have := p.length_support; omega)
      (by change index≤p.length; have := p.length_support; omega) (hi.symm.trans pinned.symm)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) : i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨
      (i+2=j ∧ i+1=index) ∨ (j+2=i ∧ j+1=index) := by
    rcases lt_trichotomy i j with lt|eq|gt
    · rcases cross_spacing p hp on longest ha hb ab hi hj lt with h|⟨h,rootAt⟩
      · exact Or.inr (Or.inl h)
      · have limit := ((mem_contactPositions p b j).mp hj).1
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h,atRoot _ (by omega) rootAt⟩)))
    · exact Or.inl eq
    · rcases cross_spacing p hp on longest hb ha ab.symm hj hi gt with h|⟨h,rootAt⟩
      · exact Or.inr (Or.inr (Or.inl h))
      · have limit := ((mem_contactPositions p a i).mp hi).1
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h,atRoot _ (by omega) rootAt⟩)))
  have shell (i : ℕ) (hi : i∈crossIndices A B) : i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
    have different (j : ℕ) : a≠p.getVert j := fun eq => ha (eq ▸ p.getVert_mem_support j)
    have ls := p.length_support
    have via (i j : ℕ) (hpi : i < p.support.length) (hj : j∈A) (no : i∉A)
        (ij : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i)=2 := by
      have hc := ((mem_contactPositions p a j).mp hj).2
      exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hpi,h.symm⟩)) hc.symm ij
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨pos,back⟩ := inside j hj
        have inrange : j-1 < p.support.length := by omega
        refine ⟨inrange,via (j-1) j inrange hj (fun hi => ?_) ?_⟩
        · have aux := own (j-1) j hi hj (by omega)
          omega
        · have edge := p.adj_getVert_succ (i := j-1) (by omega)
          rwa [show j-1+1=j by omega] at edge
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have jA := (Finset.mem_inter.mp hj).1
        obtain ⟨_,back⟩ := inside j jA
        refine ⟨back,via (j+1) j back jA (fun hi => ?_) ?_⟩
        · have aux := own j (j+1) jA hi (by omega)
          omega
        · exact (p.adj_getVert_succ (i := j) (by omega)).symm
    · obtain ⟨hB,hA⟩ := Finset.mem_sdiff.mp h
      obtain ⟨ri,ci⟩ := (mem_contactPositions p b i).mp hB
      exact ⟨ri,two_step_metric (different _) (fun h => hA ((mem_contactPositions p a i).mpr ⟨ri,h.symm⟩)) ab ci⟩
  have inj : Set.InjOn p.getVert ((crossIndices A B : Finset ℕ) : Set ℕ) := by
    intro i hi j hj same
    exact hp.getVert_injOn (by change i ≤ p.length; have := (shell i hi).1; have := p.length_support; omega)
      (by change j ≤ p.length; have := (shell j hj).1; have := p.length_support; omega) same
  have incl : (crossIndices A B).image p.getVert ⊆ p.support.toFinset.filter (fun z => G.dist a z=2) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),(shell i hi).2⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injOn inj] at bound
  exact (card_cross_rooted A B index (fun i h => (inside i h).1) separate).trans (by omega)

theorem rooted_single_shift [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact rooted_contact_internal p hp on longest ha i ri ci
  have spaced (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i<j) : i+2≤j :=
    own_spacing p hp on longest ha hi hj lt
  let B := A.image (fun i => i-1)
  let W := insert (m+1) B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_insert.mp hi with rfl|h
    · have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have maxoutside : m+1 ∉ B := by
    intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have lim : i ≤ m := Finset.le_max' _ _ hi
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = insert (m+1) B from rfl,card_insert_of_notMem maxoutside,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj] at count
  exact count

#print axioms rooted_cross_positions
#print axioms rooted_single_shift
end Graph189RootedSplice
