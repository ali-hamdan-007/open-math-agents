import Graph189ProtectedIntervals
import Graph189ExteriorDegree

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- Adding an omitted neighbor at a path endpoint preserves the protected vertex. -/
theorem protected_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  constructor
  · by_contra! zero
    have le : i ≤ t := by change i.val ≤ t.val; omega
    have bound := protected_prefix_of_detour p hp t longest i le q hq hd contact.symm
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega
  · by_contra! last
    have le : t ≤ i := by change t.val ≤ i.val; have := t.isLt; omega
    have bound := protected_suffix_of_detour p hp t longest i le q hq hd contact
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega

/-- The contacts of an omitted vertex cannot occupy two adjacent path positions. -/
theorem protected_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i<j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  by_contra! close
  have le : j ≤ t ∨ t ≤ i := by
    change j.val ≤ t.val ∨ t.val ≤ i.val
    change i.val < j.val at ordered
    omega
  have h := protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  simp only [q,Walk.support_nil,List.length_singleton] at h
  omega

/-- Cross contacts at distance two must straddle the protected position. -/
theorem protected_cross_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i<j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val ∨ i.val+1=t.val ∧ t.val+1=j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  by_cases le : j ≤ t ∨ t ≤ i
  · left
    exact protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  · change ¬(j.val ≤ t.val ∨ t.val ≤ i.val) at le
    omega


/-- Only the protected position can occur twice in the shifted-contact count. -/
private theorem card_protected_cross (A B : Finset ℕ) (t : ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t ∧ t+1=j) ∨ (j+1=t ∧ t+1=i)) :
    A.card+B.card ≤ (crossIndices A B).card+1 := by
  have overlap : ((A.image (fun i => i-1)) ∩ ((A∩B).image (fun i => i+1))) ⊆ {t} := by
    intro v hv
    obtain ⟨i,hi,ei⟩ := mem_image.mp (mem_inter.mp hv).1
    obtain ⟨j,hj,ej⟩ := mem_image.mp (mem_inter.mp hv).2
    have := positive i hi
    have := separated i hi j (mem_inter.mp hj).2
    apply mem_singleton.mpr
    omega
  have loss := Finset.card_le_card overlap
  rw [card_singleton] at loss
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      have := separated i hi t hb
      omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := separated i (Finset.mem_inter.mp hi).1 t hb
      omega
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
  have total := card_union_add_card_inter (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1))
  rw [card_image_of_injOn inj,card_image_of_injective _
    (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)] at total
  rw [crossIndices,card_union_of_disjoint dis₂]
  omega

theorem protected_cross_indices [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    ((contactPositions p a).card + (contactPositions p b).card ≤
      (crossIndices (contactPositions p a) (contactPositions p b)).card+1) ∧
      ∀ i ∈ crossIndices (contactPositions p a) (contactPositions p b),
        i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact protected_contact_internal p hp t longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) :
      i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t.val ∧ t.val+1=j) ∨ (j+1=t.val ∧ t.val+1=i) := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · have h := protected_cross_spacing p hp t longest ha hb ab ⟨i,ri⟩ ⟨j,rj⟩ lt
        (by simpa [get_at] using ci) (by simpa [get_at] using cj)
      change i+3 ≤ j ∨ i+1=t.val ∧ t.val+1=j at h
      tauto
    · exact Or.inl same
    · have h := protected_cross_spacing p hp t longest hb ha ab.symm ⟨j,rj⟩ ⟨i,ri⟩ gt
        (by simpa [get_at] using cj) (by simpa [get_at] using ci)
      change j+3 ≤ i ∨ j+1=t.val ∧ t.val+1=i at h
      tauto
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
  exact ⟨card_protected_cross A B t.val (fun i h => (inside i h).1) separate,shell⟩

theorem protected_cross_positions [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card+1 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  obtain ⟨count,shell⟩ := protected_cross_indices p hp t longest ha hb ab
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
  exact count.trans (Nat.add_le_add_right bound 1)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every neighbor of b that is off p and distinct from a either lies in the
common external neighborhood or costs an additional, non-path distance-two slot. -/
theorem protected_exterior_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+2+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := protected_cross_positions p hp t longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card+1 at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+2+C.card
  omega

/-- The protected position allows one extra unit in the cross-contact degree bound. -/
theorem protected_cross_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := protected_exterior_contact_degree p hp t longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+2+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+1+(A \ P).card
  omega

/-- A high exterior neighbor forces half the ambient degree, rounded down,
to remain outside the protected path. -/
theorem protected_half_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree b) :
    G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1 := by
  have cross := protected_cross_contact_degree p hp t longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1
  omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- The predecessors and the last successor still give distinct distance-two
witnesses when a path vertex is protected. -/
theorem protected_single_shell (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact protected_contact_internal p hp t longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
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

end Graph189ExteriorGap

#print axioms Graph189ExteriorGap.protected_half_degree
#print axioms Graph189ExteriorGap.protected_single_shell
