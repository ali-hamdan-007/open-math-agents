import Graph189ExteriorSpacing
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

def crossIndices (A B : Finset ℕ) : Finset ℕ :=
  (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) ∪ (B \ A)

private theorem card_crossIndices (A B : Finset ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i) :
    (crossIndices A B).card = A.card+B.card := by
  have dis₁ : Disjoint (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1)) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    obtain ⟨i,hi,ei⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj,ej⟩ := Finset.mem_image.mp hw
    have := positive i hi
    rcases separated i hi j (Finset.mem_inter.mp hj).2 with h | h | h <;> omega
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      rcases separated i hi t hb with h | h | h <;> omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      rcases separated i (Finset.mem_inter.mp hi).1 t hb with h | h | h <;> omega
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
  rw [crossIndices,Finset.card_union_of_disjoint dis₂,Finset.card_union_of_disjoint dis₁,
    Finset.card_image_of_injOn inj,Finset.card_image_of_injective _
      (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)]
  omega

noncomputable def contactPositions (p : G.Walk x y) (a : V) : Finset ℕ := by
  classical
  exact (Finset.range p.support.length).filter (fun i => G.Adj (p.getVert i) a)

theorem mem_contactPositions (p : G.Walk x y) (a : V) (i : ℕ) :
    i∈contactPositions p a ↔ i < p.support.length ∧ G.Adj (p.getVert i) a := by
  classical
  simp [contactPositions]

theorem get_at (p : G.Walk x y) {i : ℕ} (hi : i < p.support.length) :
    p.support[i] = p.getVert i := (p.getVert_eq_support_getElem (by
      have := p.length_support
      omega)).symm

theorem two_step_metric {a b z : V} (different : a≠b) (missing : ¬G.Adj a b)
    (az : G.Adj a z) (bz : G.Adj b z) : G.dist a b = 2 := by
  have h := SimpleGraph.edist_eq_two_iff.mpr ⟨different,missing,⟨z,az,bz⟩⟩
  simp [SimpleGraph.dist,h]

/-- Both contact populations are charged to distinct vertices at genuine ambient
distance two from the first exterior vertex. The longest path is arbitrary. -/
theorem cross_positions_le_path_shell [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact omitted_contact_internal p hp longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) : i=j ∨ i+3 ≤ j ∨ j+3 ≤ i := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · exact Or.inr (Or.inl (adjacent_omitted_contact_spacing p hp longest ha hb ab
        ⟨i,ri⟩ ⟨j,rj⟩ lt (by simpa [get_at] using ci) (by simpa [get_at] using cj)))
    · exact Or.inl same
    · exact Or.inr (Or.inr (adjacent_omitted_contact_spacing p hp longest hb ha ab.symm
        ⟨j,rj⟩ ⟨i,ri⟩ gt (by simpa [get_at] using cj) (by simpa [get_at] using ci)))
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
  rw [Finset.card_image_of_injOn inj,card_crossIndices A B (fun i h => (inside i h).1) separate] at bound
  exact bound

#print axioms cross_positions_le_path_shell
end Graph189ExteriorGap
