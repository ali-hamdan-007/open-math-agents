import Graph189DoubleExteriorShift

namespace Graph189ExteriorGap
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- At contacts with pairwise spacing at least three, every predecessor and
every successor charge different vertices of the original path. -/
theorem double_shift_positions (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (wide : ∀ i∈contactPositions p a, ∀ j∈contactPositions p a, i<j → i+3≤j) :
    let A := contactPositions p a
    let W := A.image (fun i => i+1) ∪ A.image (fun i => i-1)
    W.card = 2*A.card ∧ ∀ i ∈ W, i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
  classical
  let A := contactPositions p a
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact omitted_contact_internal p hp longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let F := A.image (fun i => i+1)
  let W := F ∪ B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_union.mp hi with h|h
    · obtain ⟨m,hm,rfl⟩ := mem_image.mp h
      have ht := (internal m hm).2
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
  have disjoint : Disjoint F B := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,hi,ei⟩ := mem_image.mp hv
    obtain ⟨j,hj,ej⟩ := mem_image.mp hw
    have := (internal j hj).1
    change i+1=v at ei
    change j-1=v at ej
    have := wide i hi j hj (by omega)
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  refine ⟨?_,valid⟩
  change (F ∪ B).card = 2*A.card
  rw [card_union_of_disjoint disjoint,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj,
    show F = A.image (fun i => i+1) from rfl,card_image_of_injective _ (show Function.Injective (fun i : ℕ => i+1) by
      intro i j eq; change i+1=j+1 at eq; omega)]
  omega

#print axioms double_shift_positions
end Graph189ExteriorGap
