import Bounds

namespace Erdos1082
open Finset

def Class.parameter : Class → Option Radical
  | .forced u _ => some u
  | _ => none

def Class.available (u : Option Radical) : Class → Option Point
  | .impossible => none
  | .free p => some p
  | .forced v p => if u = some v then some p else none

def availablePoints (cs : List Class) (u : Option Radical) : List Point :=
  (cs.filterMap (Class.available u)).eraseDups

/-- Bound extensions by encoded parameter buckets. A checked polynomial inverse
separates distinct representations of the remaining distance. -/
theorem count_of_cover (cs : List Class) (k : ℕ) (s z t : ℝ)
    (hs : s^2 = 3) (hz : z^3 = 3*z+1)
    (sep : ∀ u v : Radical, u ≠ v → some u ∈ cs.map Class.parameter →
      some v ∈ cs.map Class.parameter → verifiesNonzero (u.sub v))
    (boundFree : (availablePoints cs none).length ≤ k)
    (boundForced : ∀ u, some u ∈ cs.map Class.parameter →
      (availablePoints cs (some u)).length ≤ k)
    (X : Finset (ℝ × ℝ))
    (cover : ∀ p ∈ X,
      (∃ q, Class.free q ∈ cs ∧ p = Point.eval q s z) ∨
      (∃ u q, Class.forced u q ∈ cs ∧ t = u.eval s z ∧ p = Point.eval q s z)) :
    X.card ≤ k := by
  classical
  let uses (u : Radical) := some u ∈ cs.map Class.parameter ∧ t = u.eval s z
  let u := if h : ∃ u, uses u then some (Classical.choose h) else none
  have same {v : Radical} (hv : uses v) : u = some v := by
    have he : ∃ u, uses u := ⟨v, hv⟩
    let w := Classical.choose he
    have hw : uses w := Classical.choose_spec he
    have equiv : w = v := by
      by_contra hn
      have hne := nonzero_sound _ s z hs hz (sep w v hn hw.1 hv.1)
      apply hne
      rw [Radical.eval_sub, ← hw.2, ← hv.2, sub_self]
    dsimp [u]
    rw [dif_pos he]
    exact congrArg some equiv
  have hlength : (availablePoints cs u).length ≤ k := by
    dsimp [u]
    split
    · rename_i h
      exact boundForced _ (Classical.choose_spec h).1
    · exact boundFree
  have hsub : X ⊆ (availablePoints cs u).toFinset.image (Point.eval · s z) := by
    intro p hp
    apply mem_image.mpr
    rcases cover p hp with ⟨q, hq, rfl⟩ | ⟨v, q, hq, hv, rfl⟩
    · refine ⟨q, ?_, rfl⟩
      simp only [List.mem_toFinset, availablePoints, List.mem_eraseDups, List.mem_filterMap]
      exact ⟨.free q, hq, rfl⟩
    · refine ⟨q, ?_, rfl⟩
      simp only [List.mem_toFinset, availablePoints, List.mem_eraseDups, List.mem_filterMap]
      refine ⟨.forced v q, hq, ?_⟩
      have hm : some v ∈ cs.map Class.parameter := List.mem_map.mpr ⟨.forced v q, hq, rfl⟩
      simp [Class.available, same ⟨hm, hv⟩]
  exact (card_le_card hsub).trans (card_image_le.trans
    ((List.toFinset_card_le _).trans hlength))

def parameters (cs : List Class) : List Radical :=
  (cs.filterMap Class.parameter).eraseDups

theorem mem_parameters {cs : List Class} {u : Radical} :
    u ∈ parameters cs ↔ some u ∈ cs.map Class.parameter := by
  simp [parameters, List.mem_filterMap, List.mem_map]

def checkCounts (cs : List Class) (k : ℕ) : Bool :=
  decide ((availablePoints cs none).length ≤ k) &&
  (parameters cs).all fun u =>
    decide ((availablePoints cs (some u)).length ≤ k) &&
    (parameters cs).all fun v =>
      if u = v then true else verifiesNonzero (u.sub v)

theorem count_of_cover_checked (cs : List Class) (k : ℕ) (s z t : ℝ)
    (hs : s^2 = 3) (hz : z^3 = 3*z+1) (hcheck : checkCounts cs k)
    (X : Finset (ℝ × ℝ))
    (cover : ∀ p ∈ X,
      (∃ q, Class.free q ∈ cs ∧ p = Point.eval q s z) ∨
      (∃ u q, Class.forced u q ∈ cs ∧ t = u.eval s z ∧ p = Point.eval q s z)) :
    X.card ≤ k := by
  obtain ⟨hf, hl⟩ := Bool.and_eq_true_iff.mp hcheck
  apply count_of_cover cs k s z t hs hz ?_ (of_decide_eq_true hf) ?_ X cover
  · intro u v huv hu hv
    have h := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hl u (mem_parameters.mpr hu))).2
    simpa [if_neg huv] using List.all_eq_true.mp h v (mem_parameters.mpr hv)
  · intro u hu
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hl u (mem_parameters.mpr hu))).1

end Erdos1082

#print axioms Erdos1082.count_of_cover
