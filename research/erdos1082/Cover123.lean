import Rows123

namespace Erdos1082

def expected123 (positive : Bool) (n : ℕ) : Class :=
  ((rows123 positive).lookup n).getD .impossible

def checkBlock123 (positive : Bool) (offset width : ℕ) : Bool :=
  (List.range width).all fun i =>
    let n := offset + i
    decide (check (form123 positive) (small123 positive) n = some (expected123 positive n))

theorem checkedBlock123 {positive : Bool} {offset width i : ℕ}
    (h : checkBlock123 positive offset width) (hi : i < width) :
    check (form123 positive) (small123 positive) (offset + i) =
      some (expected123 positive (offset + i)) := by
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))

theorem expected123_mem (positive : Bool) (n : ℕ) :
    expected123 positive n = .impossible ∨ expected123 positive n ∈ (rows123 positive).map Prod.snd := by
  unfold expected123
  generalize hh : (rows123 positive).lookup n = oc
  cases oc with
  | none => exact Or.inl rfl
  | some c =>
    right
    apply List.mem_map.mpr
    refine ⟨(n,c), ?_, rfl⟩
    obtain ⟨l₁, l₂, hlist, _⟩ := List.lookup_eq_some_iff.mp hh
    rw [hlist]
    simp

open Finset in
theorem bound_of_code123 (positive : Bool)
    (verified : ∀ n < 1024,
      check (form123 positive) (small123 positive) n = some (expected123 positive n))
    (s z t : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3*z+1)
    (points : Finset (ℝ × ℝ))
    (hpoint : ∀ p ∈ points, ∃ n < 1024,
      let P := system (form123 positive) (small123 positive) (decode n)
      p = (P.x.eval s z t, P.y.eval s z t) ∧ P.Satisfies s z t)
    (hbase : ∀ p ∈ points, ∀ q ∈ base (form123 positive), p ≠ Point.eval q s z)
    (hsmall : ∀ q ∈ small123 positive, t ≠ q.eval s z) :
    points.card ≤ 4 := by
  apply count_of_cover_checked _ _ s z t hs hz (counts123 positive) points
  intro p hp
  obtain ⟨n, hn, hcoords, hsys⟩ := hpoint p hp
  let P := system (form123 positive) (small123 positive) (decode n)
  have hb : ∀ q ∈ base (form123 positive),
      P.x.eval s z t ≠ q.1.eval s z ∨ P.y.eval s z t ≠ q.2.eval s z := by
    intro q hq
    by_contra! he
    exact hbase p hp q hq (hcoords.trans (Prod.ext he.1 he.2))
  have hc := classify_sound P _ _ s z t hs hz hsys hb hsmall _ (verified n hn)
  have hm := expected123_mem positive n
  generalize he : expected123 positive n = C at hc hm
  cases C with
  | impossible => exact hc.elim
  | free q => exact Or.inl ⟨q, hm.resolve_left (by simp), hcoords.trans (Prod.ext hc.1 hc.2)⟩
  | forced u q => exact Or.inr ⟨u, q, hm.resolve_left (by simp), hc.1,
      hcoords.trans (Prod.ext hc.2.1 hc.2.2)⟩

theorem norm_form123 (positive : Bool) (s z : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3*z+1) :
    ((form123 positive).1.1.eval s z)^2 + ((form123 positive).1.2.eval s z)^2 = 1 ∧
    ((form123 positive).2.1.eval s z)^2 + ((form123 positive).2.2.eval s z)^2 = 1 := by
  have hS : sqrtThree.eval s z = s := by simp [sqrtThree, Radical.eval]
  cases positive <;>
    simp [form123, Radical.eval_mul, hs, hz, rc, hS] <;>
    linear_combination hs/4

theorem label123_exists (positive : Bool) (s z t r : ℝ)
    (hr : r = t ∨ ∃ v ∈ (small123 positive), r = v.eval s z) :
    ∃ k < 4, (label (small123 positive) k).eval s z t = r := by
  rcases hr with rfl | ⟨v, hv, rfl⟩
  · exact ⟨3, by decide, by simp [label, small123]⟩
  · simp only [small123, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨0, by decide, by simp [label, small123]⟩
    · exact ⟨1, by decide, by simp [label, small123]⟩
    · exact ⟨2, by decide, by simp [label, small123]⟩

open Finset in
theorem bound_actual123 (positive : Bool) (verified : ∀ n < 1024,
      check (form123 positive) (small123 positive) n = some (expected123 positive n))
    (s z t : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3*z+1)
    (points : Finset (ℝ × ℝ))
    (hpoint : ∀ p ∈ points, ∀ q ∈ base (form123 positive),
      distanceSq p (Point.eval q s z) = t ∨
        ∃ v ∈ (small123 positive), distanceSq p (Point.eval q s z) = v.eval s z)
    (hbase : ∀ p ∈ points, ∀ q ∈ base (form123 positive), p ≠ Point.eval q s z)
    (hsmall : ∀ q ∈ (small123 positive), t ≠ q.eval s z) :
    points.card ≤ 4 := by
  apply bound_of_code123 positive verified s z t hs hz points ?_ hbase hsmall
  rintro ⟨a,b⟩ hp
  let Q (i : ℕ) : Point := (base (form123 positive))[i]?.getD origin
  have hQ (i : ℕ) (hi : i < 5) : Q i ∈ base (form123 positive) := by
    have hh : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [Q, base]
  have hc (i : ℕ) (hi : i < 5) := label123_exists positive s z t _ (hpoint _ hp _ (hQ i hi))
  have hchoose : ∀ i : ℕ, ∃ k, k < 4 ∧ (i < 5 →
      (label (small123 positive) k).eval s z t = distanceSq (a,b) (Point.eval (Q i) s z)) := by
    intro i
    by_cases hi : i < 5
    · obtain ⟨k, hk, he⟩ := hc i hi
      exact ⟨k, hk, fun _ => he⟩
    · exact ⟨0, by decide, fun h => (hi h).elim⟩
  choose d hd he using hchoose
  obtain ⟨n, hn, hdec⟩ := encode d (fun i _ => hd i)
  have hdist (i : ℕ) (hi : i < 5) :
      (label (small123 positive) (decode n i)).eval s z t = distanceSq (a,b) (Point.eval (Q i) s z) := by
    rw [hdec i hi]
    exact he i hi
  have h0 := (hdist 0 (by decide)).symm
  have h1 := (hdist 1 (by decide)).symm
  have h2 := (hdist 2 (by decide)).symm
  have h3 := (hdist 3 (by decide)).symm
  have h4 := (hdist 4 (by decide)).symm
  have hS : sqrtThree.eval s z = s := by simp [sqrtThree, Radical.eval]
  have hu := norm_form123 positive s z hs hz
  have h := system_sound (form123 positive) (small123 positive) (decode n) s z t a b hs hz
    (by simpa [Q, base, distanceSq, origin, Point.eval, rc] using h0)
    (by simpa [Q, base, distanceSq, left, Point.eval, rc, Radical.eval_mul, hs, hz,
      hS, div_eq_mul_inv, sub_neg_eq_add] using h1)
    (by simpa [Q, base, distanceSq, right, Point.eval, rc, Radical.eval_mul, hs, hz,
      hS, div_eq_mul_inv] using h2)
    (by simpa [Q, base] using h3) (by simpa [Q, base] using h4) hu.1 hu.2
  exact ⟨n, hn, (Prod.ext h.1 h.2.1).symm, h.2.2⟩

end Erdos1082

#print axioms Erdos1082.bound_of_code123
