import NormalForms
import Mathlib.Data.Finset.Card

namespace Erdos1082

def allowed157 (n : ℕ) : Bool :=
  n == 180 || n == 382 || n == 540

def checkBlock157 (offset width : ℕ) : Bool :=
  (List.range width).all fun i =>
    let n := offset + i
    allowed157 n || decide (check form157 small157 n = some .impossible)

theorem checkedBlock157 {offset width i : ℕ} (h : checkBlock157 offset width) (hi : i < width) :
    allowed157 (offset + i) = true ∨ check form157 small157 (offset + i) = some .impossible := by
  have he := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at he
  exact he

theorem allowed157_cases {n : ℕ} (h : allowed157 n) :
    n = 180 ∨ n = 382 ∨ n = 540 := by
  simpa [allowed157, Bool.or_eq_true, or_assoc] using h

def Coordinates (n : ℕ) (s z t : ℝ) : ℝ × ℝ :=
  let P := system form157 small157 (decode n)
  (P.x.eval s z t, P.y.eval s z t)

open Finset in
theorem bound157 (verified : ∀ n < 1024, checkBlock157 n 1 = true ∨
      allowed157 n = true ∨ check form157 small157 n = some .impossible)
    (s z t : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3*z+1)
    (points : Finset (ℝ × ℝ))
    (hpoint : ∀ p ∈ points, ∃ n < 1024, p = Coordinates n s z t ∧
      (system form157 small157 (decode n)).Satisfies s z t)
    (hbase : ∀ p ∈ points, ∀ q ∈ base form157, p ≠ Point.eval q s z)
    (hsmall : ∀ q ∈ small157, t ≠ q.eval s z) :
    points.card ≤ 3 := by
  classical
  let codes : Finset ℕ := {180, 382, 540}
  have subset : points ⊆ codes.image (fun n => Coordinates n s z t) := by
    intro p hp
    obtain ⟨n, hn, hcoords, hsys⟩ := hpoint p hp
    have hcheck : allowed157 n = true ∨ check form157 small157 n = some .impossible := by
      rcases verified n hn with hb | h
      · simpa using checkedBlock157 hb (by decide : 0 < 1)
      · exact h
    have hallowed : allowed157 n = true := by
      rcases hcheck with ha | hi
      · exact ha
      · have hb : ∀ q ∈ base form157, (Coordinates n s z t).1 ≠ q.1.eval s z ∨
            (Coordinates n s z t).2 ≠ q.2.eval s z := by
          intro q hq
          by_contra! he
          apply hbase p hp q hq
          rw [hcoords]
          exact Prod.ext he.1 he.2
        exact (classify_sound _ _ _ _ _ _ hs hz hsys hb hsmall .impossible hi).elim
    refine mem_image.mpr ⟨n, ?_, hcoords.symm⟩
    simpa [codes, mem_insert, mem_singleton, or_assoc] using allowed157_cases hallowed
  calc
    points.card ≤ (codes.image (fun n => Coordinates n s z t)).card := card_le_card subset
    _ ≤ codes.card := card_image_le
    _ = 3 := by decide

theorem encode (d : ℕ → ℕ) (hd : ∀ i < 5, d i < 4) :
    ∃ n < 1024, ∀ i < 5, decode n i = d i := by
  have h0 := hd 0 (by decide)
  have h1 := hd 1 (by decide)
  have h2 := hd 2 (by decide)
  have h3 := hd 3 (by decide)
  have h4 := hd 4 (by decide)
  refine ⟨d 0 + 4*d 1 + 16*d 2 + 64*d 3 + 256*d 4, by omega, ?_⟩
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl <;> norm_num [decode] <;> omega

theorem norm_form157 (s z : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3*z+1) :
    (form157.1.1.eval s z)^2 + (form157.1.2.eval s z)^2 = 1 ∧
    (form157.2.1.eval s z)^2 + (form157.2.2.eval s z)^2 = 1 := by
  have heS : sqrtThree.eval s z = s := by simp [sqrtThree, Radical.eval]
  have heZ : cubicRoot.eval s z = z := by simp [cubicRoot, Radical.eval, Cubic.eval, Cubic.constant]
  simp only [form157, Radical.eval_mul _ _ _ _ hs hz, Radical.eval_add, Radical.eval_sub,
    Radical.eval_neg, rc, Radical.eval_constant, heS, heZ]
  push_cast
  constructor <;> linear_combination
    ((2 + z/2 - z^2)^2 / 9) * hs + ((z-1)/3) * hz

theorem label157_exists (s z t r : ℝ)
    (hr : r = t ∨ ∃ v ∈ small157, r = v.eval s z) :
    ∃ k < 4, (label small157 k).eval s z t = r := by
  rcases hr with rfl | ⟨v, hv, rfl⟩
  · exact ⟨3, by decide, by simp [label, small157]⟩
  · simp only [small157, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨0, by decide, by simp [label, small157]⟩
    · exact ⟨1, by decide, by simp [label, small157]⟩
    · exact ⟨2, by decide, by simp [label, small157]⟩

open Finset in
theorem bound_actual157 (verified : ∀ n < 1024,
      allowed157 n = true ∨ check form157 small157 n = some .impossible)
    (s z t : ℝ) (hs : s ^ 2 = 3) (hz : z ^ 3 = 3*z+1)
    (points : Finset (ℝ × ℝ))
    (hpoint : ∀ p ∈ points, ∀ q ∈ base form157,
      distanceSq p (Point.eval q s z) = t ∨
        ∃ v ∈ small157, distanceSq p (Point.eval q s z) = v.eval s z)
    (hbase : ∀ p ∈ points, ∀ q ∈ base form157, p ≠ Point.eval q s z)
    (hsmall : ∀ q ∈ small157, t ≠ q.eval s z) :
    points.card ≤ 3 := by
  apply bound157 (fun n hn => Or.inr (verified n hn)) s z t hs hz points ?_ hbase hsmall
  rintro ⟨a,b⟩ hp
  let Q (i : ℕ) : Point := (base form157)[i]?.getD origin
  have hQ (i : ℕ) (hi : i < 5) : Q i ∈ base form157 := by
    have hh : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hh with rfl | rfl | rfl | rfl | rfl <;> simp [Q, base]
  have hc (i : ℕ) (hi : i < 5) := label157_exists s z t _ (hpoint _ hp _ (hQ i hi))
  have hchoose : ∀ i : ℕ, ∃ k, k < 4 ∧ (i < 5 →
      (label small157 k).eval s z t = distanceSq (a,b) (Point.eval (Q i) s z)) := by
    intro i
    by_cases hi : i < 5
    · obtain ⟨k, hk, he⟩ := hc i hi
      exact ⟨k, hk, fun _ => he⟩
    · exact ⟨0, by decide, fun h => (hi h).elim⟩
  choose d hd he using hchoose
  obtain ⟨n, hn, hdec⟩ := encode d (fun i _ => hd i)
  have hdist (i : ℕ) (hi : i < 5) :
      (label small157 (decode n i)).eval s z t = distanceSq (a,b) (Point.eval (Q i) s z) := by
    rw [hdec i hi]
    exact he i hi
  have h0 := (hdist 0 (by decide)).symm
  have h1 := (hdist 1 (by decide)).symm
  have h2 := (hdist 2 (by decide)).symm
  have h3 := (hdist 3 (by decide)).symm
  have h4 := (hdist 4 (by decide)).symm
  have hS : sqrtThree.eval s z = s := by simp [sqrtThree, Radical.eval]
  have hu := norm_form157 s z hs hz
  have h := system_sound form157 small157 (decode n) s z t a b hs hz
    (by simpa [Q, base, distanceSq, origin, Point.eval, rc] using h0)
    (by simpa [Q, base, distanceSq, left, Point.eval, rc, Radical.eval_mul, hs, hz,
      hS, div_eq_mul_inv, sub_neg_eq_add] using h1)
    (by simpa [Q, base, distanceSq, right, Point.eval, rc, Radical.eval_mul, hs, hz,
      hS, div_eq_mul_inv] using h2)
    (by simpa [Q, base] using h3) (by simpa [Q, base] using h4) hu.1 hu.2
  exact ⟨n, hn, (Prod.ext h.1 h.2.1).symm, h.2.2⟩

end Erdos1082
