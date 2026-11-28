import Graph189WidthReplayBridge

namespace Graph189WidthInterval

private theorem accepted_iff (k n : ℤ) :
    Graph189ScalarReplay.widthPossible k n = true ↔
      n ≤ 4*k+2 ∨ (low k n ≤ 3*k ∧
        min (difference k n (low k n)) (difference k n (3*k)) ≤ 0) := by
  simp [Graph189ScalarReplay.widthPossible, Graph189ScalarReplay.ceilDiv, low, difference]

private theorem low_mono {k m n : ℤ} (hk : 0 < k) (hmn : m ≤ n) :
    low k m ≤ low k n := by
  have h := Int.ediv_le_ediv hk (show -(n-3*k-1) ≤ -(m-3*k-1) by omega)
  unfold low
  exact add_le_add_right (max_le_max_left 0 (neg_le_neg h)) k

private theorem fixed_mono {k m n d : ℤ} (hk : 0 ≤ k) (hm : 4*k+2 < m)
    (hmn : m ≤ n) (hkd : k ≤ d) (hdk : d ≤ 3*k) :
    difference k m d ≤ difference k n d := by
  have positive := mul_nonneg hk (sub_nonneg.mpr hkd)
  have factor : 0 ≤ 2*m+2*n+k*(d-k)-2*d-6*k-4 := by omega
  have product := mul_nonneg (sub_nonneg.mpr hmn) factor
  dsimp [difference]
  nlinarith only [product]

/-- Concavity in d turns a feasible point into a feasible endpoint. -/
theorem interval_endpoints {k n a d b : ℤ} (hk : 0 ≤ k) (ha : a ≤ d) (hb : d ≤ b)
    (hf : difference k n d ≤ 0) :
    min (difference k n a) (difference k n b) ≤ 0 := by
  by_cases h : a = d
  · subst a
    exact (min_le_left _ _).trans hf
  by_cases h' : b = d
  · subst b
    exact (min_le_right _ _).trans hf
  by_contra! hn
  have l := lt_of_lt_of_le hn (min_le_left _ _)
  have r := lt_of_lt_of_le hn (min_le_right _ _)
  have one := mul_pos (show 0 < b-d by omega)
    (show 0 < difference k n a - difference k n d by omega)
  have two := mul_pos (show 0 < d-a by omega)
    (show 0 < difference k n b - difference k n d by omega)
  have third := mul_nonneg (mul_nonneg (mul_nonneg hk (sub_nonneg.mpr hb))
    (sub_nonneg.mpr ha)) (sub_nonneg.mpr (ha.trans hb))
  dsimp [difference] at one two
  nlinarith only [one,two,third]

/-- The initial skip and early loop exit in projection cannot miss a higher
feasible order. This holds for every integer order and every positive k. -/
theorem widthPossible_of_le {k m n : ℤ} (hk : 0 < k) (hmn : m ≤ n)
    (hn : Graph189ScalarReplay.widthPossible k n = true) :
    Graph189ScalarReplay.widthPossible k m = true := by
  apply (accepted_iff k m).mpr
  by_cases hm : m ≤ 4*k+2
  · exact Or.inl hm
  obtain h | ⟨hu,hf⟩ := (accepted_iff k n).mp hn
  · omega
  have hlo := low_mono hk hmn
  have hkl : k ≤ low k n := by
    unfold low
    have := le_max_left (0 : ℤ) (-((-(n-3*k-1))/k))
    omega
  apply Or.inr
  refine ⟨hlo.trans hu, ?_⟩
  rcases min_le_iff.mp hf with l | r
  · exact interval_endpoints hk.le hlo hu ((fixed_mono hk.le (by omega) hmn hkl hu).trans l)
  · apply (min_le_right _ _).trans
    exact (fixed_mono hk.le (by omega) hmn (by omega : k ≤ 3*k) le_rfl).trans r

/-- Rejection persists above the first failing order. -/
theorem widthPossible_false_of_le {k m n : ℤ} (hk : 0 < k) (hmn : m ≤ n)
    (hm : Graph189ScalarReplay.widthPossible k m = false) :
    Graph189ScalarReplay.widthPossible k n = false := by
  cases hn : Graph189ScalarReplay.widthPossible k n with
  | false => rfl
  | true => simpa [hm] using widthPossible_of_le hk hmn hn

#print axioms widthPossible_of_le
#print axioms widthPossible_false_of_le
end Graph189WidthInterval
