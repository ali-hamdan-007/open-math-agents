import Graph189WidthWindows

namespace Graph189WindowCover
open Graph189WidthWindows

def basic (s l : ℤ) : ℤ := 4*((s+1)*(l-s+2)-1)
def robust (s l : ℤ) : ℤ := 4*((s+2)*(l-2*s+2)-1)
def ratioNumerator (s l : ℤ) : ℤ :=
  if 4*s ≤ l then max (basic s l) (min (robust s l) (l*(l-1))) else basic s l

private theorem affine_ratio {a C l k n : ℤ} (hC : 0 ≤ C) (hl : 0 ≤ l)
    (hk : l ≤ k) (hn : a*k-C ≤ n) : 4*(a*l-C)*k ≤ (4*l)*n := by
  have h₁ := mul_le_mul_of_nonneg_left hn hl
  have h₂ := mul_nonneg hC (sub_nonneg.mpr hk)
  nlinarith only [h₁,h₂]

/-- The lower bound for the order divided by k improves when k increases
along the window, also across the independent-exterior alternative. -/
theorem lower_ratio {s l k n : ℤ} (hs : 9 ≤ s) (hl : 0 ≤ l) (hk : l ≤ k)
    (hb : (s+1)*(k-s+2)-1 ≤ n)
    (hr : 4*s ≤ k → 4*n < k*(k-1) → (s+2)*(k-2*s+2)-1 ≤ n) :
    ratioNumerator s l * k ≤ (4*l)*n := by
  have hk0 := hl.trans hk
  have cb := mul_nonneg (show 0 ≤ s+1 by omega) (show 0 ≤ s-2 by omega)
  have hlo := affine_ratio (n := n) (a := s+1) (C := (s+1)*(s-2)+1) (by omega) hl hk
    (by nlinarith only [hb])
  have hbase : basic s l * k ≤ (4*l)*n := by dsimp [basic]; nlinarith only [hlo]
  by_cases hcut : 4*s ≤ l
  · have hmin : min (robust s l) (l*(l-1))*k ≤ 4*l*n := by
      by_cases hc : 4*n < k*(k-1)
      · have hlo := hr (hcut.trans hk) hc
        have cc := mul_nonneg (show 0 ≤ s+2 by omega) (show 0 ≤ 2*s-2 by omega)
        have hh := affine_ratio (n := n) (a := s+2) (C := (s+2)*(2*s-2)+1) (by omega) hl hk
          (by nlinarith only [hlo])
        apply (mul_le_mul_of_nonneg_right (min_le_left _ _) hk0).trans
        dsimp [robust]; nlinarith only [hh]
      · have hi := mul_le_mul_of_nonneg_left (le_of_not_gt hc) hl
        have hj := mul_nonneg (mul_nonneg hl hk0) (sub_nonneg.mpr hk)
        apply (mul_le_mul_of_nonneg_right (min_le_right _ _) hk0).trans
        nlinarith only [hi,hj]
    unfold ratioNumerator
    rw [if_pos hcut]
    rcases le_total (basic s l) (min (robust s l) (l*(l-1))) with h|h
    · simpa only [max_eq_right h] using hmin
    · simpa only [max_eq_left h] using hbase
  · simpa only [ratioNumerator,if_neg hcut] using hbase

def valid (s l u : ℤ) : Bool :=
  let m := 4*l
  let q := ratioNumerator s l
  let e := -((-(q-3*m-4))/m)
  decide (0<l ∧ l≤u ∧ m*(e-1)<q-3*m-4 ∧
    0≤first m q (2*u) ∧ 0≤second m q e ∧
    0<debit m q u e ∧ 0<debit m q u (2*u))

def scan (s l h : ℤ) : List ℤ → Bool
  | [] => decide (h<l)
  | u::t => Bool.and (valid s l u) (scan s (u+1) h t)

private theorem scan_covers {s l H k : ℤ} {t : List ℤ}
    (h : scan s l H t = true) (hlk : l≤k) (hkH : k≤H) :
    ∃ l' u', l'≤k ∧ k≤u' ∧ valid s l' u'=true := by
  induction t generalizing l with
  | nil =>
    simp only [scan,decide_eq_true_eq] at h
    omega
  | cons u t ih =>
    have hh := Bool.and_eq_true_iff.mp h
    by_cases hu : k≤u
    · exact ⟨l,u,hlk,hu,hh.1⟩
    · exact ih hh.2 (by omega)

def lastDegree (s : ℤ) : ℤ := if s=9 then 162 else 2*s*s+3*s-3

def upperEndpoints : Nat → List ℤ
  | 9 => [44, 61, 95, 129, 146, 162]
  | 10 => [55, 80, 129, 178, 203, 215, 221, 227]
  | 11 => [63, 93, 153, 213, 243, 272]
  | 12 => [108, 179, 250, 321]
  | 13 => [123, 207, 291, 374]
  | 14 => [140, 237, 431]
  | 15 => [157, 269, 492]
  | 16 => [176, 303, 557]
  | 17 => [195, 339, 626]
  | 18 => [216, 377, 699]
  | 19 => [237, 417, 776]
  | 20 => [260, 459, 857]
  | 21 => [283, 503, 942]
  | 22 => [308, 549, 1031]
  | 23 => [333, 597, 1124]
  | 24 => [360, 647, 1221]
  | 25 => [387, 699, 1322]
  | 26 => [416, 753, 1427]
  | 27 => [445, 809, 1536]
  | 28 => [476, 867, 1649]
  | 29 => [507, 927, 1766]
  | 30 => [540, 989, 1887]
  | 31 => [573, 1053, 2012]
  | 32 => [608, 1119, 2141]
  | 33 => [643, 1187, 2274]
  | 34 => [680, 1257, 2411]
  | 35 => [717, 1329, 2552]
  | 36 => [756, 1403, 2697]
  | 37 => [795, 1479, 2846]
  | 38 => [836, 1557, 2999]
  | 39 => [877, 1637, 3156]
  | 40 => [920, 1719, 3317]
  | 41 => [963, 1803, 3482]
  | 42 => [1008, 1889, 3651]
  | 43 => [1053, 1977, 3824]
  | 44 => [1100, 2067, 4001]
  | 45 => [1147, 2159, 4182]
  | 46 => [1196, 2253, 4367]
  | 47 => [1245, 2349, 4556]
  | 48 => [1296, 2447, 4749]
  | 49 => [1347, 2547, 4946]
  | 50 => [1400, 2649, 5147]
  | 51 => [1453, 2753, 5352]
  | 52 => [1508, 2859, 5561]
  | 53 => [1563, 2967, 5774]
  | 54 => [1620, 3077, 5991]
  | 55 => [1677, 3189, 6212]
  | 56 => [1736, 3303, 6437]
  | 57 => [1795, 3419, 6666]
  | 58 => [1856, 3537, 6899]
  | 59 => [1917, 3657, 7136]
  | 60 => [1980, 3779, 7377]
  | 61 => [2043, 3903, 7622]
  | 62 => [2108, 4029, 7871]
  | 63 => [2173, 4157, 8124]
  | 64 => [2240, 4287, 8381]
  | 65 => [2307, 4419, 8642]
  | 66 => [2376, 4553, 8907]
  | 67 => [2445, 4689, 9176]
  | 68 => [2516, 4827, 9449]
  | 69 => [2587, 4967, 9726]
  | 70 => [2660, 5109, 10007]
  | 71 => [2733, 5253, 10292]
  | 72 => [2808, 5399, 10581]
  | 73 => [2883, 5547, 10874]
  | 74 => [2960, 5697, 11171]
  | 75 => [3037, 5849, 11472]
  | 76 => [3116, 6003, 11777]
  | 77 => [3195, 6159, 12086]
  | 78 => [3276, 6317, 12399]
  | 79 => [3357, 6477, 12716]
  | 80 => [3440, 6639, 13037]
  | 81 => [3523, 6803, 13362]
  | 82 => [3608, 6969, 13691]
  | 83 => [3693, 7137, 14024]
  | 84 => [3780, 7307, 14361]
  | 85 => [3867, 7479, 14702]
  | 86 => [3956, 7653, 15047]
  | 87 => [4045, 7829, 15396]
  | 88 => [4136, 8007, 15749]
  | 89 => [4227, 8187, 16106]
  | 90 => [4320, 8369, 16467]
  | 91 => [4413, 8553, 16832]
  | 92 => [4508, 8739, 17201]
  | 93 => [4603, 8927, 17574]
  | 94 => [4700, 9117, 17951]
  | 95 => [4797, 9309, 18332]
  | 96 => [4896, 9503, 18717]
  | 97 => [4995, 9699, 19106]
  | 98 => [5096, 9897, 19499]
  | 99 => [5197, 10097, 19896]
  | _ => []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem all_windows : ∀ s : Fin 100, s.val < 9 ∨
    scan (s.val : ℤ) (3*(s.val : ℤ)+1) (lastDegree (s.val : ℤ)) (upperEndpoints s.val) = true := by
  decide

/-- All k up through the analytic large-degree threshold are excluded using
the two endpoint values of the quadratic in each certified interval. -/
theorem no_lower_range (t : Fin 100) {k n e : ℤ} (hs : 9≤t.val)
    (hk : 3*(t.val : ℤ) < k) (hstop : k ≤ lastDegree (t.val : ℤ))
    (he : 0 ≤ e) (heu : e ≤ 2*k) (hore : n ≤ 3*k+1+k*e)
    (hwidth : (n-2*k-e-2)*(2*(n-2*k)+k*e) ≤ k*(k+1)*(k+e))
    (horder : ((t.val : ℤ)+1)*(k-(t.val : ℤ)+2)-1 ≤ n)
    (hbridge : 4*(t.val : ℤ) ≤ k → 4*n < k*(k-1) →
      ((t.val : ℤ)+2)*(k-2*(t.val : ℤ)+2)-1 ≤ n) : False := by
  have htab := (all_windows t).resolve_left (by omega)
  obtain ⟨l,u,hl,hu,hv⟩ := scan_covers htab (by omega : 3*(t.val : ℤ)+1≤k) hstop
  simp only [valid,decide_eq_true_eq] at hv
  obtain ⟨hl0,_,hfloor,ha,hb,hL,hU⟩ := hv
  have hr := lower_ratio (s := (t.val : ℤ)) (by exact_mod_cast hs) hl0.le hl horder hbridge
  exact window_impossible hl0 hl hu he heu hr hore hwidth hfloor ha hb hL hU

end Graph189WindowCover

#print axioms Graph189WindowCover.all_windows
#print axioms Graph189WindowCover.no_lower_range
