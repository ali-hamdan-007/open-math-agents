import Mathlib.Tactic.Linarith

namespace Graph189FiniteDomain

/-- Recover an exact upper bound on the smaller population from an order lower
bound and the separator cross-product inequality. The two tests at the ends
of the excluded interval are what the finite certificate checks. -/
theorem population_bound {s k h cap x y : ℤ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (ht : h ≤ x+y)
    (hp : x*y ≤ k*x+s*k*k)
    (hc : k ≤ h-k-(cap+1))
    (hleft : s*k*k < (cap+1)*(h-k-(cap+1)))
    (hright : s*k*k < (h-k-(cap+1))*(h-k-(cap+1)-k)) :
    x ≤ cap := by
  by_contra! hn
  have hsq : x*x ≤ x*y := mul_le_mul_of_nonneg_left hxy hx
  have hxw : x ≤ h-k-(cap+1) := by
    by_contra! hz
    have h1 := mul_nonneg (sub_nonneg.mpr hz.le) (sub_nonneg.mpr hc)
    have h2 := mul_nonneg hx (sub_nonneg.mpr hz.le)
    nlinarith
  have hl : cap+1 ≤ x := by omega
  have h1 := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hxw)
  have h2 := mul_nonneg hx (sub_nonneg.mpr ht)
  nlinarith

structure Band where
  s : ℤ
  k : ℤ
  low : ℤ
  high : ℤ
  cap : ℤ
  deriving DecidableEq, Repr

def quotaPass (r : Band) (common : ℤ) : Bool := decide (
  let d := r.s-common
  (r.s*r.k+r.k-d*(d-1)+common+1)*d+r.k < (r.low-r.s-1)*d)

/-- Exact numerical conditions used by the second-separator argument. -/
def valid (r : Band) : Bool :=
  let h := r.low-r.s-1
  let a := r.cap+1
  let b := h-r.k-a
  decide (5 ≤ r.s ∧ 6*(r.s-1) < r.k ∧ r.low ≤ r.high ∧
    r.k ≤ b ∧ 0 ≤ b ∧ r.s*r.k*r.k < a*b ∧ r.s*r.k*r.k < b*(b-r.k) ∧
    (r.s+1)*r.k+2*r.s < r.low ∧
    r.s*r.k+r.cap < h ∧
    (r.s*r.k-r.s*(r.s-1)+r.cap+1)*r.s+r.cap < h*r.s ∧
    r.cap < 2*r.k-r.s ∧ quotaPass r 1 = true ∧ quotaPass r 2 = true)

def terminalBands : List Band := [
  ⟨5, 53, 342, 344, 64⟩,
  ⟨5, 54, 349, 354, 65⟩,
  ⟨5, 55, 356, 364, 66⟩,
  ⟨5, 56, 363, 370, 67⟩,
  ⟨5, 57, 370, 377, 67⟩,
  ⟨5, 58, 377, 384, 68⟩,
  ⟨5, 59, 384, 390, 69⟩,
  ⟨5, 60, 391, 400, 70⟩,
  ⟨5, 61, 398, 408, 71⟩,
  ⟨5, 62, 405, 414, 72⟩,
  ⟨5, 63, 412, 421, 73⟩,
  ⟨5, 64, 419, 427, 74⟩,
  ⟨5, 65, 426, 434, 75⟩,
  ⟨5, 66, 433, 440, 76⟩,
  ⟨5, 67, 440, 447, 77⟩,
  ⟨5, 68, 447, 453, 78⟩,
  ⟨5, 69, 454, 460, 79⟩,
  ⟨5, 70, 461, 466, 80⟩,
  ⟨5, 71, 468, 473, 81⟩,
  ⟨5, 72, 475, 479, 82⟩,
  ⟨5, 73, 482, 486, 83⟩,
  ⟨5, 74, 489, 492, 84⟩,
  ⟨5, 75, 496, 499, 85⟩,
  ⟨5, 76, 503, 505, 86⟩,
  ⟨5, 77, 510, 512, 87⟩,
  ⟨5, 78, 517, 518, 88⟩,
  ⟨5, 79, 524, 525, 89⟩,
  ⟨5, 80, 531, 531, 90⟩,
  ⟨5, 81, 538, 538, 91⟩,
  ⟨6, 82, 615, 616, 93⟩,
  ⟨6, 83, 623, 629, 94⟩,
  ⟨6, 84, 631, 638, 95⟩,
  ⟨6, 85, 639, 645, 96⟩,
  ⟨6, 86, 647, 653, 97⟩,
  ⟨6, 87, 655, 660, 98⟩,
  ⟨6, 88, 663, 668, 99⟩,
  ⟨6, 89, 671, 677, 100⟩,
  ⟨6, 90, 679, 688, 101⟩,
  ⟨6, 91, 687, 696, 102⟩,
  ⟨6, 92, 695, 703, 103⟩,
  ⟨6, 93, 703, 711, 103⟩,
  ⟨6, 94, 711, 718, 104⟩,
  ⟨6, 95, 719, 726, 105⟩,
  ⟨6, 96, 727, 733, 106⟩,
  ⟨6, 97, 735, 741, 107⟩,
  ⟨6, 98, 743, 748, 108⟩,
  ⟨6, 99, 751, 756, 109⟩,
  ⟨6, 100, 759, 763, 110⟩,
  ⟨6, 101, 767, 771, 111⟩,
  ⟨6, 102, 775, 778, 112⟩,
  ⟨6, 103, 783, 786, 113⟩,
  ⟨6, 104, 791, 793, 114⟩,
  ⟨6, 105, 799, 801, 115⟩,
  ⟨6, 106, 807, 808, 116⟩,
  ⟨6, 107, 815, 816, 117⟩,
  ⟨6, 108, 823, 823, 118⟩,
  ⟨6, 109, 831, 831, 119⟩,
  ⟨7, 117, 998, 999, 128⟩,
  ⟨7, 118, 1007, 1012, 129⟩,
  ⟨7, 119, 1016, 1021, 130⟩,
  ⟨7, 120, 1025, 1029, 131⟩,
  ⟨7, 121, 1034, 1038, 132⟩,
  ⟨7, 122, 1043, 1046, 133⟩,
  ⟨7, 123, 1052, 1055, 134⟩,
  ⟨7, 124, 1061, 1064, 135⟩,
  ⟨7, 125, 1070, 1076, 136⟩,
  ⟨7, 126, 1079, 1086, 137⟩,
  ⟨7, 127, 1088, 1095, 138⟩,
  ⟨7, 128, 1097, 1103, 139⟩,
  ⟨7, 129, 1106, 1112, 140⟩,
  ⟨7, 130, 1115, 1120, 141⟩,
  ⟨7, 131, 1124, 1129, 142⟩,
  ⟨7, 132, 1133, 1137, 143⟩,
  ⟨7, 133, 1142, 1146, 144⟩,
  ⟨7, 134, 1151, 1154, 145⟩,
  ⟨7, 135, 1160, 1163, 146⟩,
  ⟨7, 136, 1169, 1171, 147⟩,
  ⟨7, 137, 1178, 1180, 148⟩,
  ⟨7, 138, 1187, 1188, 149⟩,
  ⟨7, 139, 1196, 1197, 150⟩,
  ⟨7, 140, 1205, 1205, 151⟩,
  ⟨7, 141, 1214, 1214, 152⟩,
  ⟨8, 158, 1509, 1510, 170⟩,
  ⟨8, 159, 1519, 1521, 171⟩,
  ⟨8, 160, 1529, 1531, 172⟩,
  ⟨8, 161, 1539, 1540, 173⟩,
  ⟨8, 162, 1549, 1550, 174⟩,
  ⟨8, 163, 1559, 1559, 175⟩,
  ⟨8, 164, 1569, 1569, 176⟩,
  ⟨8, 165, 1579, 1579, 177⟩,
  ⟨8, 166, 1589, 1589, 178⟩,
  ⟨8, 167, 1599, 1604, 179⟩,
  ⟨8, 168, 1609, 1613, 180⟩,
  ⟨8, 169, 1619, 1623, 181⟩,
  ⟨8, 170, 1629, 1632, 182⟩,
  ⟨8, 171, 1639, 1642, 183⟩,
  ⟨8, 172, 1649, 1651, 184⟩,
  ⟨8, 173, 1659, 1661, 185⟩,
  ⟨8, 174, 1669, 1670, 186⟩,
  ⟨8, 175, 1679, 1680, 187⟩,
  ⟨8, 176, 1689, 1689, 188⟩,
  ⟨8, 177, 1699, 1699, 189⟩
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem terminal_bands_checked : terminalBands.all valid = true := by decide

theorem terminal_bands_count : terminalBands.length = 102 := by decide

/-- Any cut at any order in a recorded band satisfies both the population bound and
the strict lower bound on the opposite population used in the support argument. -/
theorem terminal_population {r : Band} (hm : r ∈ terminalBands)
    {x y : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hsize : r.low - r.s - 1 ≤ x+y)
    (hprod : x*y ≤ r.k*x+r.s*r.k*r.k) :
    x ≤ r.cap ∧ r.s*r.k < y := by
  have h := List.all_eq_true.mp terminal_bands_checked r hm
  simp only [valid, decide_eq_true_eq] at h
  obtain ⟨_, _, _, hb, _, hl, hr, _, hh, _, _, _, _⟩ := h
  have hcap := population_bound hx hxy hsize hprod hb hl hr
  exact ⟨hcap, by omega⟩

end Graph189FiniteDomain

#print axioms Graph189FiniteDomain.population_bound
#print axioms Graph189FiniteDomain.terminal_bands_checked
#print axioms Graph189FiniteDomain.terminal_bands_count

#print axioms Graph189FiniteDomain.terminal_population
