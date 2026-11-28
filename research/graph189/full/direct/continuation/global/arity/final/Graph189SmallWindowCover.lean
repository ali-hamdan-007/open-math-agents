import Graph189FiniteDomain
import Graph189WidthWindows

namespace Graph189SmallWindowCover
open Graph189FiniteDomain Graph189WidthWindows

def independent (k : ℤ) : ℤ := (k*(k-1)+3)/4

def startOrder (s k : ℤ) : ℤ :=
  let base := (s+1)*(k-s+2)-1
  if 4*s≤k then max base (min ((s+2)*(k-2*s+2)-1) (independent k)) else base

def maxDeficit (s k : ℤ) : ℤ :=
  if s=5 ∧ 46≤k ∧ k≤58 then 0 else
    max 0 (min (s-1) ((2*k+(k+1)*s-startOrder s k)/k))

def lower (s k : ℤ) : ℤ :=
  let d := maxDeficit s k
  if 3*s<2*(k-d-1) ∧ 2*s≤k-2*d-2 then
    max (startOrder s k) (min ((s+2)*(k-d-s+1)-1) (independent k))
  else startOrder s k

/-- A uniform order lower bound for this whole (s,k) pair. The low-cut
wedge is only needed for a positive effective deficit. -/
theorem lower_le {s k n d : ℤ} (hs : 5≤s) (hk : 3*s<k)
    (hbase : (s+1)*(k-s+2)-1 ≤ n)
    (hbridge : 4*s≤k → 4*n<k*(k-1) → (s+2)*(k-2*s+2)-1≤n)
    (hd : 0≤d) (hdmax : d≤s-1)
    (hwedge : 0<d → k*d≤2*k+(k+1)*s-n)
    (hfive : s=5 → 46≤k → k≤58 → d=0)
    (hlift : 3*s<2*(k-d-1) → 2*s≤k-2*d-2 → 4*n<k*(k-1) →
      (s+2)*(k-d-s+1)-1≤n) : lower s k≤n := by
  have hk0 : 0<k := by omega
  have hind : k*(k-1)≤4*n → independent k≤n := by unfold independent; omega
  have hstart : startOrder s k≤n := by
    unfold startOrder
    split
    next h =>
      apply max_le hbase
      by_cases hc : 4*n<k*(k-1)
      · exact (min_le_left _ _).trans (hbridge h hc)
      · exact (min_le_right _ _).trans (hind (by omega))
    next => exact hbase
  have hmax : d≤maxDeficit s k := by
    unfold maxDeficit
    split
    next h => rw [hfive h.1 h.2.1 h.2.2]
    next =>
      by_cases hpos : 0<d
      · have hr : d≤(2*k+(k+1)*s-startOrder s k)/k := by
          apply (Int.le_ediv_iff_mul_le hk0).mpr
          nlinarith only [hwedge hpos,hstart]
        exact (le_min hdmax hr).trans (le_max_right _ _)
      · exact (by omega : d≤0).trans (le_max_left _ _)
  dsimp only [lower]
  split
  next h =>
    apply max_le hstart
    by_cases hc : 4*n<k*(k-1)
    · have hl := hlift (by omega) (by omega) hc
      have ha := mul_nonneg (show 0≤s+2 by omega) (sub_nonneg.mpr hmax)
      apply (min_le_left _ _).trans
      nlinarith only [ha,hl]
    · exact (min_le_right _ _).trans (hind (by omega))
  next => exact hstart

def badOrder (s k l : ℤ) : Bool := decide
  (s*k*k < (l-2*k-1)*(k-s) ∨
    (6*(s-1)<k ∧ ((2*s+3)*k+4*s+4≤2*l ∨
       ((s+1)*(s-2)+3)*k≤(s-2)*(l-2*s-3))))

def badWidth (k l : ℤ) : Bool :=
  let m := 4*k
  let q := 4*l
  let e := -((-(q-3*m-4))/m)
  decide (m*(e-1)<q-3*m-4 ∧ 0≤first m q (2*k) ∧ 0≤second m q e ∧
    0<debit m q k e ∧ 0<debit m q k (2*k))

def populationCap : Nat → Nat → ℤ
  | 5, 51 => 62
  | 5, 52 => 63
  | 5, 53 => 64
  | 5, 54 => 65
  | 5, 55 => 66
  | 5, 56 => 67
  | 5, 57 => 67
  | 5, 58 => 68
  | 5, 59 => 72
  | 5, 60 => 73
  | 5, 61 => 74
  | 5, 62 => 75
  | 5, 63 => 73
  | 5, 64 => 74
  | 5, 65 => 75
  | 5, 66 => 76
  | 5, 67 => 77
  | 5, 68 => 78
  | 5, 69 => 79
  | 5, 70 => 80
  | 5, 71 => 81
  | 5, 72 => 82
  | 5, 73 => 83
  | 5, 74 => 84
  | 5, 75 => 85
  | 5, 76 => 86
  | 5, 77 => 87
  | 5, 78 => 88
  | 5, 79 => 89
  | 5, 80 => 90
  | 5, 81 => 91
  | 6, 77 => 90
  | 6, 78 => 91
  | 6, 79 => 92
  | 6, 80 => 93
  | 6, 81 => 94
  | 6, 82 => 95
  | 6, 83 => 96
  | 6, 84 => 97
  | 6, 85 => 98
  | 6, 86 => 99
  | 6, 87 => 100
  | 6, 88 => 99
  | 6, 89 => 100
  | 6, 90 => 101
  | 6, 91 => 102
  | 6, 92 => 103
  | 6, 93 => 103
  | 6, 94 => 104
  | 6, 95 => 105
  | 6, 96 => 106
  | 6, 97 => 107
  | 6, 98 => 108
  | 6, 99 => 109
  | 6, 100 => 110
  | 6, 101 => 111
  | 6, 102 => 112
  | 6, 103 => 113
  | 6, 104 => 114
  | 6, 105 => 115
  | 6, 106 => 116
  | 6, 107 => 117
  | 6, 108 => 118
  | 6, 109 => 119
  | 7, 113 => 126
  | 7, 114 => 127
  | 7, 115 => 128
  | 7, 116 => 129
  | 7, 117 => 128
  | 7, 118 => 129
  | 7, 119 => 130
  | 7, 120 => 131
  | 7, 121 => 132
  | 7, 122 => 133
  | 7, 123 => 134
  | 7, 124 => 135
  | 7, 125 => 136
  | 7, 126 => 137
  | 7, 127 => 138
  | 7, 128 => 139
  | 7, 129 => 140
  | 7, 130 => 141
  | 7, 131 => 142
  | 7, 132 => 143
  | 7, 133 => 144
  | 7, 134 => 145
  | 7, 135 => 146
  | 7, 136 => 147
  | 7, 137 => 148
  | 7, 138 => 149
  | 7, 139 => 150
  | 7, 140 => 151
  | 7, 141 => 152
  | 8, 158 => 170
  | 8, 159 => 171
  | 8, 160 => 172
  | 8, 161 => 173
  | 8, 162 => 174
  | 8, 163 => 175
  | 8, 164 => 176
  | 8, 165 => 177
  | 8, 166 => 178
  | 8, 167 => 179
  | 8, 168 => 180
  | 8, 169 => 181
  | 8, 170 => 182
  | 8, 171 => 183
  | 8, 172 => 184
  | 8, 173 => 185
  | 8, 174 => 186
  | 8, 175 => 187
  | 8, 176 => 188
  | 8, 177 => 189
  | _, _ => 0

def band (s k : ℤ) : Band :=
  ⟨s,k,lower s k,lower s k,populationCap s.toNat k.toNat⟩

def check (s k : ℤ) : Bool := decide (
  s<5 ∨ 8<s ∨ k<26 ∨ k≤3*s ∨ 4*s^2+8*s-2≤k ∨ badOrder s k (lower s k)=true ∨
  badWidth k (lower s k)=true ∨ valid (band s k)=true)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem all_pairs : ∀ s : Fin 9, ∀ k : Fin 318, check s.val k.val = true := by
  decide

/-- At every remaining degree-connectivity pair the order lower bound
satisfies all the strict terminal quota inequalities. This result does not
enumerate individual orders or rely on the executable projection. -/
theorem terminal_quotas {s k n e : ℤ} (hs : 5≤s) (hs8 : s≤8) (hk26 : 26≤k)
    (hk : 3*s<k) (hkmax : k<4*s^2+8*s-2)
    (he : 0≤e) (hemax : e≤2*k) (hore : n≤3*k+1+k*e)
    (hwidth : (n-2*k-e-2)*(2*(n-2*k)+k*e)≤k*(k+1)*(k+e))
    (hl : lower s k≤n)
    (hside : (n-2*k-1)*(k-s)≤s*k*k)
    (hhalf : 6*(s-1)<k → 2*n<(2*s+3)*k+4*s+4)
    (hthree : 6*(s-1)<k → (s-2)*(n-2*s-3)<((s+1)*(s-2)+3)*k) :
    valid (band s k)=true := by
  have hsquare := mul_nonneg (show 0≤s+8 by omega) (sub_nonneg.mpr hs8)
  have hk318 : k<318 := by nlinarith only [hsquare,hs8,hkmax]
  let i : Fin 9 := ⟨s.toNat,by omega⟩
  let j : Fin 318 := ⟨k.toNat,by omega⟩
  have hi : (i.val:ℤ)=s := by dsimp [i]; omega
  have hj : (j.val:ℤ)=k := by dsimp [j]; omega
  have h := all_pairs i j
  rw [hi,hj] at h
  simp only [check,decide_eq_true_eq] at h
  rcases h with h|h|h|h|h|ho|hw|h
  · omega
  · omega
  · omega
  · omega
  · omega
  · simp only [badOrder,decide_eq_true_eq] at ho
    rcases ho with h|⟨hc,h|h⟩
    · have hp := mul_le_mul_of_nonneg_right hl (show 0≤k-s by omega)
      nlinarith only [hp,h,hside]
    · have hh := hhalf hc
      omega
    · have hh := hthree hc
      have hp := mul_le_mul_of_nonneg_left hl (show 0≤s-2 by omega)
      nlinarith only [hh,hp,h]
  · simp only [badWidth,decide_eq_true_eq] at hw
    obtain ⟨hf,ha,hb,h1,h2⟩ := hw
    have hk0 : 0<k := by omega
    have hq := mul_le_mul_of_nonneg_right hl hk0.le
    exact (window_impossible (L:=k) (H:=k) (q:=4*lower s k)
      hk0 le_rfl le_rfl he hemax (by nlinarith only [hq]) hore hwidth hf ha hb h1 h2).elim
  · exact h

end Graph189SmallWindowCover

#print axioms Graph189SmallWindowCover.all_pairs
#print axioms Graph189SmallWindowCover.lower_le
#print axioms Graph189SmallWindowCover.terminal_quotas
