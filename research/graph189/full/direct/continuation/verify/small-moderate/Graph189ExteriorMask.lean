import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Init.Data.Nat.Bitwise.Lemmas

namespace Graph189ExteriorMask
open SimpleGraph Finset

/-- Pack bits in little-endian order, as used for the search's adjacency rows. -/
def packBits : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n+1, f => (f 0).toNat + 2*packBits n (fun i => f i.succ)

theorem packBits_lt {n : ℕ} (f : Fin n → Bool) : packBits n f < 2^n := by
  induction n with
  | zero => simp [packBits]
  | succ n ih =>
    rw [packBits,Nat.pow_succ]
    have cont := ih (fun i => f i.succ)
    have bit := Bool.toNat_le (f 0)
    omega

@[simp] theorem packBits_read {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (packBits n f).testBit i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (packBits (n+1) f).testBit 0 = f 0
      rw [packBits,Nat.testBit_zero]
      have rem : ((f 0).toNat + 2*packBits n (fun i => f i.succ))%2 = (f 0).toNat := by
        have bit := Bool.toNat_lt (f 0)
        omega
      rw [rem]
      cases f 0 <;> rfl
    · change (packBits (n+1) f).testBit (j.val+1) = f j.succ
      rw [packBits,Nat.testBit_add_one]
      have half : ((f 0).toNat+2*packBits n (fun i => f i.succ))/2 =
          packBits n (fun i => f i.succ) := by
        have bit := Bool.toNat_lt (f 0)
        omega
      rw [half,ih]

/-- The number of unordered vertex pairs, in successive vertex-extension blocks. -/
def edgeCount : ℕ → ℕ
  | 0 => 0
  | b+1 => edgeCount b+b

theorem edgeCount_mono : Monotone edgeCount :=
  monotone_nat_of_le_succ (fun n => by simp [edgeCount])

theorem edgeCount_eq (b : ℕ) : edgeCount b = b*(b-1)/2 := by
  have aux : ∀ n, 2*edgeCount n = n*(n-1) := by
    intro n
    induction n with
    | zero => simp [edgeCount]
    | succ n ih =>
      rw [edgeCount,Nat.succ_sub_one]
      by_cases hn : n=0
      · simp [hn,edgeCount]
      · have he : n-1+1=n := by omega
        have hm := congrArg (fun t : ℕ => n*t) he
        simp only [Nat.mul_add,Nat.mul_one] at hm
        nlinarith only [ih,hm]
  have h := aux b
  omega

/-- The bit of {i,j}, with the larger label choosing its extension block. -/
def slot {b : ℕ} (i j : Fin b) : ℕ := edgeCount (max i.val j.val) + min i.val j.val

theorem slot_of_lt {b : ℕ} {i j : Fin b} (h : i<j) : slot i j = edgeCount j.val+i.val := by
  have hh : i.val≤j.val := Nat.le_of_lt h
  simp [slot,max_eq_right hh,min_eq_left hh]

theorem slot_comm {b : ℕ} (i j : Fin b) : slot j i = slot i j := by
  unfold slot
  rw [Nat.max_comm j.val i.val,Nat.min_comm j.val i.val]

theorem slot_lt {b : ℕ} {i j : Fin b} (h : i<j) : slot i j < edgeCount b := by
  rw [slot_of_lt h]
  have before : edgeCount j.val+i.val < edgeCount (j.val+1) := by
    rw [edgeCount]
    exact Nat.add_lt_add_left h _
  exact before.trans_le (edgeCount_mono j.isLt)

theorem slot_injective {b : ℕ} {i j i' j' : Fin b}
    (h : i<j) (h' : i'<j') (eq : slot i j=slot i' j') : i=i' ∧ j=j' := by
  rw [slot_of_lt h,slot_of_lt h'] at eq
  have hj : j=j' := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with before|after
    · have hh : edgeCount (j.val+1) ≤ edgeCount j'.val := edgeCount_mono before
      rw [edgeCount] at hh
      have hi : i.val<j.val := h
      omega
    · have hh : edgeCount (j'.val+1) ≤ edgeCount j.val := edgeCount_mono after
      rw [edgeCount] at hh
      have hi : i'.val<j'.val := h'
      omega
  refine ⟨Fin.ext ?_,hj⟩
  subst j'
  omega

/-- Decode a finite simple graph from a packed upper-triangular edge mask. -/
def graph (b mask : ℕ) : SimpleGraph (Fin b) where
  Adj i j := i≠j ∧ mask.testBit (slot i j) = true
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm,by
      rw [slot_comm i j]
      exact h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

instance (b mask : ℕ) : DecidableRel (graph b mask).Adj := fun i j =>
  inferInstanceAs (Decidable (i≠j ∧ mask.testBit (slot i j) = true))

@[simp] theorem graph_adj {b m : ℕ} (i j : Fin b) :
    (graph b m).Adj i j ↔ i≠j ∧ m.testBit (slot i j) = true := Iff.rfl

/-- The full row mask used in the uncompressed Python records. -/
def rowMask (b m : ℕ) (i : Fin b) : ℕ :=
  packBits b (fun j => decide ((graph b m).Adj i j))

theorem rowMask_lt (b m : ℕ) (i : Fin b) : rowMask b m i < 2^b := packBits_lt _

@[simp] theorem rowMask_adj {b m : ℕ} (i j : Fin b) :
    (rowMask b m i).testBit j.val = true ↔ (graph b m).Adj i j := by
  simp only [rowMask,packBits_read,decide_eq_true_eq]

/-- The row list has the same indexing and bit order as the Python checker. -/
def rowMasks (b m : ℕ) : List ℕ := List.ofFn (rowMask b m)

theorem rowMasks_length (b m : ℕ) : (rowMasks b m).length=b := by simp [rowMasks]

@[simp] theorem rowMasks_get (b m : ℕ) (i : Fin b) :
    (rowMasks b m)[i.val]'(by rw [rowMasks_length]; exact i.isLt) = rowMask b m i := by
  simp [rowMasks]

/-- Neighbors interpreted directly from row masks, for the completion checker. -/
def rowNeighbors (b m : ℕ) (i : Fin b) : Finset (Fin b) :=
  univ.filter (fun j => (rowMask b m i).testBit j.val = true)

@[simp] theorem rowNeighbors_correct {b m : ℕ} (i j : Fin b) :
    j ∈ rowNeighbors b m i ↔ (graph b m).Adj i j := by simp [rowNeighbors]

/-- Encode a labelled graph by recording precisely its edges in the pair blocks. -/
noncomputable def encode {b : ℕ} (G : SimpleGraph (Fin b)) : ℕ := by
  classical
  exact packBits (edgeCount b) (fun q => decide (∃ i j : Fin b, i<j ∧ slot i j=q.val ∧ G.Adj i j))

theorem encode_lt {b : ℕ} (G : SimpleGraph (Fin b)) : encode G < 2^edgeCount b := by
  unfold encode
  exact packBits_lt _

private theorem encode_read_lt {b : ℕ} (G : SimpleGraph (Fin b)) {i j : Fin b} (lt : i<j) :
    (encode G).testBit (slot i j) = true ↔ G.Adj i j := by
  classical
  let q : Fin (edgeCount b) := ⟨slot i j,slot_lt lt⟩
  change (encode G).testBit q.val = true ↔ G.Adj i j
  simp only [encode,packBits_read,decide_eq_true_eq]
  constructor
  · rintro ⟨a,w,aw,h,edge⟩
    obtain ⟨rfl,rfl⟩ := slot_injective aw lt h
    exact edge
  · intro edge
    exact ⟨i,j,lt,rfl,edge⟩

theorem decode_encode {b : ℕ} (G : SimpleGraph (Fin b)) : graph b (encode G) = G := by
  ext i j
  rw [graph_adj]
  by_cases eq : i=j
  · subst j
    simp
  · rcases lt_or_gt_of_ne eq with lt|lt
    · exact (and_iff_right eq).trans (encode_read_lt G lt)
    · rw [slot_comm j i]
      exact (and_iff_right eq).trans ((encode_read_lt G lt).trans ⟨fun h => h.symm,fun h => h.symm⟩)

/-- Every finite exterior graph is isomorphic to a bounded edge mask on `Fin b`. -/
theorem exists_mask_labeling {V : Type*} [Fintype V] (G : SimpleGraph V) {b : ℕ}
    (card : Fintype.card V=b) : ∃ m < 2^edgeCount b, Nonempty (G ≃g graph b m) := by
  let equiv := Fintype.equivFinOfCardEq card
  let labeled := G.map equiv
  refine ⟨encode labeled,encode_lt labeled,?_⟩
  rw [decode_encode]
  exact ⟨SimpleGraph.Iso.map equiv G⟩

/-- The lower mask and the last vertex's star split at the pair-block boundary. -/
def extendMask (b old star : ℕ) : ℕ := old + 2^edgeCount b*star

theorem split_mask {b m : ℕ} (h : m < 2^edgeCount (b+1)) :
    ∃ old < 2^edgeCount b, ∃ star < 2^b, m = extendMask b old star := by
  let base := 2^edgeCount b
  have pos : 0 < base := Nat.two_pow_pos _
  have top : m < base*2^b := by simpa only [base,edgeCount,Nat.pow_add] using h
  refine ⟨m%base,Nat.mod_lt _ pos,m/base,?_,?_⟩
  · exact (Nat.div_lt_iff_lt_mul pos).mpr (by rwa [Nat.mul_comm])
  · exact (Nat.mod_add_div m base).symm

#print axioms exists_mask_labeling
#print axioms split_mask
end Graph189ExteriorMask
