
namespace C8SingleVertex

/-- A cycle with vertices 0 through 7, and one additional vertex 8 whose
adjacencies to the cycle are specified by the bit mask. -/
def adj (mask : Fin 256) (u v : Fin 9) : Bool :=
  if u.val = 8 then decide (v.val < 8) && mask.val.testBit v.val
  else if v.val = 8 then mask.val.testBit u.val
  else (u.val + 1) % 8 == v.val || (v.val + 1) % 8 == u.val

def nearThree (edges : Fin 9 → Fin 9 → Bool) (u v : Fin 9) : Prop :=
  u = v ∨ edges u v = true ∨
  (∃ a : Fin 9, edges u a = true ∧ edges a v = true) ∨
  (∃ a b : Fin 9, edges u a = true ∧ edges a b = true ∧ edges b v = true)

instance (edges : Fin 9 → Fin 9 → Bool) (u v : Fin 9) :
    Decidable (nearThree edges u v) := by
  unfold nearThree
  infer_instance

private theorem nearThree_mono {e f : Fin 9 → Fin 9 → Bool} {u v : Fin 9}
    (h : ∀ a b, e a b = true → f a b = true) :
    nearThree e u v → nearThree f u v := by
  intro hnear
  rcases hnear with he | he | ⟨a, ha, hb⟩ | ⟨a, b, ha, hb, hc⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl (h _ _ he))
  · exact Or.inr (Or.inr (Or.inl ⟨a, h _ _ ha, h _ _ hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, b, h _ _ ha, h _ _ hb, h _ _ hc⟩))

def cycleStep (i j : Fin 8) (forward : Bool) : Fin 9 :=
  ⟨(i.val + (if forward then j.val else 8 - j.val)) % 8,
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩

/-- The sixteen candidate paths going from the extra vertex in one direction
for seven cycle vertices. -/
def neighboringPath (start : Fin 8) (forward : Bool) : Fin 8 → Fin 9 :=
  fun i => if i.val = 0 then 8 else
    cycleStep start ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ forward

def inducesP8 (mask : Fin 256) (path : Fin 8 → Fin 9) : Prop :=
  (∀ i j, path i = path j → i = j) ∧
  ∀ i j, adj mask (path i) (path j) = true ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

instance (mask : Fin 256) (path : Fin 8 → Fin 9) : Decidable (inducesP8 mask path) := by
  unfold inducesP8
  infer_instance

def oppositeAtDistanceTwo (mask : Fin 256) (i : Fin 8) : Prop :=
  mask.val.testBit i.val = true ∧ mask.val.testBit ((i.val + 2) % 8) = true

instance (mask : Fin 256) (i : Fin 8) : Decidable (oppositeAtDistanceTwo mask i) := by
  unfold oppositeAtDistanceTwo
  infer_instance

def shortcut (mask : Fin 256) (i : Fin 8) : Prop :=
  mask.val.testBit i.val = true ∧
    (mask.val.testBit ((i.val + 3) % 8) = true ∨
     mask.val.testBit ((i.val + 4) % 8) = true ∨
     mask.val.testBit ((i.val + 5) % 8) = true)

instance (mask : Fin 256) (i : Fin 8) : Decidable (shortcut mask i) := by
  unfold shortcut
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem contact_mask_trichotomy :
    ∀ mask : Fin 256, mask.val = 0 ∨ (∃ i, oppositeAtDistanceTwo mask i) ∨
      (∃ i forward, inducesP8 mask (neighboringPath i forward)) ∨
      (∃ i, shortcut mask i) := by decide

private def twoContacts (i j : Fin 8) (u v : Fin 9) : Bool :=
  if u.val = 8 then (v.val == i.val || v.val == j.val)
  else if v.val = 8 then (u.val == i.val || u.val == j.val)
  else (u.val + 1) % 8 == v.val || (v.val + 1) % 8 == u.val

private theorem twoContacts_mono {mask : Fin 256} {i j : Fin 8}
    (hi : mask.val.testBit i.val = true) (hj : mask.val.testBit j.val = true) :
    ∀ u v, twoContacts i j u v = true → adj mask u v = true := by
  intro u v
  unfold twoContacts adj
  split
  · intro h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · have hv := beq_iff_eq.mp h
      simp [hv, i.isLt, hi]
    · have hv := beq_iff_eq.mp h
      simp [hv, j.isLt, hj]
  · split
    · intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · simpa [beq_iff_eq.mp h] using hi
      · simpa [beq_iff_eq.mp h] using hj
    · exact id

private def step (i : Fin 8) (d : Nat) : Fin 8 :=
  ⟨(i.val + d) % 8, Nat.mod_lt _ (by decide)⟩

private def coreVertex (i : Fin 8) : Fin 9 :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem contact_pair_bounds :
    ∀ (i : Fin 8) (d : Fin 3) (v : Fin 9),
      nearThree (twoContacts i (step i (d.val + 3))) (coreVertex i) v := by decide

theorem shortcuts_bound (mask : Fin 256) (i : Fin 8) (hs : shortcut mask i) :
    ∀ v : Fin 9, nearThree (adj mask) (coreVertex i) v := by
  intro v
  obtain ⟨hi, h⟩ := hs
  rcases h with h | h | h
  · exact nearThree_mono (twoContacts_mono (j := step i 3) hi h)
      (contact_pair_bounds i 0 v)
  · exact nearThree_mono (twoContacts_mono (j := step i 4) hi h)
      (contact_pair_bounds i 1 v)
  · exact nearThree_mono (twoContacts_mono (j := step i 5) hi h)
      (contact_pair_bounds i 2 v)

/-- Adding a nonisolated vertex to an induced eight-cycle yields a four-cycle,
an induced eight-vertex path, or a cycle vertex within three steps of every
vertex of the nine-vertex extension. -/
theorem single_vertex_obstruction (mask : Fin 256) (hn : mask.val ≠ 0) :
    (∃ i, oppositeAtDistanceTwo mask i) ∨
    (∃ i forward, inducesP8 mask (neighboringPath i forward)) ∨
    (∃ u : Fin 9, u.val < 8 ∧ ∀ v : Fin 9, nearThree (adj mask) u v) := by
  rcases contact_mask_trichotomy mask with hz | hsq | hp | ⟨i, hi⟩
  · exact (hn hz).elim
  · exact Or.inl hsq
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ⟨⟨i.val, Nat.lt_trans i.isLt (by decide)⟩,
      i.isLt, shortcuts_bound mask i hi⟩)

#print axioms single_vertex_obstruction

end C8SingleVertex
