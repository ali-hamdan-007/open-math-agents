import Graph189Bipartite

namespace Graph189Bipartite
abbrev Six := Fin 3 ⊕ Fin 3

def table3 (a b c : Fin 8) (i j : Fin 3) : Bool :=
  (if i = 0 then a.val else if i = 1 then b.val else c.val).testBit j.val

def row3 (T : Fin 3 → Fin 3 → Bool) (v : Six) (i : Fin 3) : Bool :=
  match v with
  | .inl j => T j i
  | .inr j => T i j

def high3 (T : Fin 3 → Fin 3 → Bool) (v : Six) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ row3 T v i = true ∧ row3 T v j = true

def accept3 (T : Fin 3 → Fin 3 → Bool) : Prop :=
  (∀ v : Six, ∃ i : Fin 3, row3 T v i = true) ∧
  ∀ v w : Six, v ≠ w → high3 T v ∨ high3 T w

def route3 (T : Fin 3 → Fin 3 → Bool) (l₀ l₁ l₂ r₀ r₁ r₂ : Fin 3) : Prop :=
  l₀ ≠ l₁ ∧ l₀ ≠ l₂ ∧ l₁ ≠ l₂ ∧ r₀ ≠ r₁ ∧ r₀ ≠ r₂ ∧ r₁ ≠ r₂ ∧
  T l₀ r₀ = true ∧ T l₁ r₀ = true ∧ T l₁ r₁ = true ∧
  T l₂ r₁ = true ∧ T l₂ r₂ = true

instance (T) (v) : Decidable (high3 T v) := by unfold high3; infer_instance
instance (T) : Decidable (accept3 T) := by unfold accept3; infer_instance
instance (T) (l₀ l₁ l₂ r₀ r₁ r₂) : Decidable (route3 T l₀ l₁ l₂ r₀ r₁ r₂) := by
  unfold route3; infer_instance

set_option maxHeartbeats 4000000 in
theorem all_tables3 : ∀ a b c : Fin 8, accept3 (table3 a b c) →
    ∃ l₀ l₁ l₂ r₀ r₁ r₂, route3 (table3 a b c) l₀ l₁ l₂ r₀ r₁ r₂ := by
  decide +kernel


theorem encode_row3 (R : Fin 3 → Bool) :
    ∃ n : Fin 8, ∀ i : Fin 3, n.val.testBit i.val = R i := by
  let num := (if R 0 then 1 else 0) + (if R 1 then 2 else 0) + (if R 2 then 4 else 0)
  have hnum : num < 8 := by
    cases h0 : R 0 <;> cases h1 : R 1 <;> cases h2 : R 2 <;> simp [num,h0,h1,h2]
  refine ⟨⟨num,hnum⟩,?_⟩
  intro i
  cases h0 : R 0 <;> cases h1 : R 1 <;> cases h2 : R 2 <;>
    fin_cases i <;> simp [num,h0,h1,h2,Nat.testBit]

theorem some_route3 (T : Fin 3 → Fin 3 → Bool) (hT : accept3 T) :
    ∃ l₀ l₁ l₂ r₀ r₁ r₂, route3 T l₀ l₁ l₂ r₀ r₁ r₂ := by
  obtain ⟨a,ha⟩ := encode_row3 (T 0)
  obtain ⟨b,hb⟩ := encode_row3 (T 1)
  obtain ⟨c,hc⟩ := encode_row3 (T 2)
  have he : table3 a b c = T := by
    funext i j
    fin_cases i
    · exact ha j
    · exact hb j
    · exact hc j
  rw [← he] at hT ⊢
  exact all_tables3 a b c hT

#print axioms some_route3
end Graph189Bipartite
