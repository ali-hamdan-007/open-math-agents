import Mathlib.Data.Finset.Card

namespace Graph189SupportClassification

/-- At most one label is present on the first port and absent on the second. -/
def OneDifference {ι α : Type*} (H : ι → α → Prop) : Prop :=
  ∀ i j a b, H i a → ¬ H j a → H i b → ¬ H j b → a = b

/-- A family of pairwise close supports consists, after removing its common
core and restricting to the union, of singletons/empty sets or of
complements of singletons/full sets. No finiteness or rank assumption. -/
theorem classify {ι α : Type*} {H : ι → α → Prop} (h : OneDifference H) :
    (∀ i a b, H i a → (∃ j, ¬ H j a) → H i b → (∃ j, ¬ H j b) → a = b) ∨
    (∀ i a b, (∃ j, H j a) → ¬ H i a → (∃ j, H j b) → ¬ H i b → a = b) := by
  classical
  by_cases singles : ∀ i a b, H i a → (∃ j, ¬ H j a) → H i b → (∃ j, ¬ H j b) → a = b
  · exact Or.inl singles
  right
  push Not at singles
  obtain ⟨p,x,y,hpx,⟨q,hqx⟩,hpy,⟨r,hry⟩,hxy⟩ := singles
  have keepQ {z} (hz : H p z) (hne : x ≠ z) : H q z := by
    by_contra hz'
    exact hne (h p q x z hpx hqx hz hz')
  have keepR {z} (hz : H p z) (hne : y ≠ z) : H r z := by
    by_contra hz'
    exact hne (h p r y z hpy hry hz hz')
  have hqy := keepQ hpy hxy
  have hrx := keepR hpx hxy.symm
  have outside {z} (hz : ∃ t, H t z) (hpz : ¬ H p z) : H q z ∧ H r z := by
    obtain ⟨t,htz⟩ := hz
    have hxz : x ≠ z := fun he => hpz (he ▸ hpx)
    have hyz : y ≠ z := fun he => hpz (he ▸ hpy)
    have transfer : H q z ↔ H r z := by
      constructor
      · intro hqz
        by_contra hrz
        exact hyz (h q r y z hqy hry hqz hrz)
      · intro hrz
        by_contra hqz
        exact hxz (h r q x z hrx hqx hrz hqz)
    by_contra denied
    have hqz : ¬ H q z := fun hqz => denied ⟨hqz,transfer.mp hqz⟩
    have hrz : ¬ H r z := fun hrz => hqz (transfer.mpr hrz)
    have htx : ¬ H t x := fun htx => hxz (h t q x z htx hqx htz hqz)
    have hty : ¬ H t y := fun hty => hyz (h t r y z hty hry htz hrz)
    exact hxy (h p t x y hpx htx hpy hty)
  have contain {i z} (hz : ∃ t, H t z) (hpz : ¬ H p z) (hiz : ¬ H i z) :
      ∀ v, H p v → H i v := by
    obtain ⟨hqz,hrz⟩ := outside hz hpz
    intro v hpv
    have hvz : v ≠ z := fun he => hpz (he ▸ hpv)
    by_contra hiv
    by_cases hxv : x = v
    · subst v
      exact hvz (h r i x z hrx hiv hrz hiz)
    · exact hvz (h q i v z (keepQ hpv hxv) hiv hqz hiz)
  intro i a b ha hia hb hib
  by_cases hpa : H p a
  · by_cases hpb : H p b
    · exact h p i a b hpa hia hpb hib
    · exact (hia (contain hb hpb hib a hpa)).elim
  · by_cases hpb : H p b
    · exact (hib (contain ha hpa hia b hpb)).elim
    · exact h q p a b (outside ha hpa).1 hpa (outside hb hpb).1 hpb

#print axioms classify
end Graph189SupportClassification
