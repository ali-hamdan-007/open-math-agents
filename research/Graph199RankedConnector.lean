import Graph199CliqueSeparator

open Finset SimpleGraph

namespace Graph199

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A walk crossing a level must visit its designated vertex if all ascending
edges cross one level and land on that vertex. -/
private theorem hit_rank {S : Set V} {d : ℕ} (rank : S → ℕ)
    (center : Fin (d+1) ↪ S)
    (hstep : ∀ x y : S, (G.induce S).Adj x y → rank x < rank y →
      rank y = rank x+1 ∧ ∃ j : Fin (d+1), rank y = j.val ∧ y = center j)
    {x y : S} (p : (G.induce S).Walk x y) (i : Fin (d+1))
    (hx : rank x < i.val) (hy : i.val ≤ rank y) : center i ∈ p.support := by
  induction p with
  | nil => omega
  | @cons a b c hab p ih =>
    by_cases hb : rank b < i.val
    · exact List.mem_cons_of_mem _ (ih hb hy)
    · have he : rank a < rank b := by omega
      obtain ⟨hne,j,hj,hbj⟩ := hstep a b hab he
      have hji : j = i := Fin.ext (by omega)
      subst j
      exact List.mem_cons_of_mem _ (hbj ▸ p.start_mem_support)

/-- An induced graph with mandatory level crossings has an induced path
through all designated vertices from its first to its last level. -/
theorem ranked_connector {S : Set V} {d : ℕ} (rank : S → ℕ)
    (center : Fin (d+1) ↪ S) (hc : ∀ i, rank (center i) = i.val)
    (hstep : ∀ x y : S, (G.induce S).Adj x y → rank x < rank y →
      rank y = rank x+1 ∧ ∃ j : Fin (d+1), rank y = j.val ∧ y = center j)
    (hreach : (G.induce S).Reachable (center 0) (center (Fin.last d))) :
    ∃ B : Finset V, (∀ x ∈ B, x ∈ S) ∧ (∀ i, (center i).val ∈ B) ∧
      d+1 ≤ B.card ∧ (G.induce (B : Set V)).IsTree := by
  classical
  obtain ⟨p,_,hpLen⟩ := hreach.exists_path_of_dist
  let B₀ := p.support.toFinset
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let B := B₀.map f
  have hmem (i : Fin (d+1)) : center i ∈ p.support := by
    by_cases h0 : i = 0
    · subst i
      exact p.start_mem_support
    · apply hit_rank rank center hstep p i
      · rw [hc]
        have hp : i.val ≠ 0 := fun he => h0 (Fin.ext he)
        change 0 < i.val
        omega
      · rw [hc]
        change i.val ≤ d
        omega
  have hSet (x : V) (hx : x ∈ B) : x ∈ S := by
    obtain ⟨y,_,rfl⟩ := mem_map.mp hx
    exact y.property
  have hcenter (i : Fin (d+1)) : (center i).val ∈ B :=
    mem_map.mpr ⟨center i,List.mem_toFinset.mpr (hmem i),rfl⟩
  have hcard : d+1 ≤ B.card := by
    have hsub : univ.map (center.trans f) ⊆ B := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_map.mp hx
      exact hcenter i
    simpa using card_le_card hsub
  have htree : ((G.induce S).induce (B₀ : Set S)).IsTree :=
    p.induce_support_isTree_of_length_eq_dist hpLen
  let g : ↥(B₀ : Set S) → ↥(B : Set V) := fun a => ⟨a.val.val,
    mem_map.mpr ⟨a.val,a.property,rfl⟩⟩
  have hgi : Function.Injective g := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥(B : Set V) => x.val) he))
  have hgs : Function.Surjective g := by
    intro a
    obtain ⟨x,hx,he⟩ := mem_map.mp a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let iso : (G.induce S).induce (B₀ : Set S) ≃g G.induce (B : Set V) :=
    ⟨Equiv.ofBijective g ⟨hgi,hgs⟩,by intro x y; rfl⟩
  exact ⟨B,hSet,hcenter,hcard,iso.isTree_iff.mp htree⟩

#print axioms ranked_connector

end Graph199
