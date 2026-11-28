import Graph189ContactGroupCensus
import Graph189ContactIntervals

open Finset
namespace Graph189ContactGroupCensus

section HighRows
variable {E : Type*} [Fintype E] [DecidableEq E] {q : ℕ}

omit [Fintype E] in
private theorem shared_begins (ports : Fin q → Finset E) (present : ∀ i, (ports i).Nonempty)
    {i : Fin q} (shared : 2≤(ports i).card) : i∈beginnings ports := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro j _
  obtain ⟨a,ha⟩ := present j
  obtain ⟨b,hb,ne⟩ := exists_mem_ne (by omega : 1<(ports i).card) a
  exact ⟨a,ha,b,hb,ne.symm⟩

omit [Fintype E] in
private theorem first_private_begins (ports : Fin q → Finset E) (present : ∀ i, (ports i).Nonempty)
    {x : E} (exists_private : ∃ i, ports i={x}) :
    ∃ i∈beginnings ports, ports i={x} := by
  classical
  let A := univ.filter fun i => ports i={x}
  have nonempty : A.Nonempty := by
    obtain ⟨i,hi⟩ := exists_private
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  let i := A.min' nonempty
  have only : ports i={x} := (mem_filter.mp (A.min'_mem nonempty)).2
  refine ⟨i,mem_filter.mpr ⟨mem_univ _,?_⟩,only⟩
  intro j step
  have before : j<i := by change j.val<i.val; omega
  have earlier : ports j≠{x} := fun hj => (not_lt_of_ge
    (A.min'_le j (mem_filter.mpr ⟨mem_univ _,hj⟩))) before
  obtain ⟨a,ha,ne⟩ : ∃ a∈ports j, a≠x := by
    by_contra! all
    obtain ⟨w,hw⟩ := present j
    apply earlier
    ext y
    simp only [mem_singleton]
    exact ⟨all y,fun hy => by simpa [hy,all w hw] using hw⟩
  exact ⟨a,ha,x,by simp [only],ne⟩

/-- The ordinary path census needs the row bound only on the high exterior
vertices. The shorter room inequality follows because every legal gap can
be exchanged, without a protected vertex. -/
theorem rows_uniform_on_high (ports : Fin q → Finset E) (present : ∀ i, (ports i).Nonempty)
    (H : Finset E) (u m : ℕ) (two : 2 ≤ u) (many : u ≤ H.card) (size : u < m)
    (private_overflow : 3 ≤ u ∨ u < H.card)
    (rows : ∀ x ∈ H, u ≤ (univ.filter fun i => x ∈ ports i).card)
    (room : q + (beginnings ports).card * m ≤ u * m + 2 * u) :
    q = u ∧ ∀ i, H ⊆ ports i := by
  classical
  let B := beginnings ports
  have pos : H.Nonempty := card_pos.mp (by omega)
  obtain ⟨x,hx⟩ := pos
  let marks (v : E) := univ.filter fun i => v ∈ ports i
  have marks_bound (v : E) : (marks v).card ≤ q := by
    simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (marks v))
  have qLower : u ≤ q := (rows x hx).trans (marks_bound x)
  have groupBound : B.card ≤ u := by
    by_contra! bigger
    have cost := Nat.mul_le_mul_right m (show u + 1 ≤ B.card by omega)
    rw [Nat.add_mul,one_mul] at cost
    change q + B.card * m ≤ u * m + 2 * u at room
    omega
  have positionBound (enough : u ≤ B.card) : q ≤ 2 * u := by
    have cost := Nat.mul_le_mul_right m enough
    change q + B.card * m ≤ u * m + 2 * u at room
    omega
  by_cases allPrivate : ∀ v ∈ H, ∃ i, ports i = {v}
  · choose mark begins owner using fun v : H => first_private_begins ports present
      (allPrivate v.val v.property)
    have injective : Function.Injective mark := by
      intro i j equal
      apply Subtype.ext
      have same : ({i.val} : Finset E) = {j.val} :=
        (owner i).symm.trans ((congrArg ports equal).trans (owner j))
      simpa using same
    let P := (univ : Finset H).image mark
    have included : P ⊆ B := by
      intro i hi
      obtain ⟨j,_,rfl⟩ := mem_image.mp hi
      exact begins j
    have count : P.card = H.card := by
      simp [P,card_image_of_injective _ injective,Fintype.card_coe]
    have upper := card_le_card included
    have exactGroups : B = P := (eq_of_subset_of_card_le included (by omega)).symm
    have single (i : Fin q) : ∃ v, ports i = {v} := by
      by_contra! none
      have shared : 2 ≤ (ports i).card := by
        by_contra! few
        have nonempty := card_pos.mpr (present i)
        obtain ⟨v,hv⟩ := card_eq_one.mp (show (ports i).card = 1 by omega)
        exact none v hv
      have member : i ∈ B := shared_begins ports present shared
      rw [exactGroups] at member
      obtain ⟨v,_,rfl⟩ := mem_image.mp member
      exact none _ (owner v)
    have apart {v w : E} (different : v ≠ w) : Disjoint (marks v) (marks w) :=
      Finset.disjoint_left.mpr (by
        intro i hv hw
        obtain ⟨a,actual⟩ := single i
        have hi := (mem_filter.mp hv).2
        have hj := (mem_filter.mp hw).2
        rw [actual,mem_singleton] at hi hj
        exact different (hi.trans hj.symm))
    have three : 3 ≤ u := private_overflow.resolve_right (by omega)
    obtain ⟨y,hy,hxy⟩ := exists_mem_ne (show 1 < H.card by omega) x
    have rest : 1 < (H.erase x).card := by rw [card_erase_of_mem hx]; omega
    obtain ⟨z,hz,hyz⟩ := exists_mem_ne rest y
    obtain ⟨hxz,hz'⟩ := mem_erase.mp hz
    have union_disjoint : Disjoint (marks x ∪ marks y) (marks z) := by
      apply Finset.disjoint_left.mpr
      intro i hit last
      rcases mem_union.mp hit with first | second
      · exact Finset.disjoint_left.mp (apart hxz.symm) first last
      · exact Finset.disjoint_left.mp (apart hyz.symm) second last
    have slots := card_le_card (subset_univ ((marks x ∪ marks y) ∪ marks z))
    rw [card_union_of_disjoint union_disjoint,card_union_of_disjoint (apart hxy.symm),
      card_univ,Fintype.card_fin] at slots
    have first := rows x hx
    have second := rows y hy
    have third := rows z hz'
    change u ≤ (marks x).card at first
    change u ≤ (marks y).card at second
    change u ≤ (marks z).card at third
    have cost := positionBound (by omega)
    omega
  · push Not at allPrivate
    obtain ⟨v,hv,none⟩ := allPrivate
    have shared (i : Fin q) (hit : i ∈ marks v) : 2 ≤ (ports i).card := by
      have vertex := (mem_filter.mp hit).2
      have nonempty := card_pos.mpr (present i)
      by_contra! few
      obtain ⟨w,hw⟩ := card_eq_one.mp (show (ports i).card = 1 by omega)
      rw [hw,mem_singleton] at vertex
      exact none i (by simpa only [vertex] using hw)
    have included : marks v ⊆ B :=
      fun i hi => shared_begins ports present (shared i hi)
    have whole : marks v = B := eq_of_subset_of_card_le included (groupBound.trans (rows v hv))
    have allShared (i : Fin q) : 2 ≤ (ports i).card := by
      by_contra! few
      have nonempty := card_pos.mpr (present i)
      obtain ⟨w,hw⟩ := card_eq_one.mp (show (ports i).card = 1 by omega)
      obtain ⟨j,hj,actual⟩ := first_private_begins ports present ⟨i,hw⟩
      have contradiction := shared j (whole.symm ▸ hj)
      simp [actual] at contradiction
    have total : B = univ := eq_univ_iff_forall.mpr (fun i => shared_begins ports present (allShared i))
    have qUpper : q ≤ u := by simpa only [total,card_univ,Fintype.card_fin] using groupBound
    refine ⟨le_antisymm qUpper qLower,?_⟩
    intro i w hw
    have all : marks w = univ :=
      eq_of_subset_of_card_le (subset_univ _) (by
        simpa only [card_univ,Fintype.card_fin] using qUpper.trans (rows w hw))
    exact (mem_filter.mp (show i ∈ marks w from all.symm ▸ mem_univ i)).2

#print axioms rows_uniform_on_high

end HighRows

/-- In an ordinary longest path, every interval at a group boundary or
either end has room for the full exterior route. -/
theorem ordinary_path_group_census {E : Type*} [Fintype E] [DecidableEq E]
    {q m L : ℕ} (ports : Fin q → Finset E) (f : ℕ → ℕ)
    (zero : f 0 = 0) (ending : f (q+1) = L+1)
    (strict : ∀ i j, i < j → j ≤ q+1 → f i < f j)
    (detour : ∀ i ∈ insert q ((beginnings ports).image Fin.val),
      m ≤ f (i+1) - f i - 1) :
    q + ((beginnings ports).card + 1) * m ≤ L := by
  classical
  let A := (beginnings ports).image Fin.val
  let I := insert q A
  let h (i : ℕ) := f (i+1) - f i - 1
  have real (i : ℕ) (member : i ∈ A) : i < q := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp member
    exact j.isLt
  have miss : q ∉ A := fun member => (lt_irrefl _) (real _ member)
  have number : I.card = (beginnings ports).card + 1 := by
    rw [show I = insert q A from rfl,card_insert_of_notMem miss,
      show A.card = (beginnings ports).card from card_image_of_injective _ Fin.val_injective]
  have included : I ⊆ range (q+1) := by
    intro i hi
    apply mem_range.mpr
    rcases mem_insert.mp hi with rfl | inA
    · omega
    · exact (real i inA).trans (Nat.lt_succ_self q)
  have minimum := sum_le_sum (s:=I) (f:=fun _ => m) (g:=h) detour
  rw [sum_const,Nat.nsmul_eq_mul,number] at minimum
  have total := sum_le_sum_of_subset_of_nonneg (f:=h) included (fun i _ _ => Nat.zero_le _)
  have sum := width_sum f q zero strict
  rw [ending] at sum
  change (∑ i ∈ range (q+1),h i) + (q+1) = L+1 at sum
  omega

#print axioms ordinary_path_group_census
end Graph189ContactGroupCensus
