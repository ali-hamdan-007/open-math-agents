import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push

open Finset
namespace Graph189ContactGroupCensus
variable {E : Type*} [Fintype E] [DecidableEq E] {q : ℕ}

/-- For all path marks in order, record the first mark and each subsequent mark
where one can enter from the preceding mark using two distinct exterior ports. -/
noncomputable def beginnings (ports : Fin q → Finset E) : Finset (Fin q) := by
  classical
  exact univ.filter fun i => ∀ j : Fin q, j.val+1=i.val →
    ∃ a∈ports j, ∃ b∈ports i, a≠b

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

/-- Uniformity from the contact-gap census. This also covers equal numbers of
required marks and exterior vertices, when an extra bipartite matching is impossible. -/
theorem rows_uniform (ports : Fin q → Finset E) (present : ∀ i, (ports i).Nonempty)
    (u : ℕ) (two : 2≤u) (balanced : u≤Fintype.card E)
    (rows : ∀ x : E, u≤(univ.filter fun i => x∈ports i).card)
    (room : q+(beginnings ports).card*Fintype.card E+Fintype.card E+1+2 ≤
      (u+1)*(Fintype.card E+1)+u) : q=u ∧ ∀ i, ports i=univ := by
  classical
  let B := beginnings ports
  have subsetAll : B.card≤q := by
    have := card_le_card (subset_univ B)
    simpa using this
  have factor : (u+1)*(Fintype.card E+1)=u*Fintype.card E+u+Fintype.card E+1 := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
    omega
  rw [factor] at room
  have bound : B.card≤u := by
    by_contra! bigger
    have prod : (u+1)*Fintype.card E≤B.card*Fintype.card E := Nat.mul_le_mul_right _ bigger
    rw [Nat.add_mul,one_mul] at prod
    change q+B.card*Fintype.card E+Fintype.card E+1+2≤_ at room
    omega
  have cost (enough : u≤B.card) : q+2≤2*u := by
    have prod := Nat.mul_le_mul_right (Fintype.card E) enough
    change q+B.card*Fintype.card E+Fintype.card E+1+2≤_ at room
    omega
  by_cases allprivate : ∀ x : E, ∃ i, ports i={x}
  · choose mark starts own using fun x => first_private_begins ports present (allprivate x)
    have inj : Function.Injective mark := by
      intro x y eq
      have sets : ({x} : Finset E)={y} := (own x).symm.trans ((congrArg ports eq).trans (own y))
      simpa using sets
    let image := univ.image mark
    have inside : image⊆B := by
      intro i hi
      obtain ⟨x,_,rfl⟩ := mem_image.mp hi
      exact starts _
    have count : image.card=Fintype.card E := by
      simp [image,card_image_of_injective _ inj]
    have covers : B=image := (eq_of_subset_of_card_le inside (by omega)).symm
    have singleton (i : Fin q) : ∃ x, ports i={x} := by
      by_contra! none
      have extra : 2≤(ports i).card := by
        by_contra! small
        have positive := card_pos.mpr (present i)
        obtain ⟨w,hw⟩ := card_eq_one.mp (by omega : (ports i).card=1)
        exact none w hw
      have start : i∈B := shared_begins ports present extra
      rw [covers] at start
      obtain ⟨w,_,rfl⟩ := mem_image.mp start
      exact none w (own w)
    have available : 1<(univ : Finset E).card := by simpa using (show 1<Fintype.card E by omega)
    obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<(univ : Finset E).card)
    obtain ⟨y,hy,ne⟩ := exists_mem_ne available x
    let X := univ.filter fun i => x∈ports i
    let Y := univ.filter fun i => y∈ports i
    have disjoint : Disjoint X Y := Finset.disjoint_left.mpr (by
      intro i hi hj
      obtain ⟨w,hw⟩ := singleton i
      have hxi := (mem_filter.mp hi).2
      have hyi := (mem_filter.mp hj).2
      rw [hw,mem_singleton] at hxi hyi
      exact ne (hyi.trans hxi.symm))
    have total := card_le_card (subset_univ (X∪Y))
    rw [card_union_of_disjoint disjoint,card_univ,Fintype.card_fin] at total
    have first : u≤X.card := rows x
    have second : u≤Y.card := rows y
    have budget := cost (by rw [covers,count]; exact balanced)
    omega
  · push Not at allprivate
    obtain ⟨x,none⟩ := allprivate
    let X := univ.filter fun i => x∈ports i
    have shared (i : Fin q) (hi : i∈X) : 2≤(ports i).card := by
      have hxi := (mem_filter.mp hi).2
      have positive := card_pos.mpr (present i)
      by_contra! small
      obtain ⟨w,hw⟩ := card_eq_one.mp (by omega : (ports i).card=1)
      rw [hw,mem_singleton] at hxi
      exact none i (by simpa [hxi] using hw)
    have inc : X⊆B := fun _ hi => shared_begins ports present (shared _ hi)
    have whole : X=B := eq_of_subset_of_card_le inc (bound.trans (rows x))
    have allshared (i : Fin q) : 2≤(ports i).card := by
      by_contra! small
      have positive := card_pos.mpr (present i)
      obtain ⟨w,hw⟩ := card_eq_one.mp (by omega : (ports i).card=1)
      obtain ⟨j,hj,single⟩ := first_private_begins ports present ⟨i,hw⟩
      have contradiction := shared j (whole.symm ▸ hj)
      simp [single] at contradiction
    have total : B=univ := eq_univ_iff_forall.mpr (fun i => shared_begins ports present (allshared i))
    have qBound : q≤u := by simpa [total] using bound
    have qLower : u≤q := (rows x).trans (by simpa using card_le_card (subset_univ X))
    refine ⟨by omega,?_⟩
    intro i
    apply eq_univ_iff_forall.mpr
    intro y
    let Y := univ.filter fun j => y∈ports j
    have all : Y=univ := eq_of_subset_of_card_le (subset_univ Y) (by simpa using qBound.trans (rows y))
    exact (mem_filter.mp (show i∈Y from all.symm ▸ mem_univ i)).2

#print axioms rows_uniform
end Graph189ContactGroupCensus
