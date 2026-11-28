import Graph189TwoMarkShift

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189FourNarrowPorts

/-- Two rows with two or more marks and distinct-row spacing four have no
choice inside the five-position window from 3 through 7. -/
theorem two_rows (A B : Finset ℕ) (a2 : 2 ≤ A.card) (b2 : 2 ≤ B.card)
    (aw : ∀ a∈A, 3 ≤ a ∧ a ≤ 7) (bw : ∀ b∈B, 3 ≤ b ∧ b ≤ 7)
    (spacing : ∀ a∈A, ∀ b∈B, a=b ∨ a+4 ≤ b ∨ b+4 ≤ a) :
    A={3,7} ∧ B={3,7} := by
  have row (X Y : Finset ℕ) (x2 : 2 ≤ X.card) (y2 : 2 ≤ Y.card)
      (wx : ∀ i∈X, 3 ≤ i ∧ i ≤ 7) (wy : ∀ j∈Y, 3 ≤ j ∧ j ≤ 7)
      (apart : ∀ i∈X, ∀ j∈Y, i=j ∨ i+4 ≤ j ∨ j+4 ≤ i) : X={3,7} := by
    apply eq_of_subset_of_card_le _ (by simpa using x2)
    intro i hi
    obtain ⟨j,hj,ne⟩ := exists_mem_ne y2 i
    have := wx i hi
    have := wy j hj
    have := apart i hi j hj
    simp only [mem_insert,mem_singleton]
    omega
  exact ⟨row A B a2 b2 aw bw spacing,row B A b2 a2 bw aw (by
    intro i hi j hj
    have := spacing j hj i hi
    omega)⟩

/-- A row containing three marks exhausts the four-witness bound, so both
successive gaps in every ordered triple are exactly two. -/
theorem three_marks_exact {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (outside : x∉p.support) (quota : (univ.filter (fun z => G.dist x z=2)).card ≤ 4)
    {i j l : ℕ} (hi : i∈contactPositions p x) (hj : j∈contactPositions p x) (hl : l∈contactPositions p x)
    (ij : i<j) (jl : j<l) : i+2=j ∧ j+2=l := by
  classical
  have apart {m n : ℕ} (hm : m∈contactPositions p x) (hn : n∈contactPositions p x) (lt : m<n) : m+2 ≤ n := by
    obtain ⟨mv,me⟩ := (mem_contactPositions p x m).mp hm
    obtain ⟨nv,ne⟩ := (mem_contactPositions p x n).mp hn
    exact omitted_contact_spacing p hp longest outside ⟨m,mv⟩ ⟨n,nv⟩ lt
      (by simpa [get_at] using me) (by simpa [get_at] using ne)
  have first := apart hi hj ij
  have second := apart hj hl jl
  obtain ⟨ip,ib,im,ia⟩ := shifted_contact p hp longest outside hi
  obtain ⟨jp,jb,jm,ja⟩ := shifted_contact p hp longest outside hj
  obtain ⟨lp,lb,lm,la⟩ := shifted_contact p hp longest outside hl
  let A : Finset ℕ := {i-1,i+1,j+1,l+1}
  have acard : A.card=4 := by
    dsimp [A]
    rw [card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_singleton]; omega),card_singleton]
  have full (s : ℕ) (inPath : s < p.support.length) (two : G.dist x (p.getVert s)=2) : s∈A := by
    by_contra missing
    let S := insert s A
    have good (t : ℕ) (ht : t∈S) : t < p.support.length ∧ G.dist x (p.getVert t)=2 := by
      simp only [S,A,mem_insert,mem_singleton] at ht
      rcases ht with rfl|rfl|rfl|rfl|rfl <;> constructor <;> first | assumption | omega
    have inj : Set.InjOn p.getVert (S : Set ℕ) := by
      intro m hm n hn eq
      have := (good m hm).1
      have := (good n hn).1
      have := p.length_support
      exact hp.getVert_injOn (by change m ≤ p.length; omega) (by change n ≤ p.length; omega) eq
    have sub : S.image p.getVert ⊆ univ.filter (fun z => G.dist x z=2) := by
      intro z hz
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨mem_univ _,(good t ht).2⟩
    have c := (card_le_card sub).trans quota
    rw [card_image_of_injOn inj,show S=insert s A from rfl,card_insert_of_notMem missing,acard] at c
    omega
  have m := full (j-1) (by omega) jm
  have n := full (l-1) (by omega) lm
  simp only [A,mem_insert,mem_singleton] at m n
  omega

#print axioms three_marks_exact
end Graph189FourNarrowPorts
