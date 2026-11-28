import Graph189FiveExteriorRoots
import Graph189RootedOneLow

open SimpleGraph Finset
namespace Graph189FiveOneLowRoots
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

private theorem confined {u a b c : W} (short : ¬∃ v, ∃ p : H.Walk u v, p.IsPath ∧ 5 ≤ p.support.length)
    (ua : H.Adj u a) (ab : H.Adj a b) (bc : H.Adj b c) (ub : u≠b) (uc : u≠c) (ac : a≠c) :
    H.neighborFinset c ⊆ {u,a,b} := by
  intro w hw
  by_contra skip
  have cw := (H.mem_neighborFinset _ _).mp hw
  have wu : w≠u := fun e => skip (by simp [e])
  have wa : w≠a := fun e => skip (by simp [e])
  have wb : w≠b := fun e => skip (by simp [e])
  let q : H.Walk u w := .cons ua (.cons ab (.cons bc (.cons cw .nil)))
  exact short ⟨w,q,Walk.IsPath.mk' (by simp [q,ua.ne,ab.ne,bc.ne,cw.ne,ub,uc,ac,wu.symm,wa.symm,wb.symm]),by simp [q]⟩

omit [DecidableEq W] in
private theorem high_neighbor (low : ∀ v, 2 ≤ H.degree v)
    (pair : ∀ a b, a≠b → 3 ≤ H.degree a ∨ 3 ≤ H.degree b) (u : W) :
    ∃ a, H.Adj u a ∧ 3 ≤ H.degree a := by
  obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (show 1 < (H.neighborFinset u).card from low u)
  rcases pair a b ab with high|high
  · exact ⟨a,(H.mem_neighborFinset _ _).mp ha,high⟩
  · exact ⟨b,(H.mem_neighborFinset _ _).mp hb,high⟩

/-- With minimum degree two and second-smallest degree at least three, a
graph of order five or six admits a five-vertex path from every root. -/
theorem five_from (low : ∀ v, 2 ≤ H.degree v)
    (pair : ∀ a b, a≠b → 3 ≤ H.degree a ∨ 3 ≤ H.degree b)
    (room : 5 ≤ Fintype.card W) (bound : Fintype.card W ≤ 6) (u : W) :
    ∃ v, ∃ p : H.Walk u v, p.IsPath ∧ 5 ≤ p.support.length := by
  classical
  by_contra short
  obtain ⟨a,ua,highA⟩ := high_neighbor H low pair u
  have rem : 2 ≤ ((H.neighborFinset a).erase u).card := by
    have eq := card_erase_add_one ((H.mem_neighborFinset a u).mpr ua.symm)
    rw [H.card_neighborFinset_eq_degree] at eq
    omega
  obtain ⟨b₁,h₁,b₂,h₂,ne⟩ := one_lt_card.mp rem
  obtain ⟨b,ub,ab,highB⟩ : ∃ b, u≠b ∧ H.Adj a b ∧ 3≤H.degree b := by
    rcases pair _ _ ne with h|h
    · exact ⟨_,(mem_erase.mp h₁).1.symm,(H.mem_neighborFinset _ _).mp (mem_erase.mp h₁).2,h⟩
    · exact ⟨_,(mem_erase.mp h₂).1.symm,(H.mem_neighborFinset _ _).mp (mem_erase.mp h₂).2,h⟩
  obtain ⟨c,hc⟩ := exists_mem_notMem_of_card_lt_card (s:={u,a}) (t:=H.neighborFinset b)
    (by rw [card_pair ua.ne,H.card_neighborFinset_eq_degree]; exact highB)
  have bc := (H.mem_neighborFinset _ _).mp hc.1
  have uc : u≠c := fun e => hc.2 (by simp [e])
  have ac : a≠c := fun e => hc.2 (by simp [e])
  have Nc := confined H short ua ab bc ub uc ac
  have edgeAC : H.Adj a c := by
    by_contra no
    have sub : H.neighborFinset c ⊆ {u,b} := by
      intro v hv
      have h := Nc hv
      simp only [mem_insert,mem_singleton] at h ⊢
      rcases h with rfl|rfl|rfl
      · exact Or.inl rfl
      · exact (no ((H.mem_neighborFinset _ _).mp hv).symm).elim
      · exact Or.inr rfl
    have eq : H.neighborFinset c={u,b} := eq_of_subset_of_card_le sub (by rw [card_pair ub]; exact low c)
    have ucE : H.Adj u c := ((H.mem_neighborFinset _ _).mp (by rw [eq]; simp)).symm
    have Na := confined H short ucE bc.symm ab.symm ub ua.ne ac.symm
    have full : H.neighborFinset a={u,c,b} := eq_of_subset_of_card_le Na (by simpa [uc,ub,bc.ne.symm] using highA)
    exact no ((H.mem_neighborFinset _ _).mp (by rw [full]; simp))
  have Nb := confined H short ua edgeAC bc.symm uc ub ab.ne
  have Nb' : H.neighborFinset b={u,a,c} := eq_of_subset_of_card_le Nb (by simpa [ua.ne,uc,ac] using highB)
  have ubE : H.Adj u b := ((H.mem_neighborFinset _ _).mp (by rw [Nb']; simp)).symm
  have Na := confined H short ubE bc edgeAC.symm uc ua.ne ab.ne.symm
  let T : Finset W := {u,a,b,c}
  have size : T.card=4 := by simp [T,ua.ne,ub,uc,ab.ne,ac,bc.ne]
  have boundary (x : W) (outside : x∉T) (t : W) (edge : H.Adj x t) (inside : t∈T) : t=u := by
    have no : x≠u ∧ x≠a ∧ x≠b ∧ x≠c := by simpa [T] using outside
    have e := (H.mem_neighborFinset _ _).mpr edge.symm
    simp only [T,mem_insert,mem_singleton] at inside
    rcases inside with rfl|rfl|rfl|rfl
    · rfl
    · have := Na e
      simp_all
    · have := Nb e
      simp_all
    · have := Nc e
      simp_all
  have debit (x : W) (ox : x∉T) : H.degree x ≤ Tᶜ.card := by
    have inc : insert x (H.neighborFinset x \ {u}) ⊆ Tᶜ := by
      intro t ht
      apply mem_compl.mpr
      rcases mem_insert.mp ht with rfl|inN
      · exact ox
      · intro hT
        obtain ⟨ed,tu⟩ := mem_sdiff.mp inN
        exact tu (mem_singleton.mpr (boundary x ox t ((H.mem_neighborFinset _ _).mp ed) hT))
    have cnt := card_le_card inc
    rw [card_insert_of_notMem (by simp)] at cnt
    have parts := card_sdiff_add_card_inter (H.neighborFinset x) ({u} : Finset W)
    have cap := card_le_card (inter_subset_right (s₁:=H.neighborFinset x) (s₂:={u}))
    rw [card_singleton] at cap
    rw [H.card_neighborFinset_eq_degree] at parts
    omega
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < Tᶜ.card by rw [card_compl,size]; omega)
  have dx := debit x (mem_compl.mp hx)
  have lx := low x
  obtain ⟨s,hs,t,ht,st⟩ := one_lt_card.mp (show 1 < Tᶜ.card by omega)
  have d₁ := debit s (mem_compl.mp hs)
  have d₂ := debit t (mem_compl.mp ht)
  have either := pair _ _ st
  rw [card_compl,size] at d₁ d₂
  omega

#print axioms five_from
end Graph189FiveOneLowRoots
