import Graph189DistanceLayers
import Graph189BipartiteStructure

namespace Graph189LocalOre
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def ballTwo (G : SimpleGraph V) (x : V) : Finset V :=
  Finset.univ.filter (fun v => G.dist x v ≤ 2)

noncomputable def farEven (G : SimpleGraph V) (x : V) : Finset V :=
  Finset.univ.filter (fun v => 4 ≤ G.dist x v ∧ Even (G.dist x v))

/-- Higher even distances reduce the available budget for the size of the
radius-two ball, even when its center has above-minimum degree. -/
theorem ball_budget_even (h : G.Connected) (x : V) :
    (ballTwo G x).card + (farEven G x).card ≤ G.degree x + G.distEven x := by
  let E := Finset.univ.filter (fun v => Even (G.dist x v))
  let N := G.neighborFinset x
  let L := Finset.univ.filter (fun v => G.dist x v = 2)
  have hdis : Disjoint (insert x L) (farEven G x) := by
    refine Finset.disjoint_left.mpr ?_
    intro y hy hz
    have hz' := (Finset.mem_filter.mp hz).2.1
    rcases Finset.mem_insert.mp hy with e | hy
    · subst y
      simp at hz'
    · have hd := (Finset.mem_filter.mp hy).2
      omega
  have hsub : insert x L ∪ farEven G x ⊆ E := by
    intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hy with hh | hh
    · rcases Finset.mem_insert.mp hh with e | hh
      · subst y; simp
      · rw [(Finset.mem_filter.mp hh).2]; decide
    · exact (Finset.mem_filter.mp hh).2.2
  have hE := Finset.card_le_card hsub
  have hxL : x ∉ L := by simp [L]
  rw [Finset.card_union_of_disjoint hdis,Finset.card_insert_of_notMem hxL] at hE
  change L.card + 1 + (farEven G x).card ≤ G.distEven x at hE
  have hU : ballTwo G x = insert x (N ∪ L) := by
    ext y
    simp only [ballTwo,N,L,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_union,mem_neighborFinset]
    have hz := (h.preconnected x y).dist_eq_zero_iff
    rw [← dist_eq_one_iff_adj, eq_comm (a := y) (b := x), ← hz]
    omega
  have hball := (congrArg Finset.card hU).le
  have hh := Finset.card_insert_le x (N ∪ L)
  have hll := Finset.card_union_le N L
  change (N ∪ L).card ≤ G.degree x + L.card at hll
  omega

theorem ball_budget (h : G.Connected) (s : ℕ) (hσ : ∀ x, G.distEven x ≤ 1+s) (x : V) :
    (ballTwo G x).card + (farEven G x).card ≤ 1 + G.degree x + s := by
  have := ball_budget_even h x
  have := hσ x
  omega

/-- The exceptional vertex only costs degree slack at centers adjacent to it.
A pointwise slack inequality therefore implies Asratian's local Ore bound. -/
theorem local_ore_of_slack (h : G.Connected) (s : ℕ) (hσ : ∀ x, G.distEven x ≤ 1+s)
    (z : V) (good : ∀ x, x ≠ z → s ≤ G.degree x)
    (slack : ∀ w, G.degree w + (if G.Adj w z then s-G.degree z else 0) ≤
      s+(farEven G w).card) :
    ∀ u w v, u ≠ v → G.Adj u w → G.Adj w v → ¬ G.Adj u v →
      (ballTwo G w).card ≤ 1 + G.degree u + G.degree v := by
  intro u w v hne huw hwv _
  have hb := ball_budget h s hσ w
  have hs := slack w
  by_cases hu : u=z
  · subst u
    have hg := good v hne.symm
    rw [if_pos huw.symm] at hs
    omega
  · by_cases hv : v=z
    · subst v
      have hg := good u hu
      rw [if_pos hwv] at hs
      omega
    · have hu' := good u hu
      have hv' := good v hv
      by_cases hw : G.Adj w z <;> simp [hw] at hs <;> omega

theorem local_ore_of_sharp_slack (h : G.Connected) (s : ℕ)
    (z : V) (good : ∀ x, x ≠ z → s ≤ G.degree x)
    (slack : ∀ w, G.degree w + G.distEven w + (if G.Adj w z then s-G.degree z else 0) ≤
      2*s+1+(farEven G w).card) :
    ∀ u w v, u ≠ v → G.Adj u w → G.Adj w v → ¬ G.Adj u v →
      (ballTwo G w).card ≤ 1 + G.degree u + G.degree v := by
  intro u w v hne huw hwv _
  have hb := ball_budget_even h w
  have hs := slack w
  by_cases hu : u=z
  · subst u
    have hg := good v hne.symm
    rw [if_pos huw.symm] at hs
    omega
  · by_cases hv : v=z
    · subst v
      have hg := good u hu
      rw [if_pos hwv] at hs
      omega
    · have hu' := good u hu
      have hv' := good v hv
      by_cases hw : G.Adj w z <;> simp [hw] at hs <;> omega

#print axioms ball_budget
#print axioms local_ore_of_slack
#print axioms local_ore_of_sharp_slack
end Graph189LocalOre
