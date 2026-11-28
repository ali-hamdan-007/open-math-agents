import Graph189PrescribedBatch

open SimpleGraph Finset
namespace Graph189TerminalLeafClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

def fillInside (W : Finset V) : SimpleGraph V where
  Adj x y := x∈W ∧ y∈W ∧ x≠y
  symm := ⟨fun _ _ h => ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2 rfl⟩

def fillIncident (W : Finset V) : SimpleGraph V where
  Adj x y := (x∈W ∨ y∈W) ∧ x≠y
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private theorem degree_in_filled {H : SimpleGraph V} [DecidableRel H.Adj] (W : Finset V)
    {v : V} (hv : v∈W) (all : fillInside W ≤ H) : W.card ≤ H.degree v + 1 := by
  classical
  have incl : W.erase v ⊆ H.neighborFinset v := by
    intro x hx
    obtain ⟨hneq, hxW⟩ := Finset.mem_erase.mp hx
    simp only [SimpleGraph.mem_neighborFinset]
    exact all ⟨hv,hxW,hneq.symm⟩
  have card := Finset.card_le_card incl
  rw [Finset.card_erase_of_mem hv, SimpleGraph.card_neighborFinset_eq_degree] at card
  omega

omit [DecidableEq V] in
private theorem degree_outside_filled {H : SimpleGraph V} [DecidableRel H.Adj] (W : Finset V)
    {v : V} (hv : v∉W) (all : fillIncident W ≤ H) : W.card ≤ H.degree v := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [SimpleGraph.mem_neighborFinset]
  exact all ⟨Or.inr hx,fun h => hv (h.symm ▸ hx)⟩

/-- One potentially low vertex is allowed. Its absolute degree three suffices for
every pair of distinct prescribed endpoints. -/
theorem exterior_one_low {G : SimpleGraph V} [DecidableRel G.Adj] (low u v : V) (huv : u≠v)
    (minimum : ∀ z, 3≤G.degree z)
    (high : ∀ z, z≠low → Fintype.card V+1 ≤ 2*G.degree z) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let W := Finset.univ.erase low
  let H := G⊔fillInside W
  have inc : G≤H := le_sup_left
  apply prescribed_of_supergraph inc
  · intro a b h hn
    rcases h with h | h
    · exact (hn h).elim
    · have ha := high a (Finset.mem_erase.mp h.1).1
      have hb := high b (Finset.mem_erase.mp h.2.1).1
      omega
  apply prescribed_of_supergraph (le_top : H≤⊤) _ (complete_prescribed u v huv)
  intro a b hab hnot
  have hne : a≠b := (top_adj _ _).mp hab
  have upper (z : V) (hz : z≠low) : Fintype.card V ≤ H.degree z+2 := by
    have hm : z∈W := by simp [W,hz]
    have hr := degree_in_filled W hm (show fillInside W≤H from le_sup_right)
    have wc : W.card = Fintype.card V-1 := by simp [W,Finset.card_erase_of_mem]
    omega
  have min (z : V) : 3≤H.degree z := (minimum z).trans (degree_le_of_le inc)
  by_cases ha : a=low
  · have hb : b≠low := fun h => hne (ha.trans h.symm)
    have := upper b hb
    have := min a
    omega
  · have := upper a ha
    have := min b
    omega

/-- The exterior core with a dense distinguished set and adequately attached
remaining vertices has a Hamilton path between any two prescribed endpoints. -/
theorem exterior_dense_set {G : SimpleGraph V} [DecidableRel G.Adj] (W : Finset V) (a : ℕ)
    (size : 2*a+3 ≤ Fintype.card V) (majority : Fintype.card V+1 ≤ 2*W.card)
    (inside : ∀ w∈W, Fintype.card V ≤ G.degree w + a + 1)
    (outside : ∀ z∉W, a+2 ≤ G.degree z) (u v : V) (huv : u≠v) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let H := G⊔fillInside W
  let K := G⊔fillIncident W
  have gH : G≤H := le_sup_left
  have gK : G≤K := le_sup_left
  have hK : H≤K := sup_le gK (fun x y h => Or.inr ⟨Or.inl h.1,h.2.2⟩)
  apply prescribed_of_supergraph gH
  · intro x y h hn
    rcases h with h | h
    · exact (hn h).elim
    · have := inside x h.1
      have := inside y h.2.1
      omega
  apply prescribed_of_supergraph hK
  · intro x y h hn
    rcases h with h | h
    · exact (hn (gH h)).elim
    have hx := degree_le_of_le (v := x) gH
    have hy := degree_le_of_le (v := y) gH
    rcases h.1 with xin | yin
    · have yn : y∉W := fun hi => hn (Or.inr ⟨xin,hi,h.2⟩)
      have := inside x xin
      have := outside y yn
      omega
    · have xn : x∉W := fun hi => hn (Or.inr ⟨hi,yin,h.2⟩)
      have := inside y yin
      have := outside x xn
      omega
  apply prescribed_of_supergraph (le_top : K≤⊤) _ (complete_prescribed u v huv)
  intro x y h hn
  have hne := (top_adj _ _).mp h
  have both : x∉W ∧ y∉W := ⟨fun hx => hn (Or.inr ⟨Or.inl hx,hne⟩),
    fun hy => hn (Or.inr ⟨Or.inr hy,hne⟩)⟩
  have dx := degree_outside_filled W both.1 (show fillIncident W≤K from le_sup_right)
  have dy := degree_outside_filled W both.2 (show fillIncident W≤K from le_sup_right)
  omega

#print axioms exterior_one_low
#print axioms exterior_dense_set
end Graph189TerminalLeafClosure
