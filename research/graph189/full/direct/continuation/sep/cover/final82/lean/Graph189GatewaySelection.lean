import Graph189GatewayRank

open Finset
namespace Graph189GatewayRank
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One list of distinct vertices attains all the first g degree estimates simultaneously. -/
theorem choose_gateways (W Z : Finset V) (a g : ℕ) (hg : g≤Z.card)
    (row : ∀ w∈W, (Z.filter (fun z => ¬G.Adj w z)).card ≤ a) :
    ∃ L : List V, L.length=g ∧ L.Nodup ∧ ∀ (i : ℕ) (hi : i<L.length),
      L[i] ∈ Z ∧ W.card-W.card*a/(Z.card-i) ≤ (W.filter (fun w => G.Adj w L[i])).card := by
  classical
  induction g with
  | zero => exact ⟨[],rfl,by simp,by simp⟩
  | succ g ih =>
    obtain ⟨L,hl,hn,all⟩ := ih (by omega)
    let E := Z.filter (fun z => W.card-W.card*a/(Z.card-g) ≤ (W.filter (fun w => G.Adj w z)).card)
    have many : g+1≤E.card := best_gateway_card G W Z a g (by omega) row
    have nsub : ¬E ⊆ L.toFinset := by
      intro sub
      have upper := Finset.card_le_card sub
      have len : L.toFinset.card = L.length := List.toFinset_card_of_nodup hn
      omega
    obtain ⟨z,hz,unused⟩ := Finset.not_subset.mp nsub
    have hzL : z∉L := by simpa using unused
    refine ⟨L++[z],by simp [hl],by simp [List.nodup_append',List.disjoint_left,hn,hzL],?_⟩
    intro i hi
    by_cases old : i<L.length
    · simpa [List.getElem_append_left old] using all i old
    · have same : i=L.length := by simp at hi; omega
      subst i
      simpa [hl] using (Finset.mem_filter.mp hz)

#print axioms choose_gateways
end Graph189GatewayRank
