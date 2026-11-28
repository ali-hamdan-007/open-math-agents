import Graph189ExteriorDegree

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}

/-- Both ambient degrees of an omitted edge are controlled from either endpoint's
single distance-two cap and twice its own off-path degree. -/
theorem adjacent_ambient_degree_sum (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    G.degree a + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card := by
  have cross := cross_contact_degree p hp longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card
  omega

/-- Under the parent degree hypotheses with minimum degree three, every high
nonisolated omitted vertex has a high omitted neighbor and retains half its degree. -/
theorem nonisolated_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) (nonisolated : (G.neighborFinset a \ p.support.toFinset).Nonempty)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  let E := G.neighborFinset a \ p.support.toFinset
  have member (z : V) (hz : z∈E) : z∉p.support ∧ G.Adj a z :=
    ⟨fun h => (Finset.mem_sdiff.mp hz).2 (List.mem_toFinset.mpr h),
      (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hz).1⟩
  obtain ⟨w,hw⟩ := nonisolated
  obtain ⟨hwo,aw⟩ := member w hw
  have sum := adjacent_ambient_degree_sum p hp longest ha hwo aw quota
  have card : 1 < E.card := by
    change G.degree a + G.degree w ≤ k + 2*E.card at sum
    have := minimum w
    omega
  obtain ⟨s,hs,t,ht,ne⟩ := Finset.one_lt_card.mp card
  have good : ∃ b∈E, k ≤ G.degree b := by
    by_cases highS : k ≤ G.degree s
    · exact ⟨s,hs,highS⟩
    · refine ⟨t,ht,?_⟩
      by_contra! lowT
      exact ne (uniqueLow s t (by omega) lowT)
  obtain ⟨b,hb,highB⟩ := good
  obtain ⟨off,adj⟩ := member b hb
  exact ⟨⟨b,off,adj,highB⟩,half_degree_outside_longest p hp longest ha off adj quota highB⟩

#print axioms adjacent_ambient_degree_sum
#print axioms nonisolated_exterior_half
end Graph189ExteriorGap
