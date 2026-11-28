import Graph189ScalarConclusion
import Graph189SyntheticBand
import Graph189ActualScalarWidth
import Graph189EffectiveDeficit
import Graph189GraphPopulation

namespace Graph189TerminalGraph
open SimpleGraph Finset Graph189SmallWindowCover Graph189FiniteDomain
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Conditional graph-facing domain reduction. The four remaining inputs are
the structural order lower bound, the two high-order separator bounds, and the
order lift for the effective minimum-cut deficit of this very graph. -/
theorem terminal_band (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (hn : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian)
    (hsN : 5≤G.vertexConnectivity) (hk26N : 26≤G.secondSmallestDegree)
    (hkN : 3*G.vertexConnectivity<G.secondSmallestDegree) :
    let s : ℤ := G.vertexConnectivity
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    let d : ℤ := Graph189EffectiveDeficit.effectiveDeficit G
    (s+1)*(k-s+2)-1≤n →
    (6*(s-1)<k → 2*n<(2*s+3)*k+4*s+4) →
    (6*(s-1)<k → (s-2)*(n-2*s-3)<((s+1)*(s-2)+3)*k) →
    (3*s<2*(k-d-1) → 2*s≤k-2*d-2 → 4*n<k*(k-1) →
      (s+2)*(k-d-s+1)-1≤n) →
    s≤8 ∧ valid (band s k)=true ∧ (band s k).low≤n := by
  classical
  intro s k n d hbase hhalf hthree hlift
  have hs5 : (5:ℤ)≤s := by dsimp only [s]; exact_mod_cast hsN
  have hk26 : (26:ℤ)≤k := by dsimp only [k]; exact_mod_cast hk26N
  have hk : 3*s<k := by dsimp only [s,k]; exact_mod_cast hkN
  have m₁ := mul_nonneg (show 0≤s-3 by omega) (sub_nonneg.mpr hk.le)
  have m₂ := mul_nonneg (show 0≤s by omega) (sub_nonneg.mpr hs5)
  have large : 4*k+2≤n := by nlinarith only [hbase,m₁,m₂,hs5]
  have har : 4*G.secondSmallestDegree+2≤Fintype.card V := by
    dsimp only [k,n] at large
    exact_mod_cast large
  have room : G.vertexConnectivity<Fintype.card V-1 := by omega
  have cap (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hcap
  obtain ⟨he,hem,ho,hwl,hwh⟩ := Graph189ActualScalarWidth.bounds hc hcap hn har
  have hside := Graph189GraphPopulation.actual_order_upper hc cap hsN hkN room
  have hlow := Graph189EffectiveDeficit.low_witnesses hc cap hsN hkN
  have hd : 0≤d := by dsimp [d]; positivity
  exact Graph189ScalarConclusion.terminal_band hs5 hk26 hk he hem ho hwl hwh hbase hside
    hhalf hthree hd hlow hlift

/-- An original counterexample satisfying just the two structural lower
bounds supplies a valid band at its actual connectivity and degree. A failed
cut upper bound supplies a synthetic band; the complementary case supplies
the finite-domain band. This theorem can feed a uniform cut contradiction. -/
theorem exists_valid_band (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (hn : ¬∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian)
    (hsN : 5≤G.vertexConnectivity) (hk26N : 26≤G.secondSmallestDegree)
    (hkN : 3*G.vertexConnectivity<G.secondSmallestDegree) :
    let s : ℤ := G.vertexConnectivity
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    let d : ℤ := Graph189EffectiveDeficit.effectiveDeficit G
    (s+1)*(k-s+2)-1≤n →
    (3*s<2*(k-d-1) → 2*s≤k-2*d-2 → 4*n<k*(k-1) →
      (s+2)*(k-d-s+1)-1≤n) →
    ∃ r : Band, r.s=s ∧ r.k=k ∧ r.low≤n ∧ valid r=true := by
  classical
  intro s k n d hbase hlift
  by_cases bad : 6*(s-1)<k ∧ ((2*s+3)*k+4*s+4≤2*n ∨
      ((s+1)*(s-2)+3)*k≤(s-2)*(n-2*s-3))
  · exact ⟨Graph189SyntheticBand.row s k n,rfl,rfl,le_rfl,
      Graph189SyntheticBand.high_order (by dsimp only [s]; exact_mod_cast hsN) bad.1 bad.2⟩
  · have half (small : 6*(s-1)<k) : 2*n<(2*s+3)*k+4*s+4 := by
      apply lt_of_not_ge
      exact fun h => bad ⟨small,Or.inl h⟩
    have three (small : 6*(s-1)<k) : (s-2)*(n-2*s-3)<((s+1)*(s-2)+3)*k := by
      apply lt_of_not_ge
      exact fun h => bad ⟨small,Or.inr h⟩
    obtain ⟨_,v,l⟩ := terminal_band hc hcap hn hsN hk26N hkN hbase half three hlift
    exact ⟨band s k,rfl,rfl,l,v⟩

end Graph189TerminalGraph
#print axioms Graph189TerminalGraph.terminal_band

#print axioms Graph189TerminalGraph.exists_valid_band
