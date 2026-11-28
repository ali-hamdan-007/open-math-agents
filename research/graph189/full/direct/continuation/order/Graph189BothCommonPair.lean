import Graph189DeepCommonPair
import Graph189ShallowCommonOrder

open SimpleGraph Finset Graph189DeepCommonPair
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189BothCommonPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If one side is shallow among high vertices, common ports on both sides
already force an original Hamilton path for every second degree at least twelve. -/
theorem shallow (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (sz : S.card=2) (large : 12≤G.secondSmallestDegree) (cA : ∃u∈A,∀i∈S,G.Adj u i)
    (cB : ∃v∈B,∀i∈S,G.Adj v i) (fail : ¬∃x,Deep G A S x) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have two : 2≤G.vertexConnectivity := by omega
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases high : ∃x∈A,G.secondSmallestDegree≤G.degree x
  · have cover (x : V) (xa : x∈A) (xh : G.secondSmallestDegree≤G.degree x) : ∃i∈S,G.Adj i x := by
      by_contra! nonport
      exact fail ⟨x,xa,xh,nonport⟩
    have order := Graph189ShallowCommonOrder.order hc sides sc sz point cover high cA cB
    exact Graph189OnePortCover.below_four hc cap two (by omega) (by omega)
  push_neg at high
  obtain ⟨x,xa⟩ := sides.left_nonempty
  have ns : G.neighborFinset x⊆S := by
    intro y hy
    have e := (G.mem_neighborFinset _ _).mp hy
    rcases sides.cover y with ya|yb|ys
    · rcases degree_pair (G:=G) x y e.ne with h|h
      · exact ((not_lt_of_ge h) (high x xa)).elim
      · exact ((not_lt_of_ge h) (high y ya)).elim
    · exact (sides.no_cross x xa y yb e).elim
    · exact ys
  have bound := card_le_card ns
  rw [G.card_neighborFinset_eq_degree] at bound
  have low := Graph189CutSides.connectivity_le_degree (G:=G) x
  exact Graph189DegreeTwoOriginal.traceable hc cap two x (by omega) (by omega)

/-- Every original separating pair with a common port on both sides
forces a Hamiltonian path for k≥15. The separator may be nonadjacent,
the sides may be shallow or deep, and the low vertex can lie anywhere. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    {p q : V} (sep : S={p,q}) (ne : p≠q) (large : 15≤G.secondSmallestDegree)
    (cA : ∃u∈A,∀i∈S,G.Adj u i) (cB : ∃v∈B,∀i∈S,G.Adj v i) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have sz : S.card=2 := by simp [sep,ne]
  by_cases dA : ∃x,Deep G A S x
  · by_cases dB : ∃x,Deep G B S x
    · exact Graph189DeepCommonPair.traceable hc cap sides sc sep ne large dA dB cA cB
    · exact shallow hc cap sides.swap sc sz (by omega) cB cA dB
  · exact shallow hc cap sides sc sz (by omega) cA cB dA

#print axioms shallow
#print axioms traceable
end Graph189BothCommonPair
