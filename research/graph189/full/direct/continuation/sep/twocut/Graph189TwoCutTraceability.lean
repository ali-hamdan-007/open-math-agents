import Graph189TwoCutResidual
import Graph189TwoCutJoin

open Finset SimpleGraph Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TwoCutTraceability

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The graph-facing hypotheses common to the three separator routing cases.
The least-side property applies to later recuts, including disconnected sides. -/
structure MinimumCut (A B : Finset V) (p q : V) : Prop where
  different : p ≠ q
  sides : CutSides G A B {p,q}
  leftConnected : (G.induce (A : Set V)).Connected
  rightConnected : (G.induce (B : Set V)).Connected
  leftSize : 2 ≤ A.card
  rightSize : 2 ≤ B.card
  ordered : A.card ≤ B.card
  least : ∀ C D T, CutSides G C D T → T.card=2 → A.card≤C.card

/-- Two rooted original-edge side paths with a shared separator contact and
at most half the second degree in total side omissions. -/
def MatchingPaths (A B : Finset V) (p q : V) : Prop :=
  ∃ r ∈ ({p,q} : Finset V),
    ∃ a a' : (A : Set V), ∃ b b' : (B : Set V),
      ∃ P : (G.induce (A : Set V)).Walk a a',
        ∃ Q : (G.induce (B : Set V)).Walk b b',
          P.IsPath ∧ Q.IsPath ∧ G.Adj a.val r ∧ G.Adj r b.val ∧
          A.card+B.card≤P.support.length+Q.support.length+(G.secondSmallestDegree+1)/2

/-- Integrate the minimum-cut selector, the missing-private exclusion, and
the original-edge join. The three working branches are explicit parameters. -/
theorem near_of_routes (hc : G.Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (large : 9≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (connectivity : G.vertexConnectivity=2)
    (notTrace : ¬∃ a b, ∃ P : G.Walk a b, P.IsHamiltonian)
    (balanced : ∀ {A B p q}, MinimumCut (G:=G) A B p q →
      B.card<2*G.secondSmallestDegree → MatchingPaths (G:=G) A B p q)
    (commonFree : ∀ {A B p q}, MinimumCut (G:=G) A B p q →
      2*G.secondSmallestDegree≤B.card →
      (¬∃ x∈A, G.Adj x p ∧ G.Adj x q) → MatchingPaths (G:=G) A B p q)
    (shallow : ∀ {A B p q}, MinimumCut (G:=G) A B p q →
      2*G.secondSmallestDegree≤B.card →
      (∃ x∈A, G.Adj x p ∧ G.Adj x q) →
      (∀ x∈A, G.secondSmallestDegree≤G.degree x → G.Adj x p ∨ G.Adj x q) →
      (∃ x∈A, G.Adj x p ∧ ¬G.Adj x q) →
      (∃ x∈A, G.Adj x q ∧ ¬G.Adj x p) → MatchingPaths (G:=G) A B p q) :
    ∃ a b, ∃ P : G.Walk a b, P.IsPath ∧
      Fintype.card V≤P.support.length+(G.secondSmallestDegree+1)/2+1 := by
  obtain ⟨A,B,p,q,diff,sides,connA,connB,sa,sb,ordered,least,route⟩ :=
    Graph189TwoCutResidual.routing_cases hc cap large minimum connectivity notTrace
  have cut : MinimumCut (G:=G) A B p q := ⟨diff,sides,connA,connB,sa,sb,ordered,least⟩
  have paths : MatchingPaths (G:=G) A B p q := by
    rcases route with small|⟨big,free|⟨common,all,privP,privQ⟩⟩
    · exact balanced cut small
    · exact commonFree cut big free
    · exact shallow cut big common all privP privQ
  obtain ⟨r,hr,a,a',b,b',P,Q,hP,hQ,ar,rb,size⟩ := paths
  have two : ({p,q} : Finset V).card=2 := by simp [diff]
  exact Graph189TwoCutJoin.omission sides two hr P hP Q hQ ar rb size


/-- The handoff between the routing layer and the original-graph gap theorem.
The gap parameter is a separate proof obligation. -/
theorem traceable_of_gap
    (near : (¬∃ a b, ∃ P : G.Walk a b, P.IsHamiltonian) →
      ∃ a b, ∃ P : G.Walk a b, P.IsPath ∧
        Fintype.card V≤P.support.length+(G.secondSmallestDegree+1)/2+1)
    (gap : (¬∃ a b, ∃ P : G.Walk a b, P.IsHamiltonian) →
      ∀ {a b}, ∀ P : G.Walk a b, P.IsPath →
        P.support.length+(G.secondSmallestDegree+1)/2+2≤Fintype.card V) :
    ∃ a b, ∃ P : G.Walk a b, P.IsHamiltonian := by
  classical
  by_contra fail
  obtain ⟨a,b,P,hP,sz⟩ := near fail
  have bound := gap fail P hP
  omega

end Graph189TwoCutTraceability
#print axioms Graph189TwoCutTraceability.near_of_routes
#print axioms Graph189TwoCutTraceability.traceable_of_gap
