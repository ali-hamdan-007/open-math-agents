import Graph189MinimumDeletionReplay

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189RootedSplice
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A purely numerical form of the small-degree layer ceiling used by the
protected exterior exchange. It leaves at least two exact-size eligible gaps. -/
theorem order_room_for_two_exchanges {n k d m u : ℕ} (sum : m+u=k+1)
    (below : d+1≤u) (balanced : u≤m)
    (upper : n≤1+d+k+d*(k+1-d)) :
    n+2≤(u+1)*(m+1)+u := by
  obtain ⟨a,ea⟩ := Nat.exists_eq_add_of_le below
  obtain ⟨b,eb⟩ := Nat.exists_eq_add_of_le (below.trans balanced)
  have ek : k=2*d+1+a+b := by omega
  have et : k+1-d=d+2+a+b := by omega
  rw [et,ek] at upper
  rw [ea,eb]
  nlinarith [Nat.zero_le (a*b)]

/-- The combined uniform-contact and two-gap exchange to be formalized.
Every path in the exchange family is a longest protected path of the same size. -/
def UniformGapExclusion (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (z : V) (m u k : ℕ), 2≤u → u≤m → m+u=k+1 →
    (∀ v, G.distEven v≤k+1) →
    Fintype.card V+2≤(u+1)*(m+1)+u →
    (∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ z∈p.support ∧
      (univ \ p.support.toFinset).card=m ∧
      ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → z∈q.support → q.length≤p.length) →
    (∀ {a b}, ∀ q : G.Walk a b, q.IsPath → z∈q.support →
      (∀ {x y}, ∀ t : G.Walk x y, t.IsPath → z∈t.support → t.length≤q.length) →
      (univ \ q.support.toFinset).card=m →
      let E := univ \ q.support.toFinset
      (∀ x y : E, x≠y → ∃ r : (G.induce (E : Set V)).Walk x y, r.IsHamiltonian) ∧
      ∀ x : E, u≤(contactPositions q x.val).card) → False

/-- Graph-facing reduction for the unrestricted minimum-deletion theorem.
Only the protected contact census and two-full-gap exchange remain. -/
theorem traceable_of_minimum_deletion_via_uniform_exchange (exchange : UniformGapExclusion G)
    (hc : G.Connected) (z : V) (least : G.degree z=G.minDegree)
    (three : 3≤G.degree z) (k5 : 5≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b) (hr : r.IsHamiltonian) :
    ∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  by_contra fail
  obtain ⟨x,y,p,hp,on,longest⟩ := exists_longest_containing G z
  let k := G.secondSmallestDegree
  let d := G.degree z
  let m := (univ \ p.support.toFinset).card
  let u := k+1-m
  obtain ⟨half,small,_⟩ := near_spanning_rooted_exterior hc z least three k5 fail cap r hr p hp on longest
  obtain ⟨_,balanced,_⟩ := rooted_matching_cone_order hc z least three k5 fail cap r hr p hp on longest
  have strict := strict_matching_allowance hc z least three k5 fail cap r hr p hp on longest
  change 2*d≤k at half
  change m≤k+1-d at small
  change u≤m at balanced
  change d<u at strict
  have sum : m+u=k+1 := by dsimp [u]; omega
  have upper := Graph189LayerCutoff.order_of_small_degree G hc z k cap (by omega)
  change Fintype.card V≤1+d+k+d*(k+1-d) at upper
  have room := order_room_for_two_exchanges sum strict balanced upper
  refine exchange z m u k (by change 3≤d at three; omega) balanced sum cap room
    ⟨x,y,p,hp,on,rfl,longest⟩ ?_
  intro a b q hq member maximal same
  obtain ⟨_,_,routes⟩ := near_spanning_rooted_exterior hc z least three k5 fail cap r hr q hq member maximal
  refine ⟨routes,?_⟩
  intro v
  have high := exterior_contact_minimum q hq member least v
  change G.secondSmallestDegree+1-(univ \ q.support.toFinset).card≤_ at high
  rw [same] at high
  exact high

#print axioms order_room_for_two_exchanges
#print axioms traceable_of_minimum_deletion_via_uniform_exchange
end Graph189RootedSplice
