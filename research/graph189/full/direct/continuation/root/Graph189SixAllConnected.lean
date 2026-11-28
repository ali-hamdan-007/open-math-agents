import Graph189SixThreeConnected
import Graph189FiveCycleAttached
import Graph189FiveCycleLarge

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189SixAllConnected
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At degree six every ordinary longest path in the two-connected,
minimum-degree-three case has no exterior cycle longer than four. -/
theorem exterior_four (hcG : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) (conn : 2≤G.vertexConnectivity) (minimum : ∀ v, 3≤G.degree v)
    {a b r : V} (p : G.Walk a b) (hp : p.IsPath) (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (off : ∀ v∈C.support,v∉p.support) : C.length≤4 := by
  classical
  have lim := Graph189SixCycleExtra.five_bound hcG cap degree conn p hp mx C hc off
  by_contra! more
  have five : C.length=5 := by omega
  have point (v : V) : G.distEven v≤7 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  let E := p.support.toFinsetᶜ
  have inc : C.support.toFinset⊆E := fun v hv => mem_compl.mpr fun h =>
    off v (List.mem_toFinset.mp hv) (List.mem_toFinset.mp h)
  have lower := card_le_card inc
  have wc := Graph189SixCycleExtra.cycle_card C hc
  by_cases large : 7≤E.card
  · exact Graph189FiveCycleLarge.excluded hcG cap degree conn minimum p hp mx C hc five off large
  by_cases six : E.card=6
  · exact Graph189FiveCycleAttached.excluded hcG cap degree conn minimum p hp mx C hc five off six
  exact Graph189FiveCycleSpanning.excluded hcG degree point minimum p hp mx C hc five off (by change E.card=5; omega)

/-- The original conclusion at all orders in the two-connected,
minimum-degree-three case of second-smallest degree six. -/
theorem traceable (hcG : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) (conn : 2≤G.vertexConnectivity) (minimum : ∀ v, 3≤G.degree v) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤7 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  obtain ⟨z,sz⟩ := Graph189QuadraticOrder.second_attained (G:=G)
  have quad := Graph189QuadraticOrder.rooted hcG z 6 point
  rw [sz,degree] at quad
  have order : Fintype.card V≤25 := by omega
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤6 := by
    let T := univ.filter (fun w => G.dist v w=2)
    have inc : insert v T⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have n := card_le_card inc
    rw [card_insert_of_notMem (by simp [T])] at n
    change T.card+1≤G.distEven v at n
    exact Nat.le_of_succ_le_succ (n.trans (point v))
  let E := p.support.toFinsetᶜ
  have low (v : V) (hv : v∈E) : G.degree v<6 := by
    by_contra! high
    exact Graph189SixWideRotation.no_high_of_cycle_cap p hp mx
      (fun C hc off => exterior_four hcG cap degree conn minimum p hp mx C hc off)
      order degree minimum quota (by simpa [E] using hv) high
  have few : E.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    have l := low u hu
    have r := low v hv
    omega
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  exact Graph189SixThreeConnected.traceable_of_four hcG cap degree minimum p hp (by omega)

#print axioms exterior_four
#print axioms traceable
end Graph189SixAllConnected
