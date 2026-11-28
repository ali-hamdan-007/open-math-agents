import Graph189LinkedRootDegrees
import Graph189UniversalLinked

open SimpleGraph Finset
namespace Graph189LinkedRoot

/-- A small high exterior root and its actual off-path neighbors supply the
linked set required in the complement of the longest path. -/
theorem small_root_linked {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {a b : V} (p : H.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : H.Walk u v, r.IsPath → r.length≤p.length)
    (x : V) (outside : x∉p.support) (high : V→Prop) (hx : high x)
    (atMostOne : ∀ i j, i≠j → high i ∨ high j) {k δ l : ℕ}
    (hd : ∀ v, high v → k≤H.degree v+1) (md : ∀ v, δ≤H.degree v+1)
    (cap : (univ.filter (fun z => H.dist x z=2)).card≤k)
    (three : 3≤l) (size : l≤(H.neighborFinset x \ p.support.toFinset).card)
    (highRoom : l-1+(H.neighborFinset x \ p.support.toFinset).card+2≤k)
    (lowRoom : 3+(H.neighborFinset x \ p.support.toFinset).card+2≤δ) :
    Graph189LinkedExterior.Linked (H.induce {z | z∉p.support.toFinset}) l := by
  classical
  let X := window H p.support.toFinset x
  let K := H.induce (X : Set V)
  let c : X := ⟨x,mem_insert_self _ _⟩
  have degs := window_degrees H p hp longest x outside high hx hd md cap three size highRoom lowRoom
  have hub (y : X) (ne : y≠c) : K.Adj y c := by
    exact (window_adj H p.support.toFinset y.property (fun eq => ne (Subtype.ext eq))).symm
  have many : l+1≤Fintype.card X := by
    rw [Fintype.card_coe,window_card]; omega
  have paired (i j : X) (ne : i≠j) : l-1≤K.degree i ∨ l-1≤K.degree j := by
    rcases atMostOne i.val j.val (fun eq => ne (Subtype.ext eq)) with ih|jh
    · exact Or.inl ((degs i).2 ih)
    · exact Or.inr ((degs j).2 jh)
  have linked := Graph189UniversalLinked.linked (G:=K) c hub many three
    (fun v => (degs v).1) paired
  let T := {z : V | z∉p.support.toFinset}
  let embed : K →g H.induce T := {
    toFun := fun y => ⟨y.val,window_outside H p.support.toFinset
      (fun h => outside (List.mem_toFinset.mp h)) y.property⟩
    map_rel' := fun h => h }
  apply Graph189LinkedExterior.map embed _ linked
  intro i j ij
  exact Subtype.ext (congrArg (fun y : T => y.val) ij)

#print axioms small_root_linked
end Graph189LinkedRoot
