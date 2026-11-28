import Graph189HighExteriorLinked
import Graph189SmallRootLinked

namespace Graph189DeletionLinked
open SimpleGraph Finset Graph189ExteriorGap

/-- A nontrivial exterior supplies either a large high-degree cycle or a
linked set centered at a single high vertex. The parameters allow a unique
low vertex to remain in the ambient graph after deletion. -/
theorem exterior {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length≤p.length)
    (edge : ∃ a ∉ p.support, ∃ b ∉ p.support, G.Adj a b)
    (high : V→Prop) (pair : ∀ i j, i≠j → high i ∨ high j)
    {k d l : ℕ} (hd : ∀ x, high x → k≤G.degree x+1) (minimum : ∀ x, d≤G.degree x+1)
    (cap : ∀ x, (univ.filter (fun y => G.dist x y=2)).card≤k)
    (three : 3≤l) (ratio : 3*l≤k+2) (low : 2*l+2≤d) (gap : k+6≤2*d) :
    Graph189LinkedExterior.Linked (G.induce {x | x∉p.support.toFinset}) l := by
  classical
  let q (x : V) := (G.neighborFinset x \ p.support.toFinset).card
  have sum (x y : V) (xo : x∉p.support) (yo : y∉p.support) (xy : G.Adj x y) :
      G.degree x+G.degree y ≤ k+2*q x := by
    have c := cross_contact_degree p hp longest xo yo xy (cap x)
    have s := card_sdiff_add_card_inter (G.neighborFinset x) p.support.toFinset
    rw [G.card_neighborFinset_eq_degree] at s
    dsimp [q]
    omega
  have minTwo (x y : V) (xo : x∉p.support) (yo : y∉p.support) (xy : G.Adj x y) : 2≤q x := by
    have h := sum x y xo yo xy
    have xdeg := minimum x
    have ydeg := minimum y
    omega
  by_cases small : ∃ x ∉ p.support, high x ∧ (∃ y ∉ p.support, G.Adj x y) ∧ q x < 2*l-2
  · obtain ⟨x,xo,hx,⟨y,yo,xy⟩,short⟩ := small
    obtain ⟨z,zo,hz,xz⟩ := Graph189HighExteriorLinked.high_neighbor p high pair x (minTwo x y xo yo xy)
    have cnt := sum x z xo zo xz
    have xd := hd x hx
    have zd := hd z hz
    exact Graph189LinkedRoot.small_root_linked p hp longest x xo high hx pair hd minimum (cap x) three
      (show l≤q x by omega) (show l-1+q x+2≤k by omega) (show 3+q x+2≤d by omega)
  · have seeded : ∃ a ∉ p.support, ∃ b ∉ p.support, high a ∧ high b ∧ G.Adj a b := by
      obtain ⟨a,ao,b,bo,ab⟩ := edge
      rcases pair a b ab.ne with ha|hb
      · obtain ⟨z,zo,hz,az⟩ := Graph189HighExteriorLinked.high_neighbor p high pair a (minTwo a b ao bo ab)
        exact ⟨a,ao,z,zo,ha,hz,az⟩
      · obtain ⟨z,zo,hz,bz⟩ := Graph189HighExteriorLinked.high_neighbor p high pair b (minTwo b a bo ao ab.symm)
        exact ⟨b,bo,z,zo,hb,hz,bz⟩
    apply Graph189HighExteriorLinked.high_cycle p high pair seeded three
    intro x xo hx y yo xy
    by_contra! bad
    exact small ⟨x,xo,hx,⟨y,yo,xy⟩,bad⟩

#print axioms exterior
end Graph189DeletionLinked
