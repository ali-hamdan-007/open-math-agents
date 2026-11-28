import Graph189OrdinaryNearOriginal
import Graph189OrdinaryOmission

open SimpleGraph Finset
namespace Graph189TwelvePathOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At degree twelve the order and the number missed by a joined pair of routes
cannot simultaneously fit the small-exterior lower bound. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (two : 2≤G.vertexConnectivity) (degree : G.secondSmallestDegree=12)
    {a b : V} (q : G.Walk a b) (hq : q.IsPath) (loss : ℕ)
    (near : Fintype.card V≤q.support.length+loss)
    (small : loss≤10) (joint : Fintype.card V+loss≤53) :
    ∃x y, ∃p : G.Walk x y,p.IsHamiltonian := by
  classical
  obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
  have mind := two.trans (Graph189CutSides.connectivity_le_degree (G:=G) z)
  by_cases low : G.degree z=2
  · exact Graph189DegreeTwoOriginal.traceable hc cap two z low (by omega)
  have min : 3≤G.minDegree := by omega
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  obtain ⟨x,y,p,hp,longest⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let m := (p.support.toFinsetᶜ : Finset V).card
  have count := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at count
  change p.support.length+m=Fintype.card V at count
  have comparison := longest q hq
  have pq := p.length_support
  have qq := q.length_support
  have bound : m≤loss := by omega
  by_cases short : m≤7
  · apply Graph189OrdinaryPathGap.traceable_of_near_unrestricted hc upper (by omega) min p hp
    unfold Graph189OrdinaryPathGap.Near
    omega
  obtain ⟨_,product⟩ := Graph189OrdinaryOmission.small_exterior_order_extended p hp longest
    (fun v => by simpa only [Nat.add_comm] using upper v)
    (fun v => min.trans (G.minDegree_le_degree v)) (m:=m) rfl (by omega) (by omega)
  rw [degree] at product
  have choices : m=8 ∨ m=9 ∨ m=10 := by omega
  rcases choices with h|h|h <;> rw [h] at product <;> omega

#print axioms traceable
end Graph189TwelvePathOrder
