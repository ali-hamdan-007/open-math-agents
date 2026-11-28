import Graph189ThreeSelectedPorts
import Graph189SimplicialEndpoint
import Graph189OddExteriorClique
import Graph189ProtectedHamiltonConnected

open SimpleGraph Finset Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}

/-- The extremal exterior on k−1 vertices is Hamilton-connected in the
degree-two order range. In odd degree the only competing endpoint obstruction
would yield three matched simplicial ports, contradicting that same order. -/
theorem extreme_two_routes (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length≤p.length)
    (low : G.degree p.support[t.val]<G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (large : 7 ≤ G.secondSmallestDegree) (order : Fintype.card V ≤ 3*G.secondSmallestDegree+1)
    (size : (p.support.toFinsetᶜ : Finset V).card+1=G.secondSmallestDegree) :
    let E := (p.support.toFinsetᶜ : Finset V)
    ∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian := by
  classical
  let P := p.support.toFinset
  let E := (Pᶜ : Finset V)
  let F := G.induce (E : Set V)
  let k := G.secondSmallestDegree
  let d := k/2
  change E.card+1=k at size
  change 7 ≤ k at large
  change Fintype.card V ≤ 3*k+1 at order
  change ∀ x y : E, x≠y → ∃ q : F.Walk x y, q.IsHamiltonian
  have half (a : E) : d ≤ F.degree a := protected_exterior_minimum p hp t mx low cap a
  have nE : Fintype.card E=E.card := Fintype.card_coe E
  by_cases enough : E.card+1 ≤ 2*d
  · intro x y ne
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (H:=⊤) le_top _ (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro a b _ _
    have h := half a
    have h' := half b
    change Fintype.card E+1 ≤ F.degree a+F.degree b
    omega
  have odd : k=2*d+1 := by dsimp [d] at *; omega
  have count : Fintype.card E=2*d := by omega
  have out (a : V) (h : a∈E) : a∉p.support := by simpa [E,P] using h
  have high (a : V) (h : a∈E) : k ≤ G.degree a :=
    (degree_pair (G:=G) a p.support[t.val] (fun e => out a h (e ▸ List.getElem_mem _))).resolve_right (not_le.mpr low)
  have internal (a : E) : F.degree a=(G.neighborFinset a.val \ P).card := by
    rw [show F.degree a = _ from degree_induce_filter (E : Set V) a]
    congr 1
    ext b
    simp [E]
  let W := E.filter (fun a => (G.neighborFinset a \ P).card=d)
  let incl : W ↪ E := ⟨fun a => ⟨a.val,(mem_filter.mp a.property).1⟩,
    fun a b h => Subtype.ext (congrArg (fun i : E => i.val) h)⟩
  let L : Finset E := univ.map incl
  by_cases many : 3 ≤ W.card
  · exfalso
    have rows (a : V) (h : a∈W) : 3 ≤ ((univ : Finset (Fin p.support.length)).filter
        (fun i => G.Adj p.support[i.val] a)).card := by
      let A := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] a)
      have sub : G.neighborFinset a ∩ P ⊆ A.image (fun i => p.support[i.val]) := by
        intro b hb
        obtain ⟨ab,mem⟩ := mem_inter.mp hb
        obtain ⟨j,hj,val⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp mem)
        exact mem_image.mpr ⟨⟨j,hj⟩,mem_filter.mpr ⟨mem_univ _,by simpa [val] using ((G.mem_neighborFinset _ _).mp ab).symm⟩,val⟩
      have enough := (card_le_card sub).trans card_image_le
      have degree := high a (mem_filter.mp h).1
      have eq := (mem_filter.mp h).2
      have parts := card_sdiff_add_card_inter (G.neighborFinset a) P
      rw [G.card_neighborFinset_eq_degree] at parts
      change 3 ≤ A.card
      omega
    have route (a b : W) (diff : a≠b) : ExteriorRoute p a.val b.val E.card := by
      have clique (c e : E) (ac : F.Adj (incl a) c) (ae : F.Adj (incl a) e) (ne : c≠e) : F.Adj c e := by
        have exactQ : (univ.filter (fun w => G.dist a.val w=2)).card ≤ 2*d+1 := by
          let T := univ.filter (fun w => G.dist a.val w=2)
          have short : a.val ∉ T := by simp [T]
          have sub : insert a.val T ⊆ univ.filter (fun w => Even (G.dist a.val w)) := by
            intro w hw
            rcases mem_insert.mp hw with rfl | h
            · simp
            · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
          have h := (card_le_card sub).trans (cap a.val)
          rw [card_insert_of_notMem short] at h
          change T.card+1 ≤ k+1 at h
          change T.card ≤ 2*d+1
          omega
        exact adjacent_of_odd_equality p hp t mx (out _ (incl a).property) (out _ c.property) (out _ e.property)
          ac ae (fun eq => ne (Subtype.ext eq)) (odd ▸ high _ (incl a).property) (odd ▸ high _ c.property)
          (mem_filter.mp a.property).2 exactQ
      obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.prescribed_of_simplicial (G:=F) (incl a) (incl b)
        (incl.injective.ne diff) (fun v => by
          change Fintype.card E ≤ 2*F.degree v
          rw [count]
          exact Nat.mul_le_mul_left 2 (half v)) clique
      exact route_of_induced_hamilton p E out hq
    have bound := order_of_three_selected p hp t mx E W out many rows route
    omega
  · have few : L.card≤2 := by simp [L]; omega
    have better (a : E) (notin : a∉L) : d < F.degree a := by
      have h := half a
      by_contra! no
      apply notin
      have eq := internal a
      let v : W := ⟨a.val,mem_filter.mpr ⟨a.property,by omega⟩⟩
      exact mem_map.mpr ⟨v,mem_univ _,Subtype.ext rfl⟩
    exact Graph189TerminalLeafClosure.prescribed_of_two_exceptions count (by omega) half L few better

#print axioms extreme_two_routes
end Graph189ExteriorGap
