import Graph189RotationExterior
import Graph189TwoExteriorLinks
import Graph189ExteriorMatching
import Graph189ExteriorAttachment
import Graph189ThreeRegularMinimum
import Graph189ExteriorHalf

open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189OrdinaryRotationWindow
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] in
/-- A four- or five-vertex exterior window with three full high vertices
has prescribed spanning routes for a matching of three distinct marks. -/
theorem full_ports {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (W D : Finset V) (lower : 4≤W.card) (upper : W.card≤5) (many : 3≤D.card) (sub : D⊆W)
    (outside : ∀ v∈W, v∉p.support)
    (clique : ∀ a∈D, ∀ b∈W, a≠b → G.Adj a b)
    (bound : ∀ a∈D, ∀ b, G.Adj a b → b∉W → b∈p.support)
    (high : ∀ a∈D, W.card+2≤G.degree a) : 5*W.card+3≤Fintype.card V := by
  classical
  let H := G.induce (W : Set V)
  have degree (a : W) : 3≤H.degree a := by
    change 3≤(G.induce (W : Set V)).degree a
    rw [degree_induce_filter]
    by_cases inside : a.val∈D
    · have inc : W.erase a.val⊆(G.neighborFinset a.val).filter (fun v => v∈(W : Set V)) := by
        intro v hv
        obtain ⟨ne,mem⟩ := mem_erase.mp hv
        exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr (clique _ inside _ mem ne.symm),mem⟩
      have h := card_le_card inc
      rw [card_erase_of_mem a.property] at h
      omega
    · have inc : D⊆(G.neighborFinset a.val).filter (fun v => v∈(W : Set V)) := by
        intro v hv
        exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (clique v hv _ a.property (fun e => inside (e ▸ hv))).symm,sub hv⟩
      exact many.trans (card_le_card inc)
  have hc (a b : W) (ne : a≠b) : ∃ q : H.Walk a b, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed a b ne)
    intro u v _ _
    have h1 := degree u
    have h2 := degree v
    change Fintype.card W+1≤H.degree u+H.degree v
    rw [Fintype.card_coe]
    omega
  have rows (a : V) (ha : a∈D) : 3≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] a)).card := by
    let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] a)
    let P := R.image (fun i => p.support[i.val])
    have subset : insert a (G.neighborFinset a)⊆W∪P := by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem_union_left _ (sub ha)
      have adj := (G.mem_neighborFinset _ _).mp h
      by_cases vw : v∈W
      · exact mem_union_left _ vw
      obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp (bound a ha v adj vw)
      exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,mem_filter.mpr
        ⟨mem_univ _,by simpa only [e] using adj.symm⟩,e⟩)
    have h := (card_le_card subset).trans (card_union_le W P)
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
    have pc : P.card≤R.card := card_image_le
    have d := high a ha
    change 3≤R.card
    omega
  obtain ⟨M,sz,f,adj⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p D 3 many rows
  let inc : D ↪ W := ⟨fun v => ⟨v.val,sub v.property⟩,fun _ _ h => Subtype.ext (congrArg (fun t : W => (t : V)) h)⟩
  have h := exterior_hamilton_connected_matching p hp mx W (by omega) outside hc M
    (card_pos.mp (by omega)) (f.trans inc) adj
  rw [sz] at h
  exact h

/-- In an ordinary longest-path exterior, a high omission gives a rotation
window after the two-link order bound excludes longer cycles. -/
theorem of_cycle_cap {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    {k d L : ℕ} (original : G.secondSmallestDegree=k)
    (positive : 0<d) (rounding : 2*d≤k+1) (two : 2≤L)
    (bounded : ∀ {r}, ∀ C : G.Walk r r, C.IsCycle → (∀ v∈C.support,v∉p.support) → C.length≤L)
    (minimum : ∀ v, 3≤G.degree v) (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤k)
    {highVertex : V} (omitted : highVertex∉p.support) (large : k≤G.degree highVertex) :
    let E := p.support.toFinsetᶜ
    let J := G.induce (E : Set V)
    (∀ a : E, k≤G.degree a.val → d≤J.degree a) ∧
    ∃ B R : Finset E, d≤R.card ∧ R⊆B ∧ B.card≤L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  let emb := Embedding.induce (G:=G) (E : Set V)
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique (a b : V) (aLow : G.degree a<k) (bLow : G.degree b<k) : a=b := by
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
    omega
  have degree (a : E) (hi : k≤G.degree a.val) : d≤J.degree a := by
    have lower := (high_exterior_half p hp mx (off a) (quota _) hi minimum unique).2
    have eq : J.degree a=(G.neighborFinset a.val \ p.support.toFinset).card := by
      rw [degree_induce_filter]
      congr 1
      ext v
      simp [E]
    omega
  have short (a : E) (c : J.Walk a a) (hc : c.IsCycle) : c.length≤L := by
    have bound := bounded (c.map emb.toHom) (hc.map emb.injective) (fun v hv => by
      rw [Walk.support_map] at hv
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
      exact off w)
    simpa only [Walk.length_map] using bound
  let h : E := ⟨highVertex,mem_compl.mpr fun mem => omitted (List.mem_toFinset.mp mem)⟩
  obtain ⟨a,b,q,hq,maxQ⟩ := Graph189ThreeRegularMinimum.longest_path (G:=J) h
  have positive : 0<q.length := by
    have dh := degree h large
    obtain ⟨w,e⟩ := card_pos.mp (show 0<(J.neighborFinset h).card by
      rw [J.card_neighborFinset_eq_degree]
      omega)
    have edge := (J.mem_neighborFinset _ _).mp e
    have length := maxQ edge.toWalk edge.isPath_toWalk
    rw [edge.length_toWalk] at length
    omega
  have ab : a≠b := by
    intro eq
    subst b
    have zero := (Walk.isPath_iff_nil.mp hq).length_eq_zero
    omega
  have endpoints := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a.val b.val
    (fun e => ab (Subtype.ext e))
  have win : ∃ B R : Finset E, d≤R.card ∧ R⊆B ∧ B.card≤L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
    rcases endpoints with ha|hb
    · exact Graph189RotationExterior.degree_window_at q hq maxQ two (degree a (by omega)) short
    · apply Graph189RotationExterior.degree_window_at q.reverse hq.reverse _ two (degree b (by omega)) short
      intro u v r hr
      simpa using maxQ r hr
  exact ⟨degree,win⟩

/-- In an ordinary longest-path exterior, a high omission gives a rotation
window after the two-link order bound excludes longer cycles. -/
theorem of_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) {k d L : ℕ} (original : G.secondSmallestDegree=k)
    (positive : 0<d) (rounding : 2*d≤k+1) (two : 2≤L)
    (oversized : ∀ q, L<q → Fintype.card V<3*q+(q+1)/2+3)
    (minimum : ∀ v, 3≤G.degree v) (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤k)
    {highVertex : V} (omitted : highVertex∉p.support) (large : k≤G.degree highVertex) :
    let E := p.support.toFinsetᶜ
    let J := G.induce (E : Set V)
    (∀ a : E, k≤G.degree a.val → d≤J.degree a) ∧
    ∃ B R : Finset E, d≤R.card ∧ R⊆B ∧ B.card≤L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
  apply of_cycle_cap p hp mx original positive rounding two _ minimum quota omitted large
  intro r c hc out
  have n := Graph189TwoExteriorLinks.order_of_cycle p hp mx conn c hc out
  by_contra! longer
  exact (not_lt_of_ge n) (oversized c.length longer)

end Graph189OrdinaryRotationWindow
#print axioms Graph189OrdinaryRotationWindow.full_ports
#print axioms Graph189OrdinaryRotationWindow.of_high
