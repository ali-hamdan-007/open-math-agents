import Graph189RotationExterior
import Graph189TwoExteriorLinks
import Graph189ExteriorMatching
import Graph189ExteriorAttachment
import Graph189ThreeRegularMinimum
import Graph189ExteriorHalf

open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189SevenRotation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] in
/-- A five-vertex exterior window in which three high vertices have full
internal degree and no other exterior neighbor forces at least 28 vertices. -/
private theorem window_order {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (W D : Finset V) (size : W.card=5) (many : 3≤D.card) (sub : D⊆W)
    (outside : ∀ v∈W, v∉p.support)
    (clique : ∀ a∈D, ∀ b∈W, a≠b → G.Adj a b)
    (bound : ∀ a∈D, ∀ b, G.Adj a b → b∉W → b∈p.support)
    (high : ∀ a∈D, 7≤G.degree a) : 28≤Fintype.card V := by
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
      rw [card_erase_of_mem a.property,size] at h
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
    rw [Fintype.card_coe,size]
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
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree,size] at h
    have pc : P.card≤R.card := card_image_le
    have d := high a ha
    change 3≤R.card
    omega
  obtain ⟨M,sz,f,adj⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p D 3 many rows
  let inc : D ↪ W := ⟨fun v => ⟨v.val,sub v.property⟩,fun _ _ h => Subtype.ext (congrArg (fun t : W => (t : V)) h)⟩
  have h := exterior_hamilton_connected_matching p hp mx W (by omega) outside hc M
    (card_pos.mp (by omega)) (f.trans inc) adj
  rw [sz,size] at h
  exact h

/-- Any high omission in an ordinary longest path is impossible in a
two-connected qualifying graph of order at most twenty-three and k=7. -/
theorem no_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) (order : Fintype.card V≤23)
    (original : G.secondSmallestDegree=7) (minimum : ∀ v, 3≤G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤7)
    {highVertex : V} (omitted : highVertex∉p.support) (large : 7≤G.degree highVertex) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  let emb := Embedding.induce (G:=G) (E : Set V)
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique (a b : V) (aLow : G.degree a<7) (bLow : G.degree b<7) : a=b := by
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
    omega
  have degree (a : E) (hi : 7≤G.degree a.val) : 4≤J.degree a := by
    have lower := (high_exterior_half p hp mx (off a) (quota _) hi minimum unique).2
    have eq : J.degree a=(G.neighborFinset a.val \ p.support.toFinset).card := by
      rw [degree_induce_filter]
      congr 1
      ext v
      simp [E]
    omega
  have short (a : E) (c : J.Walk a a) (hc : c.IsCycle) : c.length≤5 := by
    have ord := Graph189TwoExteriorLinks.order_of_cycle p hp mx conn (c.map emb.toHom) (hc.map emb.injective)
      (fun v hv => by
        rw [Walk.support_map] at hv
        obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
        exact off w)
    rw [Walk.length_map] at ord
    omega
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
  have win : ∃ B R : Finset E, 4≤R.card ∧ R⊆B ∧ B.card≤5 ∧ ∀ v∈R,J.neighborFinset v⊆B := by
    rcases endpoints with ha|hb
    · exact Graph189RotationExterior.degree_window_at q hq maxQ (by decide) (degree a (by omega)) short
    · apply Graph189RotationExterior.degree_window_at q.reverse hq.reverse _ (by decide) (degree b (by omega)) short
      intro u v r hr
      simpa using maxQ r hr
  obtain ⟨B,R,rank,sub,width,neighbor⟩ := win
  let D := R.filter (fun v => 7≤G.degree v.val)
  have few : (R \ D).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    apply Subtype.ext
    apply unique
    · by_contra! high
      exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,high⟩)
    · by_contra! high
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,high⟩)
  have split := card_sdiff_add_card_eq_card (show D⊆R from filter_subset _ _)
  have many : 3≤D.card := by omega
  have full (a : E) (ha : a∈D) : J.neighborFinset a=B.erase a ∧ B.card=5 := by
    have ar := (mem_filter.mp ha).1
    have degreeA := degree a (mem_filter.mp ha).2
    have inc : J.neighborFinset a⊆B.erase a := by
      intro v hv
      exact mem_erase.mpr ⟨((J.mem_neighborFinset _ _).mp hv).ne.symm,neighbor a ar hv⟩
    have size := card_le_card inc
    rw [J.card_neighborFinset_eq_degree,card_erase_of_mem (sub ar)] at size
    exact ⟨eq_of_subset_of_card_le inc (by
      rw [J.card_neighborFinset_eq_degree,card_erase_of_mem (sub ar)]
      omega),by omega⟩
  obtain ⟨d,hd⟩ := card_pos.mp (show 0<D.card by omega)
  let f : E ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have ord := window_order p hp mx (B.map f) (D.map f) (by rw [card_map,(full d hd).2])
    (by rwa [card_map]) (map_subset_map.mpr ((filter_subset _ _).trans sub))
    (fun v hv => by obtain ⟨v,_,rfl⟩ := mem_map.mp hv; exact off v)
    (by
      intro a ha b hb diff
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hb
      apply (J.mem_neighborFinset u v).mp
      rw [(full u hu).1]
      exact mem_erase.mpr ⟨fun eq => diff (congrArg f eq.symm),hv⟩)
    (by
      intro a ha v step no
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      by_contra offV
      let w : E := ⟨v,mem_compl.mpr fun mem => offV (List.mem_toFinset.mp mem)⟩
      have e : J.Adj u w := step
      exact no (mem_map.mpr ⟨w,neighbor u (mem_filter.mp hu).1 ((J.mem_neighborFinset _ _).mpr e),rfl⟩))
    (by
      intro a ha
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      exact (mem_filter.mp hu).2)
  omega

end Graph189SevenRotation
#print axioms Graph189SevenRotation.no_high
