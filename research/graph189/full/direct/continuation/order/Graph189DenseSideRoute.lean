import Graph189PortRotation
import Graph189SidePathDegree

open SimpleGraph Finset
namespace Graph189DenseSideRoute
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path inside W starting at a neighbor of the prescribed anchor u. -/
def Route (G : SimpleGraph V) (W : Finset V) (u : V) (loss : ℕ) : Prop :=
  ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ G.Adj u a ∧ (∀ v∈p.support, v∈W) ∧
    W.card≤p.support.length+loss

/-- Only neighbors in the boundary can be lost upon restriction to W. -/
theorem retained (W T : Finset V) (closed : ∀ x∈W, ∀ y, G.Adj x y → y∉W → y∈T)
    (x : W) : G.degree x.val≤(G.induce (W:Set V)).degree x+T.card := by
  classical
  let N := (G.neighborFinset x.val).filter (fun y => y∈(W:Set V))
  have inc : G.neighborFinset x.val⊆N∪T := by
    intro y hy
    by_cases h : y∈W
    · exact mem_union_left _ (mem_filter.mpr ⟨hy,h⟩)
    · exact mem_union_right _ (closed x.val x.property y ((G.mem_neighborFinset _ _).mp hy) h)
  have cnt := (card_le_card inc).trans (card_union_le N T)
  rw [G.card_neighborFinset_eq_degree] at cnt
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  exact cnt

/-- A connected dense side yields a route from its prescribed anchor.
The two costs are the longest path deficit and the trimming needed to
start from a prescribed contact. -/
theorem from_region (W : Finset V) (u : V) {d t b : ℕ} (pos : 1≤d)
    (min : ∀ x : W, d≤(G.induce (W:Set V)).degree x)
    (large : 1<W.card) (size : W.card≤2*d+1+b)
    (con : W.card≤2*d+1 ∨ (G.induce (W:Set V)).Connected)
    (port : ∃ x∈W, G.Adj u x)
    (remote : (W.filter (fun x => ¬G.Adj u x)).card < d+t)
    (room : (W.filter (fun x => ¬G.Adj u x)).card≤2*d) :
    Route G W u (b+t) := by
  classical
  let J := G.induce (W:Set V)
  let P := W.filter (G.Adj u)
  let T := P.subtype (fun x => x∈W)
  letI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using large)
  have cardT : T.card=P.card := by
    rw [show T=P.subtype (fun x => x∈W) from rfl,card_subtype,
      filter_eq_self.mpr (fun v h => (mem_filter.mp h).1)]
  have tag : T.Nonempty := by
    obtain ⟨v,vw,uv⟩ := port
    exact ⟨⟨v,vw⟩,mem_subtype.mpr (mem_filter.mpr ⟨vw,uv⟩)⟩
  have eqT : ((univ:Finset W)\T).card=(W.filter (fun x => ¬G.Adj u x)).card := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_coe,cardT]
    have total := card_filter_add_card_filter_not (s:=W) (p:=G.Adj u)
    change W.card-(W.filter (G.Adj u)).card=_
    omega
  have chosen : ∃ x y, ∃ p : J.Walk x y, p.IsPath ∧
      (∀ {a b}, ∀ q : J.Walk a b, q.IsPath → q.length≤p.length) ∧
      (p.support.length=W.card ∨ 2*d+1≤p.support.length) := by
    rcases con with short|hc
    · obtain ⟨x,y,p,hp⟩ := Graph189PortPath.of_degree min (by simpa using short)
      have len : p.support.length=W.card := hp.length_support.trans (Fintype.card_coe W)
      refine ⟨x,y,p,hp.isPath,?_,Or.inl len⟩
      intro x y q hq
      have upper := hq.support_nodup.length_le_card
      change _ ≤ Fintype.card W at upper
      rw [Fintype.card_coe] at upper
      have pL:=p.length_support
      have qL:=q.length_support
      omega
    · obtain ⟨x,y,p,hp,mx,len⟩ := Graph189SidePathDegree.longest_order hc pos min
      exact ⟨x,y,p,hp,mx,len.imp (fun h => h.trans (Fintype.card_coe W)) id⟩
  obtain ⟨x,y,p,hp,mx,len⟩ := chosen
  have on : ∃ i≤p.length, p.getVert i∈T := by
    by_contra! fail
    have inc : p.support.toFinset⊆univ\T := by
      intro v hv
      obtain ⟨j,val,jp⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hv)
      exact mem_sdiff.mpr ⟨mem_univ _,val ▸ fail j jp⟩
    have cnt := card_le_card inc
    rw [List.toFinset_card_of_nodup hp.support_nodup] at cnt
    have split := card_filter_add_card_filter_not (s:=W) (p:=G.Adj u)
    have hit := tag.card_pos
    rw [cardT] at hit
    change 0<(W.filter (G.Adj u)).card at hit
    omega
  obtain ⟨a,atT,b',q,hq,cost⟩ := Graph189PortRotation.from_longest p hp mx T on (s:=t) (by
    have hd := min x
    change d≤J.degree x at hd
    change _ < (J.degree x)+t
    rw [eqT]
    omega)
  let f := (Embedding.induce (G:=G) (W:Set V)).toHom
  let r := q.map f
  have actual : a.val∈P := mem_subtype.mp atT
  refine ⟨_,_,r,hq.map Subtype.val_injective,(mem_filter.mp actual).2,?_,?_⟩
  · intro w hw
    rw [show r.support=q.support.map f from Walk.support_map _ _] at hw
    obtain ⟨w',_,rfl⟩ := List.mem_map.mp hw
    exact w'.property
  · have eq : r.support.length=q.support.length := by simp [r]
    omega

#print axioms from_region
end Graph189DenseSideRoute
