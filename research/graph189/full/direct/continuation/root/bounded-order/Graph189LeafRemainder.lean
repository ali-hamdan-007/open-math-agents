import Graph189ExteriorLeaf
import Graph189OptimalCoreOrder
import Graph189RootedOneLow

open SimpleGraph Finset Graph189ExteriorGap Graph189OptimalExterior
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Even the exceptional low vertex has at least two internal neighbors in a
high-bearing exterior component. -/
theorem two_internal {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    {x : V} (xc : x∈C) (four : 4≤k) (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    2≤(G.neighborFinset x∩C).card := by
  by_cases high : k≤G.degree x
  · have half := internal_half h xc high (quota _) minimum uniqueLow
    omega
  obtain ⟨v,vc,vh⟩ := h.high
  have vx : v≠x := fun eq => high (eq ▸ vh)
  obtain ⟨y,ys,z,zc,zs,edge⟩ := crossing h.connected (singleton_subset_iff.mpr xc)
    (singleton_nonempty x) vc (by simpa using vx)
  have sy : y=x := mem_singleton.mp ys
  subst y
  have zh : k≤G.degree z := by
    by_contra! low
    exact zs (mem_singleton.mpr (uniqueLow _ _ low (by omega)))
  have sum := adjacent_ambient_degree_sum p h.path h.longest (h.outside _ xc) (h.outside _ zc) edge (quota _)
  have split := degree_split h xc
  have parts := card_sdiff_add_card_inter (G.neighborFinset x) p.support.toFinset
  rw [←contact_card_neighbors p h.path x] at parts
  change _+(contactPositions p x).card=G.degree x at parts
  have min := minimum x
  omega

/-- After leaving a leaf at its articulation, a tail can cover at least
ceil(k/2) further exterior vertices, including when the remainder has the low
vertex. The rooted one-low theorem works directly on the remainder. -/
theorem remainder_route {a b : V} {p : G.Walk a b} {C D : Finset V} {w : V} {k : ℕ}
    (h : Chosen p C k) (L : Limb G C D w) (four : 4≤k)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    let R := C \ insert w D
    (k+1)/2≤R.card ∧
    ∃r∈R,G.Adj w r ∧ ∃y,∃q : G.Walk r y,q.IsPath ∧ (k+1)/2≤q.support.length ∧ ∀v∈q.support,v∈R := by
  classical
  let R := C \ insert w D
  let J := G.induce (R:Set V)
  have sub : R⊆C := sdiff_subset
  have notW : w∉R := fun hw => (mem_sdiff.mp hw).2 (mem_insert_self _ _)
  obtain ⟨u,uc,uD,uw⟩ := L.remainder
  have non : R.Nonempty := ⟨u,mem_sdiff.mpr ⟨uc,fun m => (mem_insert.mp m).elim uw uD⟩⟩
  have boundary {v y : V} (vr : v∈R) (yc : y∈C) (edge : G.Adj v y) : y∈R ∨ y=w := by
    by_cases eq : y=w
    · exact Or.inr eq
    refine Or.inl (mem_sdiff.mpr ⟨yc,fun m => ?_⟩)
    have yd := (mem_insert.mp m).resolve_left eq
    exact (mem_sdiff.mp vr).2 (mem_insert.mpr (L.exits _ yd _ (sub vr) edge.symm).symm)
  have loss (v : R) : (G.neighborFinset v.val∩C).card≤J.degree v+1 := by
    have cover : G.neighborFinset v.val∩C⊆insert w (G.neighborFinset v.val∩R) := by
      intro y hy
      obtain ⟨adj,yc⟩ := mem_inter.mp hy
      exact mem_insert.mpr ((boundary v.property yc ((G.mem_neighborFinset _ _).mp adj)).elim
        (fun yr => Or.inr (mem_inter.mpr ⟨adj,yr⟩)) Or.inl)
    have graph : J.degree v=(G.neighborFinset v.val∩R).card := by
      rw [show J.degree v=_ from Graph189ExteriorDegreeCycle.degree_induce_filter (R:Set V) v]
      congr 1
    rw [graph]
    exact (card_le_card cover).trans (card_insert_le _ _)
  obtain ⟨r,rr,y,yc,yo,e⟩ := crossing h.connected sub non L.gate notW
  have yw := (boundary rr yc e).resolve_left yo
  have minr := two_internal h (sub rr) four quota minimum uniqueLow
  have deg := loss ⟨r,rr⟩
  change (G.neighborFinset r∩C).card≤J.degree ⟨r,rr⟩+1 at deg
  have neigh : ∃v : R,J.Adj ⟨r,rr⟩ v := by
    have pos : 0<J.degree ⟨r,rr⟩ := by omega
    obtain ⟨v,hv⟩ := card_pos.mp pos
    exact ⟨v,(J.mem_neighborFinset _ _).mp hv⟩
  have pair {i : R} (high : k≤G.degree i.val) : (k+1)/2-1≤J.degree i := by
    have half := internal_half h (sub i.property) high (quota _) minimum uniqueLow
    have step := loss i
    omega
  obtain ⟨v,q,hq,len⟩ := Graph189RootedOneLow.rooted_path (H:=J) ⟨r,rr⟩ neigh (d:=(k+1)/2-1) (by
    intro i j ne
    by_cases hi : k≤G.degree i.val
    · exact Or.inl (pair hi)
    apply Or.inr (pair ?_)
    by_contra! low
    exact ne (Subtype.ext (uniqueLow _ _ (by omega) low)))
  let emb := (Embedding.induce (G:=G) (R:Set V)).toHom
  let s : G.Walk r v.val := q.map emb
  have path : s.IsPath := hq.map Subtype.val_injective
  have sizeBound := hq.support_nodup.length_le_card
  have inside {z : V} (zs : z∈s.support) : z∈R := by
    rw [show s.support=q.support.map emb from Walk.support_map _ _] at zs
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp zs
    exact i.property
  have sl : s.support.length=q.support.length := by rw [show s.support=q.support.map emb from Walk.support_map _ _,List.length_map]
  change (k+1)/2≤R.card ∧ _
  change q.support.length≤Fintype.card R at sizeBound
  rw [Fintype.card_coe] at sizeBound
  exact ⟨by omega,r,rr,yw ▸ e.symm,v.val,s,path,by omega,fun z hz => inside hz⟩

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.remainder_route
