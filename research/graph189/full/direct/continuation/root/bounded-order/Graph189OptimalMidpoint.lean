import Graph189OptimalExterior
import Graph189ExteriorHalf

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Consecutive vertices of a longest path cannot both touch one connected
part of its exterior. This includes the case of identical contact vertices. -/
theorem no_next_contact {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀{u v},∀q : G.Walk u v,q.IsPath → q.length≤p.length)
    {F : V→Finset V} (part : Partition G p.support.toFinsetᶜ F)
    {i x w : V} (xi : x∈F i) (wi : w∈F i) {t : ℕ} (valid : t+1<p.support.length)
    (left : G.Adj (p.getVert t) x) : ¬G.Adj w (p.getVert (t+1)) := by
  classical
  intro edge
  obtain ⟨s,hs⟩ := (part.connected i ⟨x,xi⟩ ⟨w,wi⟩).exists_isPath
  let emb := (Embedding.induce (G:=G) (F i : Set V)).toHom
  let r : G.Walk x w := s.map emb
  have path : r.IsPath := hs.map Subtype.val_injective
  have dis : List.Disjoint r.support p.support := by
    rw [List.disjoint_left]
    intro z hz on
    rw [show r.support=s.support.map emb from Walk.support_map _ _] at hz
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
    exact (mem_compl.mp ((part.cover _).mpr ⟨i,v.property⟩)) (List.mem_toFinset.mpr on)
  have gap := interval_of_detour p hp longest ⟨t,by omega⟩ ⟨t+1,valid⟩
    (by change t<t+1; omega) r path dis (by simpa only [get_at] using left)
    (by simpa only [get_at] using edge)
  change t+1+r.support.length≤t+1 at gap
  have len := r.length_support
  omega

/-- The only vertex that can lie between two marks two positions apart for a
noncut vertex of a smallest high-bearing exterior part is the exceptional low vertex. -/
theorem midpoint_low {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀{u v},∀q : G.Walk u v,q.IsPath → q.length≤p.length)
    {F : V→Finset V} (part : Partition G p.support.toFinsetᶜ F)
    (optimal : ∀{u v},∀q : G.Walk u v,q.IsPath → q.length=p.length →
      ∀K : V→Finset V,Partition G q.support.toFinsetᶜ K → score K≤score F)
    {i x : V} (xi : x∈F i) (noncut : (G.induce ((F i).erase x:Set V)).Preconnected)
    {k : ℕ} (least : ∀j,(∃v∈F j,k≤G.degree v) → (F i).card≤(F j).card)
    {t : ℕ} (valid : t+2<p.support.length)
    (left : G.Adj (p.getVert t) x) (right : G.Adj (p.getVert (t+2)) x)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v) :
    G.degree (p.getVert (t+1))<k := by
  classical
  by_contra! high
  let y := p.getVert (t+1)
  have yon : y∈p.support.toFinset := List.mem_toFinset.mpr (p.getVert_mem_support _)
  have xoff := mem_compl.mp ((part.cover _).mpr ⟨i,xi⟩)
  have ne : x≠y := fun e => xoff (e ▸ yon)
  obtain ⟨u,v,q,hq,len,swap⟩ := swap_contact_midpoint p hp
    (fun h => xoff (List.mem_toFinset.mpr h)) t valid left right
  have newU : q.support.toFinsetᶜ=insert y (p.support.toFinsetᶜ.erase x) := by
    ext z
    rw [swap]
    simp only [mem_compl,mem_insert,mem_erase]
    change (¬(z=x ∨ z≠y ∧ z∈p.support.toFinset)) ↔ z=y ∨ z≠x ∧ z∉p.support.toFinset
    grind
  have yoff : y∉q.support := by
    have h : y∈q.support.toFinsetᶜ := newU ▸ mem_insert_self _ _
    exact fun hy => (mem_compl.mp h) (List.mem_toFinset.mpr hy)
  obtain ⟨⟨z,zo,edge,zh⟩,_⟩ := high_exterior_half q hq
    (fun r hr => (longest r hr).trans_eq len.symm) yoff (quota _) high minimum uniqueLow
  have zout : z∈q.support.toFinsetᶜ := mem_compl.mpr (fun h => zo (List.mem_toFinset.mp h))
  rw [newU] at zout
  have old := (mem_erase.mp ((mem_insert.mp zout).resolve_left edge.ne.symm)).2
  obtain ⟨j,zj⟩ := (part.cover z).mp old
  have diff : i≠j := by
    rintro rfl
    exact no_next_contact p hp longest part xi zj (by omega) left edge.symm
  obtain ⟨K,data,increase⟩ := exchange part diff xi (fun h => mem_compl.mp h yon)
    zj edge noncut (least j ⟨z,zj,zh⟩)
  exact (Nat.not_lt_of_ge (optimal q hq len K (newU ▸ data))) increase

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.midpoint_low
