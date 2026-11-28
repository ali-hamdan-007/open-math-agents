import Graph189TwoCutSingleton
import Graph189MatchedOrder

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189EndpointPivotCount
variable {V : Type*} {G : SimpleGraph V} {a b : V}

theorem gap [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (i j : ℕ) (ij : i<j) (valid : j≤p.length) (chord : G.Adj a (p.getVert j))
    {r s : V} (q : G.Walk r s) (hq : q.IsPath) (outside : List.Disjoint q.support p.support)
    (contact : G.Adj (p.getVert i) r) : i+1+q.support.length≤j := by
  let l := (p.take i).reverse
  let t := p.drop j
  have left {v : V} (h : v∈l.support) : v∈p.support.take (i+1) := by
    simpa [l,Walk.support_take] using h
  have right {v : V} (h : v∈t.support) : v∈p.support.drop j := by
    simpa [t,Walk.drop_support_eq_support_drop_min,Nat.min_eq_left valid] using h
  have dis : List.Disjoint l.support t.support := by
    have nd : (p.support.take (i+1)++p.support.drop (i+1)).Nodup := by simpa using hp.support_nodup
    apply List.disjoint_left.mpr
    intro v hv ht
    exact List.disjoint_left.mp nd.disjoint (left hv) ((List.drop_sublist_drop_left _ ij).subset (right ht))
  obtain ⟨core,pc,sc⟩ := Graph189TwoCutSingleton.joined l (hp.take i).reverse t (hp.drop j) chord dis
  have apart : List.Disjoint q.reverse.support core.support := by
    rw [Walk.support_reverse,sc,List.disjoint_left]
    intro v hv hc
    apply List.disjoint_left.mp outside (List.mem_reverse.mp hv)
    exact (List.mem_append.mp hc).elim (fun h => (List.take_subset _ _) (left h))
      (fun h => (List.drop_subset _ _) (right h))
  obtain ⟨full,pf,sf⟩ := Graph189TwoCutSingleton.joined q.reverse hq.reverse core pc contact.symm apart
  have bound := mx full pf
  have n := full.length_support
  rw [sf,sc,List.length_append,List.length_append,Walk.support_reverse,List.length_reverse] at n
  have ll : l.support.length=i+1 := by
    simp [l,Walk.length_support,Walk.take_length,Nat.min_eq_left (show i≤p.length by omega)]
  have rr : t.support.length=p.length-j+1 := by simp [t,Walk.length_support,Walk.drop_length]
  omega

/-- An endpoint can use none of three disjoint five-position intervals
when its chords avoid the three marks and each mark starts an exterior tail
of four vertices. -/
theorem degree [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (i j k : ℕ) (ipos : 0 < i) (mid : i+5≤j) (jk : j+5≤k)
    (room : k+5≤p.support.length) (short : p.support.length≤21)
    (miss : ∀ t, t∈({i,j,k} : Finset ℕ) → ¬G.Adj a (p.getVert t))
    (tail : ∀ t, t∈({i,j,k} : Finset ℕ) →
      ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ List.Disjoint q.support p.support ∧
        G.Adj (p.getVert t) u ∧ 4≤q.support.length) :
    G.degree a≤5 := by
  classical
  let A := Ico i (i+5)
  let B := Ico j (j+5)
  let C := Ico k (k+5)
  let D := insert 0 (A∪B∪C)
  let N := (range p.support.length).filter (fun t => G.Adj a (p.getVert t))
  have avoid (t : ℕ) (ht : t∈({i,j,k} : Finset ℕ)) (z : ℕ) (hz : z∈Ico t (t+5)) (zr : z∈N) : False := by
    have edge := (mem_filter.mp zr).2
    have pos := mem_Ico.mp hz
    by_cases eq : t=z
    · exact miss t ht (eq ▸ edge)
    obtain ⟨u,v,q,hq,out,contact,len⟩ := tail t ht
    have valid := mem_range.mp (mem_filter.mp zr).1
    have pl := p.length_support
    have h := gap p hp mx t z (by omega) (by omega) edge q hq out contact
    omega
  have dis : Disjoint D N := by
    apply Finset.disjoint_left.mpr
    intro z dz nz
    rcases mem_insert.mp dz with rfl|d
    · exact G.irrefl (by simpa using (mem_filter.mp nz).2)
    rcases mem_union.mp d with ab|c
    · rcases mem_union.mp ab with a|b
      · exact avoid i (by simp) z a nz
      · exact avoid j (by simp) z b nz
    · exact avoid k (by simp) z c nz
  have distinct (u v : ℕ) (uv : u+5≤v) : Disjoint (Ico u (u+5)) (Ico v (v+5)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have l := mem_Ico.mp hx
    have r := mem_Ico.mp hy
    omega
  have sz : D.card=16 := by
    have ab : Disjoint A B := distinct i j mid
    have ac : Disjoint A C := distinct i k (by omega)
    have bc : Disjoint B C := distinct j k jk
    have zero : 0∉A∪B∪C := by simp [A,B,C,show i≠0 by omega,show j≠0 by omega,show k≠0 by omega]
    rw [show D=insert 0 (A∪B∪C) from rfl,card_insert_of_notMem zero,
      card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨ac,bc⟩),card_union_of_disjoint ab]
    simp [A,B,C]
  have cover : D∪N⊆range p.support.length := by
    intro v hv
    rcases mem_union.mp hv with d|n
    · apply mem_range.mpr
      rcases mem_insert.mp d with rfl|e
      · omega
      rcases mem_union.mp e with ab|c
      · rcases mem_union.mp ab with a|b
        · have := (mem_Ico.mp a).2; omega
        · have := (mem_Ico.mp b).2; omega
      · have := (mem_Ico.mp c).2; omega
    · exact (mem_filter.mp n).1
  have count := card_le_card cover
  rw [card_union_of_disjoint dis,sz,card_range] at count
  have all : G.neighborFinset a⊆N.image p.getVert := by
    intro v hv
    have e := (G.mem_neighborFinset _ _).mp hv
    have on : v∈p.support := by
      by_contra absent
      have h := mx (p.cons e.symm) (Walk.IsPath.mk' (by simp [absent,hp.support_nodup]))
      simp at h
    obtain ⟨t,ht,eq⟩ := List.mem_iff_getElem.mp on
    have eq' : p.getVert t=v := (get_at p ht).symm.trans eq
    exact mem_image.mpr ⟨t,mem_filter.mpr ⟨mem_range.mpr ht,by rwa [eq']⟩,eq'⟩
  have upper := (card_le_card all).trans (card_image_le (f:=p.getVert))
  rw [G.card_neighborFinset_eq_degree] at upper
  omega

#print axioms gap
#print axioms degree
end Graph189EndpointPivotCount
