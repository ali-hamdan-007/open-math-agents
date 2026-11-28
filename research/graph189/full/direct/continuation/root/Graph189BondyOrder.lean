import Graph189LinkedExterior
import Graph189BondyCore

namespace OMA.BondyK

open SimpleGraph Finset Arxiv.«2606.03696»

/-- The actual disjoint attachment and exterior sets used in the linked degree inequality. -/
theorem graph189_linked_witness {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (deletion : ∀ S : Finset V, S.card<k → (G.induce ((S : Set V)ᶜ)).Connected)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b, ∀ Q : G.Walk b b, Q.IsCycle → Q.length≤C.length)
    (linked : Graph189LinkedExterior.Linked (G.induce (offWalk C)) k) :
    ∃ H D : Finset V, Cy G C.length (cyc C) ∧ Comp G (cyc C) H ∧ KSep G k ∧
      D⊆H ∧ k+1≤D.card ∧ ∀ x∈D,∀ y∈D,x≠y → ∃ L, HP G D x y L ∧ k≤L.length := by
  classical
  let L : Set ℕ := {m | ∃ b, ∃ q : G.Walk b b, q.IsCycle ∧ q.length=m}
  have mem : C.length∈L := ⟨a,C,hC,rfl⟩
  have upper : ∀ m∈L, m≤C.length := by
    rintro m ⟨b,q,hq,rfl⟩
    exact longest b q hq
  have hlong : C.length=G.circumference :=
    (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  obtain ⟨D,size,paths⟩ := linked
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0<D.card by omega)
  have hD := cy_of C hC hlong
  have hsupp := mem_support_cyc C hC
  have mem_s : ∀ y, y ∈ offWalk C ↔ y ∉ C.support := fun y => Iff.rfl
  classical
  obtain ⟨H, hH⟩ : ∃ H : Finset V, H = Finset.univ.filter
      (fun y => ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩) := ⟨_, rfl⟩
  have memH : ∀ y, y ∈ H ↔ ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩ := by
    intro y; simp [hH]
  have hComp : Comp G (cyc C) H := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx t ht
      obtain ⟨hxs, -⟩ := (memH x).mp hx
      exact (mem_s x).mp hxs ((hsupp x).mpr ⟨t, ht⟩)
    · intro x hx y hxy
      obtain ⟨hxs, hr⟩ := (memH x).mp hx
      by_cases hy : y ∈ C.support
      · exact Or.inr ((hsupp y).mp hy)
      · left
        have hys : y ∈ offWalk C := (mem_s y).mpr hy
        exact (memH y).mpr ⟨hys, hr.trans (Adj.reachable (G := G.induce (offWalk C))
          (u := ⟨x, hxs⟩) (v := ⟨y, hys⟩) hxy)⟩
    · intro x hx y hy
      obtain ⟨hxs, hrx⟩ := (memH x).mp hx
      obtain ⟨hys, hry⟩ := (memH y).mp hy
      obtain ⟨w⟩ := hrx.symm.trans hry
      obtain ⟨p, hp⟩ := w.toPath
      refine ⟨p.support.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
      · exact hp.support_nodup.map Subtype.val_injective
      · exact (List.isChain_map Subtype.val).mpr p.isChain_adj_support
      · intro z hz
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact (memH z').mpr ⟨z'.2, hrx.trans (reach_mem p hz')⟩
      · rw [← p.cons_tail_support, List.map_cons, List.head?_cons]
      · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
          Walk.getLast_support]; rfl
  have hKs : KSep G k := by
    intro S hS X hXS hXcl hXne y hyS hyX
    obtain ⟨x, hx⟩ := hXne
    have hconn := deletion S (by omega)
    obtain ⟨w⟩ := hconn.preconnected ⟨x, hXS x hx⟩ ⟨y, hyS⟩
    have key : ∀ (p q : ((S : Set V)ᶜ : Set V)) (w : (G.induce ((S : Set V)ᶜ)).Walk p q),
        p.1 ∈ X → q.1 ∈ X := by
      intro p q w
      induction w with
      | nil => exact id
      | @cons p0 p1 q h w ih =>
        intro hp
        exact ih (hXcl _ hp _ h (fun h' => p1.2 h'))
    exact hyX (key _ _ w hx)
  let e : offWalk C ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let M := D.map e
  have sub : M⊆H := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hz
    apply (memH _).mpr
    refine ⟨y.property,?_⟩
    by_cases eq : u=y
    · subst y
      exact SimpleGraph.Reachable.refl _
    · obtain ⟨p,_,_,_⟩ := paths u hu y hy eq
      exact ⟨p⟩
  have msize : k+1≤M.card := by simpa [M] using size
  refine ⟨H,M,hD,hComp,hKs,sub,msize,?_⟩
  intro x hx y hy ne
  obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hy
  obtain ⟨p,hp,plen,within⟩ := paths v hv w hw (fun same => ne (congrArg e same))
  refine ⟨p.support.map Subtype.val,?_,by simpa only [List.length_map] using plen⟩
  refine ⟨hp.support_nodup.map Subtype.val_injective,
    (List.isChain_map Subtype.val).mpr p.isChain_adj_support,?_,?_,?_⟩
  · intro z hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    exact Finset.mem_map.mpr ⟨b,within b hb,rfl⟩
  · rw [← p.cons_tail_support, List.map_cons, List.head?_cons]
    all_goals rfl
  · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
        Walk.getLast_support]
    rfl

/-- An order bound supplied by a linked set outside an actual longest cycle.
The connectivity input is the small-deletion property. No global order threshold
or conjectured form of Bondy's theorem is used. -/
theorem graph189_order_of_linked {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 1≤k) (min : k≤G.minDegree)
    (deletion : ∀ S : Finset V, S.card<k → (G.induce ((S : Set V)ᶜ)).Connected)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b, ∀ Q : G.Walk b b, Q.IsCycle → Q.length≤C.length)
    (linked : Graph189LinkedExterior.Linked (G.induce (offWalk C)) k) :
    (k+1)*(G.minDegree-k+2)-1 ≤ Fintype.card V := by
  classical
  by_contra! fail
  have order : Fintype.card V+2≤(k+1)*(G.minDegree-k+2) := by omega
  have hkn : Fintype.card V+k*(k-1)≤(k+1)*G.minDegree := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le min
    rw [hd,Nat.add_sub_cancel_left] at order
    rw [hd]
    obtain ⟨h,hl⟩ := Nat.exists_eq_add_of_le hk
    rw [hl,Nat.add_sub_cancel_left]
    rw [hl] at order
    nlinarith
  obtain ⟨H,D,cy,comp,sep,sub,size,paths⟩ := graph189_linked_witness deletion C hC longest linked
  exact linked_contra cy comp (fun x => G.minDegree_le_degree x) hk hkn sep sub size paths

#print axioms graph189_order_of_linked
end OMA.BondyK
