import Graph189BondyOrder

/-! Equality in the linked-set order bound. The disjoint-path extraction below
uses @koolkao's accepted OMA.BondyK.linked_contra and graph189_order_of_linked
scaffolding. We retain the tight separators, degrees and exterior component. -/
open SimpleGraph Finset OMA.BondyK
namespace Graph189BondyEquality
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c d k : ℕ} {f : ℕ→V} {H D : Finset V}

structure Layout (G : SimpleGraph V) [DecidableRel G.Adj] (c k d : ℕ) (f : ℕ→V)
    (H : Finset V) (s : ℕ→ℕ) : Prop where
  sorted : ∀ i j, i<j → j≤k → s i<s j
  period : s k=s 0+c
  anchor_count : ((Finset.range k).image (fun j => f (s j))).card=k
  outside : ∀ x ∈ H, ∀ t, f t ≠ x
  size : H.card+k=d+1
  neighbors : ∀ x∈H, G.neighborFinset x=H.erase x ∪ (Finset.range k).image (fun j => f (s j))
  successors : ∀ j<k, G.degree (f (s j+1))=d

private theorem separator_neighbors {v : V} (hD : Cy G c f) (hC : Comp G f H)
    (sub : D⊆H) {S : Finset V} (meet : Sep G D ((range c).image f) S)
    (outside : v∈D) (free : v∉S) (size : S.card=k)
    (low : ∀ x, d≤G.degree x) (count : H.card+k=d+1) :
    S⊆(range c).image f ∧ ∀ x∈H, G.neighborFinset x=H.erase x ∪S := by
  classical
  let T := (G.neighborFinset v) \ H
  have ts : T⊆S := by
    intro y hy
    obtain ⟨edge,off⟩ := mem_sdiff.mp hy
    have e := (G.mem_neighborFinset _ _).mp edge
    obtain ⟨i,hi⟩ := (hC.cl v (sub outside) y e).resolve_left off
    have m := hD.mem_cset i
    rw [hi] at m
    have path : ABP G D ((range c).image f) [v,y] :=
      ⟨by simpa using e.ne,by simp [e],⟨v,outside,rfl⟩,⟨y,m,rfl⟩⟩
    obtain ⟨x,hx,hS⟩ := meet _ path
    rcases (show x=v ∨ x=y by simpa using hx) with rfl|rfl
    · exact (free hS).elim
    · exact hS
  have cut : T=S := by
    apply eq_of_subset_of_card_le ts
    have subset : G.neighborFinset v ∩ H ⊆ H.erase v := by
      intro x hx
      obtain ⟨hv,hh⟩ := mem_inter.mp hx
      exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hv).ne.symm,hh⟩
    have upper := card_le_card subset
    rw [card_erase_of_mem (sub outside)] at upper
    have part := card_sdiff_add_card_inter (G.neighborFinset v) H
    rw [G.card_neighborFinset_eq_degree] at part
    have positive := card_pos.mpr ⟨v,sub outside⟩
    have dv := low v
    change T.card+_= _ at part
    omega
  have ons : S⊆(range c).image f := by
    rw [←cut]
    intro y hy
    obtain ⟨edge,off⟩ := mem_sdiff.mp hy
    obtain ⟨i,hi⟩ := (hC.cl v (sub outside) y ((G.mem_neighborFinset _ _).mp edge)).resolve_left off
    exact hi ▸ hD.mem_cset i
  have apart : Disjoint H S := by
    apply Finset.disjoint_left.mpr
    intro y hy ys
    obtain ⟨i,_,eq⟩ := mem_image.mp (ons ys)
    exact hC.off y hy i eq
  refine ⟨ons,?_⟩
  intro x xH
  have inc : G.neighborFinset x⊆H.erase x∪S := by
    intro y hy
    have edge := (G.mem_neighborFinset _ _).mp hy
    by_cases inside : y∈H
    · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,inside⟩)
    obtain ⟨i,eq⟩ := (hC.cl x xH y edge).resolve_left inside
    have on : y∈(range c).image f := eq ▸ hD.mem_cset i
    obtain ⟨X,nd,chain,members,first,last⟩ := hC.conn v (sub outside) x xH
    have absent : y∉X := fun m => inside (members y m)
    have path : ABP G D ((range c).image f) (X++[y]) := by
      refine ⟨List.nodup_append.mpr ⟨nd,by simp,?_⟩,List.isChain_append.mpr ⟨chain,by simp,?_⟩,
        ⟨v,outside,?_⟩,⟨y,on,?_⟩⟩
      · intro a ha b hb eq
        have be : b=y := by simpa using hb
        exact absent ((eq.trans be) ▸ ha)
      · intro a ha b hb
        have ax : x=a := by simpa [last] using ha
        have by' : y=b := by simpa using hb
        simpa only [ax,by'] using edge
      · simp [List.head?_append,first]
      · simp [List.getLast?_append]
    obtain ⟨q,hq,qs⟩ := meet _ path
    rcases List.mem_append.mp hq with qx|qy
    · exact (Finset.disjoint_left.mp apart (members q qx) qs).elim
    · have eq : q=y := by simpa using qy
      exact mem_union_right _ (eq ▸ qs)
  apply eq_of_subset_of_card_le inc
  rw [card_union_of_disjoint (apart.mono_left (erase_subset _ _)),card_erase_of_mem xH,
    size,G.card_neighborFinset_eq_degree]
  have := low x
  have positive := card_pos.mpr ⟨x,xH⟩
  omega

/-- The component and cyclic contact list in the equality case of the
accepted linked-set estimate. The degree d is an explicit lower bound. -/
theorem linked_layout (hD : Cy G c f) (hC : Comp G f H) (hδ : ∀ x, d≤G.degree x)
    (hk : 1≤k) (eqn : Fintype.card V+k*k=(k+1)*d+k+1) (hK : KSep G k)
    (hDH : D⊆H) (hDk : k+1≤D.card)
    (hDl : ∀ x∈D, ∀ y∈D, x≠y → ∃ X, HP G D x y X ∧ k≤X.length) :
    ∃ s, Layout G c k d f H s := by
  set Cs := (Finset.range c).image f with hCs
  have hsepk := sep_ge hD hC hK hDH hDk
  have hHD : D.card ≤ H.card := Finset.card_le_card hDH
  have hk1 : k * (k - 1) + k = k * k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp; ring
  by_cases h : ∀ S : Finset V, (∀ l, ABP G D Cs l → ∃ x ∈ l, x ∈ S) → k + 1 ≤ S.card
  · obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs (k + 1) h
    obtain ⟨s, hs, hsq, hatt, hph, -⟩ := ends_sorted hD hC hDH hDl (by omega) P hP hdisj
    have := succ_deg hD hC (q := k + 1) (by omega) hs hsq hatt
      (fun i hi j hj hij => by simpa using hph i hi j hj hij)
    have hsum : (k + 1) * d ≤ ∑ i ∈ Finset.range (k + 1), G.degree (f (s i + 1)) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) => hδ (f (s i + 1)))
      simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this
    have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    exfalso
    nlinarith
  · push Not at h
    obtain ⟨S, hS, hSk⟩ := h
    have hSc : S.card = k := le_antisymm (by omega) (hsepk S hS)
    obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs k (fun S' hS' => hsepk S' hS')
    obtain ⟨s, hs, hsq, hatt, hph, hend⟩ := ends_sorted hD hC hDH hDl hk P hP hdisj
    -- every separator vertex lies on one of the paths
    have hmeet : ∀ i, ∃ x ∈ P i, x ∈ S := fun i => hS _ (hP i).1
    choose σ hσP hσS using hmeet
    have σinj : Function.Injective σ := by
      intro i j hij; by_contra hne; exact hdisj i j hne _ (hσP i) (hij ▸ hσP j)
    have himg : Finset.univ.image σ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact hσS i
      · rw [Finset.card_image_of_injective _ σinj, hSc]; simp
    have onP : ∀ x ∈ S, ∃ i, x ∈ P i := by
      intro x hx; rw [← himg] at hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact ⟨i, hσP i⟩
    obtain ⟨v, hvD, hvS⟩ : ∃ v ∈ D, v ∉ S := by
      by_contra h'; push Not at h'
      have := Finset.card_le_card (show D ⊆ S from h'); omega
    have hvH := hDH hvD
    have hN : ∀ t, G.Adj v (f t) → ∃ j < k, f t = f (s j) := by
      intro t hvt
      have hl : ABP G D Cs [v, f t] := ⟨by simp; intro h; exact hC.off v hvH t h.symm,
        by simp [hvt], ⟨v, hvD, rfl⟩, ⟨f t, hD.mem_cset t, rfl⟩⟩
      obtain ⟨x, hx, hxS⟩ := hS _ hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd hxS hvS
      · obtain ⟨i, hi⟩ := onP _ hxS
        obtain ⟨j, hj, hjl⟩ := hend i
        refine ⟨j, hj, ?_⟩
        have hne : P i ≠ [] := by intro h; rw [h] at hi; simp at hi
        have hsplit := List.dropLast_append_getLast hne
        rw [← hsplit] at hi
        rcases List.mem_append.mp hi with h1 | h1
        · exact absurd (hD.mem_cset t) ((hP i).2.2 _ h1)
        · simp at h1
          rw [List.getLast?_eq_getLast_of_ne_nil hne] at hjl
          simp at hjl; rw [h1, hjl]
    have hv := vert_deg hD hC hvH hN
    have hsd := succ_deg hD hC (q := k) hk hs hsq hatt
      (fun i hi j hj hij => (hph i hi j hj hij).mono (by omega))
    have hsum : k * d ≤ ∑ i ∈ Finset.range k, G.degree (f (s i + 1)) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => hδ (f (s i + 1)))
      simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this
    have hvd := hδ v
    have size : H.card+k=d+1 := by nlinarith
    have succ (i : ℕ) (hi : i<k) : G.degree (f (s i+1))=d := by
      by_contra bad
      have str : (∑ _j ∈ Finset.range k, d) < ∑ j ∈ Finset.range k, G.degree (f (s j+1)) := by
        apply Finset.sum_lt_sum (fun j _ => hδ (f (s j+1)))
        exact ⟨i,mem_range.mpr hi,lt_of_le_of_ne (hδ _) (Ne.symm bad)⟩
      simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at str
      nlinarith
    obtain ⟨ons,all⟩ := separator_neighbors hD hC hDH hS hvD hvS hSc hδ size
    let A := (range k).image (fun i => f (s i))
    have con : S⊆A := by
      intro y ys
      obtain ⟨m,_,ym⟩ := mem_image.mp (ons ys)
      have vm : y∈G.neighborFinset v := by rw [all v hvH]; exact mem_union_right _ ys
      have e : G.Adj v (f m) := ym.symm ▸ (G.mem_neighborFinset _ _).mp vm
      obtain ⟨j,hj,eq⟩ := hN m e
      exact mem_image.mpr ⟨j,mem_range.mpr hj,eq.symm.trans ym⟩
    have bound : A.card≤k := (card_image_le).trans_eq (card_range k)
    have same := eq_of_subset_of_card_le con (by omega)
    refine ⟨s,hs,hsq,?_,hC.off,size,?_,succ⟩
    · exact (congrArg Finset.card same).symm.trans hSc
    · intro x hx
      exact (all x hx).trans (congrArg (fun T => H.erase x ∪T) same)


/-- From an actual longest cycle and a linked set in its actual exterior,
recover the saturated component and all the periodic anchor data. -/
theorem equality_layout_of_linked
    (hk : 1≤k) (kd : k≤d) (min : d≤G.minDegree)
    (order : Fintype.card V=(k+1)*(d-k+2)-1)
    (deletion : ∀ S : Finset V, S.card<k → (G.induce ((S : Set V)ᶜ)).Connected)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (Q : G.Walk b b), Q.IsCycle → Q.length≤C.length)
    (linked : Graph189LinkedExterior.Linked (G.induce (offWalk C)) k) :
    ∃ H s, Layout G C.length k d (cyc C) H s := by
  classical
  have eqn : Fintype.card V+k*k=(k+1)*d+k+1 := by
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le kd
    rw [he,Nat.add_sub_cancel_left] at order
    rw [he]
    have pos : 1≤(k+1)*(e+2) := Nat.mul_pos (by omega) (by omega)
    have n : Fintype.card V+1=(k+1)*(e+2) := by omega
    nlinarith
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
  refine ⟨H,?_⟩
  apply linked_layout hD hComp (fun x => min.trans (G.minDegree_le_degree x)) hk eqn hKs sub msize
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
  · change (p.support.map Subtype.val).head?=some v.val
    rw [← p.cons_tail_support, List.map_cons, List.head?_cons]
  · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
        Walk.getLast_support]
    rfl

#print axioms linked_layout
#print axioms equality_layout_of_linked
end Graph189BondyEquality
