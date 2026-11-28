import Graph189UpstreamBondy
import Graph189MinimumCutOrder
import Graph189ConeNontrivial

open SimpleGraph Finset OMA.BondyK
namespace Graph189BondyExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

private theorem periodic_longest {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : G.Walk b b), R.IsCycle → R.length ≤ C.length) : Cy G C.length (cyc C) := by
  have upper : ∀ m ∈ G.cycleLengths, m ≤ C.length := by
    rintro m ⟨b,R,hR,rfl⟩
    exact longest b R hR
  have max : C.length = G.circumference := by
    change C.length = sSup G.cycleLengths
    have mem : C.length ∈ G.cycleLengths := ⟨a,C,hC,rfl⟩
    exact (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  exact cy_of C hC max

private theorem actual_component {a : V} (C : G.Walk a a) (hC : C.IsCycle) (u : offWalk C) :
    ∃ H : Finset V, Comp G (cyc C) H ∧
      ∀ y, y∈H ↔ ∃ hy : y∈offWalk C, (G.induce (offWalk C)).Reachable u ⟨y,hy⟩ := by
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
      · rw [Walk.support_eq_cons, List.map_cons, List.head?_cons]
      · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
          Walk.getLast_support]; rfl
  exact ⟨H,hComp,memH⟩

private theorem separator_of_connectivity {k : ℕ} (conn : k ≤ G.vertexConnectivity) : KSep G k := by
  intro S hS X hXS hXcl hXne y hyS hyX
  obtain ⟨x, hx⟩ := hXne
  have hconn := Graph189CutSides.connected_after_smaller_deletion (G:=G) S (by omega)
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

/-- The linked-set part of the accepted Bondy proof has no order threshold.
A sufficiently long actual exterior cycle already provides the linked set. -/
theorem excludes_long_exterior {k : ℕ} (positive : 1 ≤ k)
    (conn : k ≤ G.vertexConnectivity)
    (degree : Fintype.card V + k*(k-1) ≤ (k+1)*G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : G.Walk b b), R.IsCycle → R.length ≤ C.length)
    {u : {t : V | t ∉ C.support}} (Q : (G.induce {t : V | t ∉ C.support}).Walk u u)
    (hQ : Q.IsCycle) (size : k+1 ≤ Q.length) (twice : 2*k ≤ Q.length+2) : False := by
  classical
  have hD := periodic_longest C hC longest
  obtain ⟨H,hComp,memH⟩ := actual_component C hC u
  let P := Q.dropLast
  have hP : P.IsPath := hQ.isPath_dropLast
  have hVL : VL G H (P.support.map Subtype.val) := by
    refine ⟨hP.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr P.isChain_adj_support, ?_⟩
    intro z hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (memH z').mpr ⟨z'.2, reach_mem P hz'⟩
  have len : (P.support.map Subtype.val).length = Q.length := by
    simpa [P] using (Graph189ExteriorDegreeCycle.path_of_exterior_cycle Q hQ).2
  have first : (P.support.map Subtype.val).head? = some u.val := by
    rw [←P.cons_tail_support,List.map_cons,List.head?_cons]
  have last : (P.support.map Subtype.val).getLast? = some Q.penultimate.val := by
    rw [List.getLast?_map,List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),Walk.getLast_support]
    rfl
  have closure : ∀ b ∈ (P.support.map Subtype.val).getLast?, ∀ a ∈ (P.support.map Subtype.val).head?,
      G.Adj b a := by
    intro b hb a ha
    rw [first] at ha
    rw [last] at hb
    rw [Option.mem_def,Option.some.injEq] at ha hb
    subst a b
    exact Walk.adj_penultimate hQ.not_nil
  let M := (P.support.map Subtype.val).toFinset
  have card : M.card = Q.length := (List.toFinset_card_of_nodup hVL.1).trans len
  exact linked_contra hD hComp (fun v => G.minDegree_le_degree v) positive degree (separator_of_connectivity conn) (D:=M)
    (fun v hv => hVL.2.2 v (List.mem_toFinset.mp hv)) (by omega)
    (cyc_linked hVL closure (by omega))

private theorem degree_of_short {n d k : ℕ} (pos : 1≤k) (min : k≤d)
    (short : n < (k+1)*(d-k+2)-1) : n+k*(k-1) ≤ (k+1)*d := by
  have step : n+2 ≤ (k+1)*(d-k+2) := by omega
  obtain ⟨m,hd⟩ := Nat.exists_eq_add_of_le min
  rw [hd,Nat.add_sub_cancel_left] at step
  rw [hd]
  obtain ⟨h,hl⟩ := Nat.exists_eq_add_of_le pos
  rw [hl,Nat.add_sub_cancel_left]
  rw [hl] at step
  nlinarith

/-- The exact integral order bound for a long residual cycle, without a
large-order restriction or a premise about the other residual cycles. -/
theorem order_of_long_exterior {k : ℕ} (pos : 1 ≤ k) (conn : k ≤ G.vertexConnectivity)
    (min : k ≤ G.minDegree) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : G.Walk b b), R.IsCycle → R.length ≤ C.length)
    {u : {t : V | t ∉ C.support}} (Q : (G.induce {t : V | t ∉ C.support}).Walk u u)
    (hQ : Q.IsCycle) (size : k+1 ≤ Q.length) (twice : 2*k ≤ Q.length+2) :
    (k+1)*(G.minDegree-k+2)-1 ≤ Fintype.card V := by
  by_contra! short
  apply excludes_long_exterior pos conn _ C hC longest Q hQ size twice
  exact degree_of_short pos min short

/-- An embedded Hamilton-connected set yields the very same order inequality,
even when the ambient exterior has no cycle of twice the connectivity. -/
theorem order_of_hamilton_connected_exterior {k : ℕ} (pos : 1≤k) (conn : k≤G.vertexConnectivity)
    (min : k≤G.minDegree) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : G.Walk b b), R.IsCycle → R.length ≤ C.length)
    {X : Type*} [Fintype X] [DecidableEq X] {J : SimpleGraph X}
    (f : J →g G.induce {v : V | v ∉ C.support}) (inj : Function.Injective f)
    (E : Finset X) (size : k+1≤E.card)
    (hc : ∀ u v : E, u≠v → ∃ q : (J.induce (E : Set X)).Walk u v, q.IsHamiltonian) :
    (k+1)*(G.minDegree-k+2)-1 ≤ Fintype.card V := by
  classical
  by_contra! short
  let g : (J.induce (E : Set X)) →g G.induce (offWalk C) :=
    f.comp (Embedding.induce (G:=J) (E : Set X)).toHom
  have ig : Function.Injective g := inj.comp Subtype.val_injective
  let emb : E ↪ V := ⟨fun t => (g t).val,Subtype.val_injective.comp ig⟩
  let M := (univ : Finset E).map emb
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<E.card by omega)
  let root : E := ⟨u,hu⟩
  obtain ⟨H,hComp,memH⟩ := actual_component C hC (g root)
  have sub : M⊆H := by
    intro v hv
    obtain ⟨t,_,rfl⟩ := mem_map.mp hv
    apply (memH _).mpr
    refine ⟨(g t).property,?_⟩
    by_cases eq : root=t
    · subst t
      exact Reachable.refl _
    obtain ⟨q,_⟩ := hc root t eq
    exact (q.map g).reachable
  have linked (x : V) (hx : x∈M) (y : V) (hy : y∈M) (ne : x≠y) :
      ∃ L, HP G M x y L ∧ k≤L.length := by
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    obtain ⟨j,_,rfl⟩ := mem_map.mp hy
    obtain ⟨q,hq⟩ := hc i j (fun eq => ne (congrArg emb eq))
    refine ⟨q.support.map emb,⟨hq.isPath.support_nodup.map emb.injective,?_,?_,?_,?_⟩,?_⟩
    · apply (List.isChain_map emb).mpr
      exact q.isChain_adj_support.imp (fun a b e => (show G.Adj (emb a) (emb b) from g.map_adj e))
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact mem_map.mpr ⟨w,mem_univ _,rfl⟩
    · rw [Walk.support_eq_cons,List.map_cons,List.head?_cons]
    · rw [List.getLast?_map,List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),Walk.getLast_support]
      rfl
    · rw [List.length_map,hq.length_support]
      change k ≤ Fintype.card E
      rw [Fintype.card_coe]
      omega
  have card : M.card = E.card := by simp [M]
  exact linked_contra (periodic_longest C hC longest) hComp (fun v => G.minDegree_le_degree v) pos
    (degree_of_short pos min short) (separator_of_connectivity conn) sub (by omega) linked

#print axioms order_of_hamilton_connected_exterior
#print axioms excludes_long_exterior
#print axioms order_of_long_exterior
end Graph189BondyExterior
