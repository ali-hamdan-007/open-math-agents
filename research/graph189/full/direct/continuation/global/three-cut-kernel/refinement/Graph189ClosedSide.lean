import Graph189AlmostFullColumn

open SimpleGraph Finset Graph189PositiveEvenCut
namespace Graph189ClosedSide
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S U Y : Finset V}

/-- If all but t even-distance slots at b are used on the other side,
and b has more than t separator contacts, at most t other B-vertices
can be absent from the closed neighborhood of b. -/
theorem neighborhood (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    {b : V} (hb : b∈B) {k t : ℕ} (cap : G.distEven b≤k+1)
    (us : U⊆A) (uEven : U⊆evenOthers G b) (used : k≤U.card+t)
    (contacts : t<(Graph189PortLabels.support G S b).card)
    (connected : G.Connected) :
    ∃ E : Finset V, E.card≤t ∧ ∀ v∈B,v∉E → v≠b → G.Adj b v := by
  classical
  let E := evenOthers G b \ U
  let T := S \ Graph189PortLabels.support G S b
  let K := E∪T
  have counts := card_sdiff_add_card_eq_card uEven
  change E.card+U.card=_ at counts
  have emax := even_others_card cap
  have ec : E.card≤t := by omega
  have ts := card_sdiff_add_card_eq_card (show Graph189PortLabels.support G S b⊆S from filter_subset _ _)
  change T.card+(Graph189PortLabels.support G S b).card=S.card at ts
  have ksmall : K.card<S.card := by
    have ku : K.card≤E.card+T.card := card_union_le _ _
    omega
  have bK : b∉K := by
    intro mem
    rcases mem_union.mp mem with e | missing
    · exact (mem_erase.mp (mem_sdiff.mp e).1).1 rfl
    · exact disjoint_left.mp cut.right_cut hb (mem_sdiff.mp missing).1
  have adjacent {v : V} (vb : v∈B) (vE : v∉E) (vb' : v≠b) : G.Adj b v := by
    by_contra nonadj
    have vK : v∉K := fun h => (mem_union.mp h).elim vE
      (fun hT => disjoint_left.mp cut.right_cut vb (mem_sdiff.mp hT).1)
    let D := {w : V | w∉K}
    obtain ⟨p⟩ := smaller K ksmall (⟨v,vK⟩ : D) (⟨b,bK⟩ : D)
    let far (w : D) := w.val∈B ∧ w.val≠b ∧ ¬G.Adj b w.val
    obtain ⟨w,u,hw,hu,edge,_⟩ := Graph189CutSides.walk_exits (G:=G.induce D) far p
      ⟨vb,vb',nonadj⟩ (fun h => h.2.1 rfl)
    have wu : G.Adj w.val u.val := edge
    have bu : G.Adj b u.val := by
      rcases cut.cover u.val with ua | ub | ui
      · exact (cut.no_cross _ ua _ hw.1 wu.symm).elim
      · by_contra missing
        have un : u.val≠b := fun eq => hw.2.2 (eq ▸ wu.symm)
        exact hu ⟨ub,un,missing⟩
      · by_contra missing
        apply u.property
        exact mem_union_right _ (mem_sdiff.mpr ⟨ui,fun support => missing (mem_filter.mp support).2⟩)
    have w2 := Graph189PrivateQuota.exact_two connected bu wu.symm hw.2.1.symm hw.2.2
    apply w.property
    exact mem_union_left _ (mem_sdiff.mpr
      ⟨mem_even_others hw.2.1 (by simp [w2]),fun h => disjoint_left.mp cut.apart (us h) hw.1⟩)
  exact ⟨E,ec,fun _ vb ve ne => adjacent vb ve ne⟩

/-- All high vertices missing an anchor adjacent to b, except at most t,
belong to the exact second layer at that anchor. -/
theorem second_column (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    {b : V} (hb : b∈B) {k t : ℕ} (cap : G.distEven b≤k+1)
    (us : U⊆A) (uEven : U⊆evenOthers G b) (used : k≤U.card+t)
    (contacts : t<(Graph189PortLabels.support G S b).card) (connected : G.Connected)
    (ys : Y⊆B) {j : V} (hj : j∈S) (bj : G.Adj b j) :
    Y.card≤(Y.filter (G.Adj j)).card+(Y.filter (fun v => G.dist j v=2)).card+t := by
  classical
  obtain ⟨E,emax,near⟩ := neighborhood cut smaller hb cap us uEven used contacts connected
  let F := Y.filter (G.Adj j)
  let D := Y.filter (fun v => G.dist j v=2)
  have incl : Y⊆F∪D∪E := by
    intro v hv
    by_cases port : G.Adj j v
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hv,port⟩))
    by_cases e : v∈E
    · exact mem_union_right _ e
    have vb : v≠b := fun eq => port (eq ▸ bj.symm)
    have vj : v≠j := fun eq => disjoint_left.mp cut.right_cut (ys hv) (eq ▸ hj)
    have d := Graph189PrivateQuota.exact_two connected bj.symm (near v (ys hv) e vb) vj.symm port
    exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hv,d⟩))
  have nf := (card_le_card incl).trans (card_union_le _ _)
  have nc := card_union_le F D
  change Y.card≤F.card+D.card+t
  omega

#print axioms neighborhood
#print axioms second_column
end Graph189ClosedSide
