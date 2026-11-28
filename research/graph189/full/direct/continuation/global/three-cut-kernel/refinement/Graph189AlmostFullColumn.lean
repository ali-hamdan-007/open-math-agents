import Graph189BoundaryDebit
import Graph189PositiveEvenCut
import Graph189ResidualWindows
import Graph189PortDifference

open SimpleGraph Finset Graph189PositiveEvenCut
namespace Graph189AlmostFullColumn
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S X Y : Finset V}

/-- An anchor with all but t of its k possible opposite contacts bounds
the entire other side when the minimum cut can absorb two defects of size t. -/
theorem opposite_population (connected : G.Connected) (cut : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    {k t : ℕ} (cap : ∀ v, G.distEven v≤k+1)
    (xs : X⊆A) (ys : Y⊆B) {i : V} (hi : i∈S)
    (near : k≤(X.filter (G.Adj i)).card+t) (small : 2*t<S.card) :
    Y.card≤k+(Y.filter (G.Adj i)).card+t := by
  classical
  let U := X.filter (G.Adj i)
  let F := Y.filter (G.Adj i)
  obtain ⟨b,hb,bi⟩ := (cut.contacts_of_minimum smaller hi).2
  let E := evenOthers G b \ U
  let T := S \ Graph189PortLabels.support G S b
  let K := E∪T
  have us : U⊆A := (filter_subset _ _).trans xs
  have ub (u : V) (hu : u∈U) : u≠b := fun eq => Finset.disjoint_left.mp cut.apart (us hu) (eq ▸ hb)
  have u2 (u : V) (hu : u∈U) : G.dist b u=2 :=
    Graph189PortDifference.cross_two connected cut.swap hb (us hu) bi (mem_filter.mp hu).2
  have uEven : U⊆evenOthers G b :=
    fun u hu => mem_even_others (ub u hu) (by simp [u2 u hu])
  have used := card_sdiff_add_card_eq_card uEven
  have emax := even_others_card (cap b)
  change E.card+U.card=_ at used
  change k≤U.card+t at near
  have ec : E.card≤t := by omega
  have debit := Graph189BoundaryDebit.even_quota connected cut.swap smaller cap us hb
  have hfilter : U.filter (fun u => Even (G.dist b u))=U :=
    filter_eq_self.mpr fun u hu => by simp [u2 u hu]
  rw [hfilter] at debit
  have ts := card_sdiff_add_card_eq_card (show Graph189PortLabels.support G S b⊆S from filter_subset _ _)
  change T.card+_=S.card at ts
  have tc : T.card≤t := by omega
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
  have incl : Y⊆F∪E∪evenOthers G i := by
    intro v hv
    by_cases port : G.Adj i v
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hv,port⟩))
    by_cases ve : v∈E
    · exact mem_union_left _ (mem_union_right _ ve)
    have vb' : v≠b := fun eq => port (eq ▸ bi.symm)
    have vi : v≠i := fun eq => disjoint_left.mp cut.right_cut (ys hv) (eq ▸ hi)
    have d := Graph189PrivateQuota.exact_two connected bi.symm (adjacent (ys hv) ve vb') vi.symm port
    exact mem_union_right _ (mem_even_others vi (by simp [d]))
  have full := (card_le_card incl).trans (card_union_le _ _)
  have two : (F∪E).card≤F.card+E.card := card_union_le _ _
  have remain := even_others_card (cap i)
  change Y.card≤k+F.card+t
  omega

#print axioms opposite_population
end Graph189AlmostFullColumn
