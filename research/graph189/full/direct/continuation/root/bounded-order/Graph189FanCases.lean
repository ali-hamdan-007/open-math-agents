import Graph189FanCycle
import Graph189FanCrossing
import Graph189FanRegions

open SimpleGraph Finset
namespace Graph189FanCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a graph with at most one low vertex, either a longest path already
closes to the required cycle, or its two high ends have separated regions
with every neighbour contained in the corresponding region. -/
theorem cycle_or_regions (low : V) {q : ℕ} (dq : 2≤q) (dz : 2≤G.degree low)
    (conn : G.Preconnected) (high : ∀ u, u≠low → q≤G.degree u) :
    (∃ a, ∃ C : G.Walk a a, C.IsCycle ∧ min (Fintype.card V) (2*q) ≤ C.length) ∨
    ∃ x y, q≤G.degree x ∧ q≤G.degree y ∧ Nonempty (Regions G x y) := by
  classical
  obtain ⟨l,nd,ch,three,h0,h1,mx⟩ := longest_high_ends low dz
  have ne : l≠[] := by rintro rfl; simp at three
  let x := l.head ne
  let y := l.getLast ne
  have lh : l.head?=some x := List.head?_eq_some_head ne
  have lt : l.getLast?=some y := List.getLast?_eq_some_getLast ne
  have dx := high x (fun e => h0 (lh.trans (congrArg some e)))
  have dy := high y (fun e => h1 (lt.trans (congrArg some e)))
  let S := leftMarks (G:=G) l x
  let T := rightMarks (G:=G) l x y
  obtain ⟨cs,ct⟩ := endpoint_marks ne nd ch mx
  change G.degree x ≤ S.card at cs
  change G.degree y ≤ T.card at ct
  have sm (i : ℕ) (h : i∈S) : i+1<l.length ∧ G.Adj x (l.getD (i+1) x) := by
    obtain ⟨hr,e⟩ := mem_filter.mp h
    have := mem_range.mp hr
    exact ⟨by omega,e⟩
  have tm (i : ℕ) (h : i∈T) : i+1<l.length ∧ G.Adj (l.getD i x) y := by
    obtain ⟨hr,e⟩ := mem_filter.mp h
    have := mem_range.mp hr
    exact ⟨by omega,e⟩
  by_cases meet : ∃ j∈S,j∈T
  · obtain ⟨j,js,jt⟩ := meet
    obtain ⟨a,C,hC⟩ := spanning_of_common_mark ne nd ch three mx conn js jt
    exact Or.inl ⟨a,C,hC.isCycle,(min_le_left _ _).trans_eq hC.length_eq.symm⟩
  have dis : Disjoint S T := disjoint_left.mpr (fun j js jt => meet ⟨j,js,jt⟩)
  by_cases cross : ∃i∈T,∃j∈S,i<j
  · obtain ⟨a,C,hC,c⟩ := crossing_cycle ne nd ch S T sm tm dis cross (by omega)
    exact Or.inl ⟨a,C,hC,(min_le_right _ _).trans (by omega)⟩
  right
  have sn : S.Nonempty := card_pos.mp (by omega)
  have tn : T.Nonempty := card_pos.mp (by omega)
  let r := S.max' sn+1
  let s := T.min' tn
  have rm : S.max' sn∈S := max'_mem _ _
  have sm' : s∈T := min'_mem _ _
  have rs : r≤s := by
    by_contra! lt
    have n : s ≤ S.max' sn := by dsimp [r] at lt; omega
    rcases n.eq_or_lt with eq|strict
    · exact meet ⟨_,rm,eq ▸ sm'⟩
    exact cross ⟨_,sm',_,rm,strict⟩
  have first : l.getD 0 x=x := by cases l with | nil => contradiction | cons a b => rfl
  have last : l.getD (l.length-1) x=y := by rw [List.getD_eq_getElem _ _ (by omega),←List.getLast_eq_getElem]
  have startOn (v : V) (e : G.Adj x v) : v∈l := by
    by_contra outside
    have ext := mx (v::l) (List.nodup_cons.mpr ⟨outside,nd⟩) (List.IsChain.cons_of_ne_nil ne ch e.symm)
    simp at ext
  have stopOn (v : V) (e : G.Adj y v) : v∈l := by
    by_contra outside
    have nd' : (l++[v]).Nodup := by
      refine List.nodup_append.mpr ⟨nd,List.nodup_singleton _,?_⟩
      intro a ha b hb
      simp at hb
      subst b
      rintro rfl
      exact outside ha
    have ch' : (l++[v]).IsChain G.Adj := by
      refine List.isChain_append.mpr ⟨ch,List.isChain_singleton _,?_⟩
      intro a ha b hb
      rw [lt] at ha
      simp at ha hb
      subst a b
      exact e
    have ext := mx _ nd' ch'
    simp at ext
  refine ⟨x,y,dx,dy,regions_of_indices nd ch ne rfl rfl rs (by have := (tm _ sm').1; omega)
    (sm _ rm).2 (tm _ sm').2.symm ?_ ?_⟩
  · intro v e
    obtain ⟨i,il,iv⟩ := List.getElem_of_mem (startOn v e)
    have val : l.getD i x=v := (List.getD_eq_getElem _ _ il).trans iv
    have pos : i≠0 := by rintro rfl; exact e.ne (first.symm.trans val)
    have mark : i-1∈S := by
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (by omega),by rwa [show i-1+1=i by omega,val]⟩
    have bound := le_max' S _ mark
    exact ⟨i,by dsimp [r]; omega,val⟩
  · intro v e
    obtain ⟨i,il,iv⟩ := List.getElem_of_mem (stopOn v e)
    have val : l.getD i x=v := (List.getD_eq_getElem _ _ il).trans iv
    have room : i≠l.length-1 := by rintro rfl; exact e.ne (last.symm.trans val)
    have mark : i∈T := mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [val]; exact e.symm⟩
    exact ⟨i,min'_le T _ mark,il,val⟩

end Graph189FanCycle
#print axioms Graph189FanCycle.cycle_or_regions
