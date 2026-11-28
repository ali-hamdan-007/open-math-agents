import Graph189TwoProtectedGaps
import Graph189FullExteriorExchange

open Finset SimpleGraph Graph189ExteriorGap Graph189ContactGroupCensus
namespace Graph189RootedSplice
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

theorem two_full_gaps_on_protected_path (p : G.Walk x y) (hp : p.IsPath)
    (root : V) (t : Fin p.support.length) (index : p.getVert t.val=root)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → root∈r.support → r.length≤p.length)
    (E : Finset V) (m u : ℕ) (size : E.card=m) (two : 2≤u) (balanced : u≤m)
    (outside : ∀ v∈E, v∉p.support) (a b : E) (ne : a≠b)
    (routes : ∀ i j : E, i≠j → ∃ h : (G.induce (E : Set V)).Walk i j, h.IsHamiltonian)
    (uniform : ∀ v∈p.support, G.Adj v a.val → G.Adj v b.val)
    (marks : (contactPositions p a.val).card=u) (room : p.support.length+m+2≤(u+1)*(m+1)+u) :
    ∃ I J : TightGap p a.val m, List.Disjoint I.block J.block ∧ root∉I.block ∧ root∉J.block := by
  classical
  let z := a.val
  have marksPositive : 1≤(contactPositions p z).card := by dsimp [z]; omega
  let A := contactPositions p z
  let d := A.card
  let L := p.support.length
  let mark : Fin d ↪o ℕ := A.orderEmbOfFin rfl
  have real (i : Fin d) : mark i<L ∧ G.Adj (p.getVert (mark i)) z :=
    (mem_contactPositions p z _).mp (A.orderEmbOfFin_mem rfl i)
  let f : ℕ → ℕ
    | 0 => 0
    | j+1 => if h : j<d then mark ⟨j,h⟩+1 else L+1
  let hi (i : Fin (d+1)) := if h : i.val<d then mark ⟨i.val,h⟩ else L
  have successor (i : Fin (d+1)) : f (i.val+1)=hi i+1 := by
    by_cases h : i.val<d <;> simp [f,hi,h]
  have endBound (i : Fin (d+1)) : hi i≤L := by
    dsimp [hi]
    split <;> rename_i h
    · exact (real ⟨i.val,h⟩).1.le
    · rfl
  have loBound (i : Fin (d+1)) : f i.val≤hi i := by
    rcases i with ⟨i,ir⟩
    cases i with
    | zero => simp [f]
    | succ j =>
      have jd : j<d := by omega
      change f (j+1) ≤ if t : j+1<d then mark ⟨j+1,t⟩ else L
      simp only [f,dif_pos jd]
      split <;> rename_i h
      · exact mark.strictMono (show (⟨j,jd⟩ : Fin d) < ⟨j+1,h⟩ by exact Nat.lt_succ_self j)
      · exact (real ⟨j,jd⟩).1
  have before (i : Fin (d+1)) (positive : 0<f i.val) : G.Adj (p.getVert (f i.val-1)) z := by
    rcases i with ⟨i,ir⟩
    cases i with
    | zero => simp [f] at positive
    | succ j =>
      have jd : j<d := by omega
      simpa [f,jd] using (real ⟨j,jd⟩).2
  have after (i : Fin (d+1)) (below : hi i<L) : G.Adj z (p.getVert (hi i)) := by
    by_cases h : i.val<d
    · simpa [hi,h] using (real ⟨i.val,h⟩).2.symm
    · simp [hi,h] at below
  have oneBound (i : Fin (d+1)) : 0<f i.val ∨ hi i<L := by
    rcases i with ⟨i,ir⟩
    cases i with
    | zero =>
      have h : 0<d := marksPositive
      exact Or.inr (by simpa [hi,h] using (real ⟨0,h⟩).1)
    | succ j =>
      have jd : j<d := by omega
      exact Or.inl (by simp [f,jd])
  have silent (i : Fin (d+1)) (t : ℕ) (lt : f i.val≤t) (tr : t<hi i) : ¬G.Adj z (p.getVert t) := by
    intro edge
    have trange : t<p.support.length := tr.trans_le (endBound i)
    have tin : t∈A := (mem_contactPositions p z t).mpr ⟨trange,edge.symm⟩
    let iso := A.orderIsoOfFin (show A.card=d from rfl)
    let pos : Fin d := iso.symm ⟨t,tin⟩
    have value : mark pos=t := congrArg Subtype.val (iso.apply_symm_apply ⟨t,tin⟩)
    by_cases less : pos.val < i.val
    · rcases i with ⟨iv,ir⟩
      cases iv with
      | zero => exact (Nat.not_lt_zero _ less).elim
      | succ j =>
        have jd : j<d := by omega
        have le : pos≤(⟨j,jd⟩ : Fin d) := by change pos.val≤j; exact Nat.le_of_lt_succ less
        have bound := mark.monotone le
        change f (j+1)≤t at lt
        rw [show f (j+1)=mark ⟨j,jd⟩+1 by simp [f,jd]] at lt
        omega
    · have iRange : i.val<d := by have := pos.isLt; omega
      have le : (⟨i.val,iRange⟩ : Fin d) ≤ pos := by change i.val≤pos.val; omega
      have mono := mark.monotone le
      rw [show hi i=mark ⟨i.val,iRange⟩ by simp [hi,iRange]] at tr
      omega
  have dEqual : d=u := marks
  have fStrict (i j : ℕ) (ij : i<j) (endj : j≤d+1) : f i<f j := by
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [f]
        split <;> omega
      | succ i =>
        have id : i<d := by omega
        simp only [f,dif_pos id]
        split <;> rename_i h
        · have order := mark.strictMono (show (⟨i,id⟩ : Fin d)<⟨j,h⟩ by change i<j; omega)
          omega
        · have limit := (real ⟨i,id⟩).1
          omega
  have insideRoot : root∈p.support := by
    rw [←index,←get_at p t.isLt]
    exact List.getElem_mem _
  have keeps (i : Fin (d+1)) (safe : t.val<f i.val ∨ f (i.val+1)≤t.val+1) :
      root∉pathSegment p (f i.val) (hi i) := by
    intro hit
    obtain ⟨j,lo,up,value⟩ := (segment_member p (endBound i) root).mp hit
    have same := hp.getVert_injOn (show j∈{i | i≤p.length} by
      have := endBound i; have := p.length_support; change j≤p.length; omega)
      (show t.val∈{i | i≤p.length} by have := p.length_support; have := t.isLt; change t.val≤p.length; omega)
      (value.trans index.symm)
    rw [successor] at safe
    omega
  have full (i : Fin (d+1)) (safe : t.val<f i.val ∨ f (i.val+1)≤t.val+1) :
      m≤f (i.val+1)-f i.val-1 := by
    obtain ⟨lc,rc⟩ := coordinate_neighbors p z _ _ (loBound i) (endBound i) (before i) (after i)
    obtain ⟨c,v,r,hr,on,sz,_,_⟩ := full_exterior_splice p hp root insideRoot E m size outside
      a b ne routes uniform _ _ _ (by rw [pathSegment,←List.take_add,Nat.add_sub_of_le (loBound i),List.take_append_drop]) (keeps i safe) lc rc
    have atMost := longest r hr on
    have rp := r.length_support
    have pp := p.length_support
    have seg := segment_size p (lo:=f i.val) (endBound i)
    rw [successor]
    omega
  have last : f (d+1)=L+1 := by simp [f]
  obtain ⟨i,j,lt,limit,si,sj,ti,tj⟩ := two_swappable_intervals f t.val rfl last fStrict
    (by omega : d≤m) (by simpa [L,dEqual] using room)
    (fun h eh safe => full ⟨h,by omega⟩ safe)
  let I : Fin (d+1) := ⟨i,by omega⟩
  let J : Fin (d+1) := ⟨j,by omega⟩
  have construct (g : Fin (d+1)) (tight : f (g.val+1)-f g.val-1=m) :
      ∃ A : TightGap p z m, A.block=pathSegment p (f g.val) (hi g) := by
    rw [successor] at tight
    have lower := loBound g
    have positive : 0<m := by omega
    have eq : hi g-f g.val=m := by omega
    obtain ⟨A,hA⟩ := gap_from_coordinates p z (by omega : f g.val<hi g) (endBound g)
      (before g) (after g) (oneBound g) (silent g)
    exact eq ▸ ⟨A,hA⟩
  obtain ⟨X,hX⟩ := construct I ti
  obtain ⟨Y,hY⟩ := construct J tj
  refine ⟨X,Y,?_,by rw [hX]; exact keeps I si,by rw [hY]; exact keeps J sj⟩
  rw [hX,hY]
  apply disjoint_segments p hp (endBound I) (endBound J)
  have beforeJ : f (I.val+1)≤f J.val := by
    rcases eq_or_lt_of_le (show i+1≤j by omega) with eq|less
    · change f (i+1)≤f j
      rw [eq]
    · exact (fStrict _ _ less (by omega)).le
  rw [successor] at beforeJ
  omega

#print axioms two_full_gaps_on_protected_path

end Graph189RootedSplice
