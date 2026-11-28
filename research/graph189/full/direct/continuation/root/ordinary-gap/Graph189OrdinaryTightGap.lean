import Graph189FullGapPositions
open Finset SimpleGraph Graph189ExteriorGap Graph189ContactGroupCensus Graph189RootedSplice
namespace Graph189OrdinaryPathGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- On an ordinary longest path, the quadratic path-room bound forces a tight interval.
Its endpoints are returned as coordinates for counting shifted marks outside it. -/
theorem find_tight_interval (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length≤p.length)
    (E : Finset V) (m u : ℕ) (size : E.card=m) (two : 2≤u) (positive : 0<m)
    (outside : ∀ v∈E, v∉p.support) (a b : E) (ne : a≠b)
    (routes : ∀ i j : E, i≠j → ∃ h : (G.induce (E : Set V)).Walk i j, h.IsHamiltonian)
    (uniform : ∀ v∈p.support, G.Adj v a.val → G.Adj v b.val)
    (marks : (contactPositions p a.val).card=u) (room : p.support.length≤(u+1)*m+2*u) :
    ∃ lo hi : ℕ, lo+m=hi ∧ hi≤p.support.length ∧
      ∃ J : TightGap p a.val m, J.block=pathSegment p lo hi := by
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
  let first : Fin d := ⟨0,by omega⟩
  let root := p.getVert (mark first)
  have insideRoot : root∈p.support := p.getVert_mem_support _
  have safe (i : Fin (d+1)) : root∉pathSegment p (f i.val) (hi i) := by
    intro hit
    obtain ⟨j,lo,up,value⟩ := (segment_member p (endBound i) root).mp hit
    exact silent i j lo up (value ▸ (real first).2.symm)
  have full (i : Fin (d+1)) : m≤hi i-f i.val := by
    obtain ⟨lc,rc⟩ := coordinate_neighbors p z _ _ (loBound i) (endBound i) (before i) (after i)
    obtain ⟨c,v,r,hr,_,sz,_,_⟩ := full_exterior_splice p hp root insideRoot E m size outside
      a b ne routes uniform _ _ _ (by rw [pathSegment,←List.take_add,Nat.add_sub_of_le (loBound i),List.take_append_drop]) (safe i) lc rc
    have atMost := longest r hr
    have rp := r.length_support
    have pp := p.length_support
    have seg := segment_size p (lo:=f i.val) (endBound i)
    omega
  obtain ⟨i,tight⟩ : ∃ i : Fin (d+1), hi i-f i.val=m := by
    by_contra! fail
    have counts := width_sum f d rfl fStrict
    rw [show f (d+1)=L+1 by simp [f]] at counts
    have upper := sum_le_sum (s:=range (d+1)) (f:=fun _ => m+1)
      (g:=fun i => f (i+1)-f i-1) (fun j hj => by
        let i : Fin (d+1) := ⟨j,mem_range.mp hj⟩
        have bound := full i
        have diff := fail i
        have step := successor i
        change f (j+1)=hi i+1 at step
        change m+1≤f (j+1)-f i.val-1
        omega)
    simp only [sum_const,card_range,Nat.nsmul_eq_mul] at upper
    change L≤(u+1)*m+2*u at room
    rw [dEqual] at counts upper
    nlinarith
  have low := loBound i
  have pos : f i.val<hi i := by omega
  obtain ⟨J,hJ⟩ := gap_from_coordinates p z pos (endBound i)
    (before i) (after i) (oneBound i) (silent i)
  exact ⟨f i.val,hi i,by omega,endBound i,tight ▸ ⟨J,hJ⟩⟩

#print axioms find_tight_interval
end Graph189OrdinaryPathGap
