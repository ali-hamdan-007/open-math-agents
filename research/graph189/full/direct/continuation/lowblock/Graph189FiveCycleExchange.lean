import Mathlib.Data.Finset.Sort
import Graph189FourTerminalGap
import Graph189GapExchange

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleExchange
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b x y : V}

/-- In a path of at most eighteen vertices the three ordinary gaps
around two marks have at least two gaps of size five, so the interval
can be exchanged while protecting any selected old position. -/
theorem impossible (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length≤p.length)
    (q : G.Walk x y) (hq : q.IsPath) (outside : List.Disjoint q.support p.support)
    (length : q.support.length=5) (room : p.support.length≤18)
    (M : Finset (Fin p.support.length)) (two : M.card=2)
    (first : ∀ i : Fin p.support.length, G.Adj p.support[i.val] x ↔ i∈M)
    (last : ∀ i∈M, G.Adj p.support[i.val] y)
    (common : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val]∈r.support →
      q.support⊆r.support → r.length=p.length →
      ∀ c∈r.support, ∀ u∉r.support, ∀ w∉r.support, G.Adj c u → G.Adj c w)
    (cap : G.distEven x≤7) : False := by
  classical
  let A := M.orderEmbOfFin two
  let I := A 0
  let J := A 1
  have im : I∈M := M.orderEmbOfFin_mem two 0
  have jm : J∈M := M.orderEmbOfFin_mem two 1
  have lt : I<J := A.strictMono (show (0:Fin 2)<1 by decide)
  have pair : M={I,J} := by
    symm
    apply eq_of_subset_of_card_le (by simpa [insert_subset_iff] using And.intro im jm)
    rw [two,card_pair lt.ne]
  have backwards : List.Disjoint q.reverse.support p.support := by simpa [Walk.support_reverse] using outside
  have left := prefix_of_detour p hp mx I q.reverse hq.reverse backwards ((first I).mpr im).symm
  have middle := interval_of_detour p hp mx I J lt q hq outside ((first I).mpr im) (last J jm).symm
  have right := suffix_of_detour p hp mx J q.reverse hq.reverse backwards (last J jm)
  rw [Walk.support_reverse,List.length_reverse,length] at left right
  rw [length] at middle
  have choose : (I.val=5 ∧ I.val≤t.val) ∨
      (J.val=I.val+6 ∧ (t.val≤I.val ∨ J.val≤t.val)) ∨
      (p.support.length=J.val+6 ∧ t.val≤J.val) := by omega
  have gap : ∃ lo hi, lo<hi ∧ hi≤p.support.length ∧ hi-lo=5 ∧ (t.val<lo ∨ hi≤t.val) ∧
      (lo=0 ∨ ∃ i∈M,i.val+1=lo) ∧ (hi=p.support.length ∨ ∃ i∈M,i.val=hi) ∧
      (0<lo ∨ hi<p.support.length) ∧ ∀ j∈Ico lo hi, j≠I.val ∧ j≠J.val := by
    rcases choose with ⟨e,keep⟩|⟨e,keep⟩|⟨e,keep⟩
    · refine ⟨0,I.val,by omega,I.isLt.le,by omega,Or.inr keep,Or.inl rfl,Or.inr ⟨I,im,rfl⟩,Or.inr I.isLt,?_⟩
      intro j hj
      have := mem_Ico.mp hj
      omega
    · refine ⟨I.val+1,J.val,by omega,J.isLt.le,by omega,by omega,Or.inr ⟨I,im,rfl⟩,
        Or.inr ⟨J,jm,rfl⟩,Or.inl (by omega),?_⟩
      intro j hj
      have := mem_Ico.mp hj
      omega
    · refine ⟨J.val+1,p.support.length,by omega,le_rfl,by omega,Or.inl (by omega),
        Or.inr ⟨J,jm,rfl⟩,Or.inl rfl,Or.inl (by omega),?_⟩
      intro j hj
      have := mem_Ico.mp hj
      omega
  obtain ⟨lo,hi,ne,top,sz,safe,lb,ub,one,empty⟩ := gap
  have witnesses := interval_exchange_witnesses_with_route p hp t M q hq outside
    (fun i h => ⟨(first i).mpr h,last i h⟩) common ne top (sz.trans length.symm) safe lb ub one
  have marks : contactPositions p x={I.val,J.val} := by
    ext n
    constructor
    · intro h
      obtain ⟨hn,edge⟩ := (mem_contactPositions _ _ _).mp h
      have m := (first ⟨n,hn⟩).mp (by simpa only [get_at] using edge)
      simpa only [pair,mem_insert,mem_singleton,Fin.ext_iff] using m
    · intro h
      rcases mem_insert.mp h with e|e
      · subst n
        exact (mem_contactPositions _ _ _).mpr ⟨I.isLt,by simpa only [get_at] using (first I).mpr im⟩
      · obtain rfl := mem_singleton.mp e
        exact (mem_contactPositions _ _ _).mpr ⟨J.isLt,by simpa only [get_at] using (first J).mpr jm⟩
  exact Graph189FourTerminalGap.impossible_of_length p hp
    (List.disjoint_left.mp outside q.start_mem_support) (i:=I.val) (j:=J.val) (lo:=lo) (hi:=hi) (m:=5)
    (by omega) (by omega) (by omega)
    marks top (by rw [←sz,Nat.add_sub_of_le ne.le]) empty witnesses cap

#print axioms impossible
end Graph189FiveCycleExchange
