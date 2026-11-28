import Graph189OrdinaryShiftPositions
import Graph189FullExteriorExchange
import Graph189OrdinaryContactRows

open Finset SimpleGraph Graph189ExteriorGap Graph189RootedSplice
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189OrdinaryPathGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}

/-- Shifted contacts cover 2u vertices. Every inner high position of the tight gap
adds a distinct distance-two vertex. At most one such position can be low. -/
theorem tight_gap_debit (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (off : a∉p.support) {m u lo hi : ℕ}
    (large : 3≤m) (width : lo+m=hi) (bound : hi≤p.support.length)
    (marks : (contactPositions p a).card=u)
    (wide : ∀ i∈contactPositions p a, ∀ j∈contactPositions p a, i<j → i+3≤j)
    (gap : TightGap p a m) (coords : gap.block=pathSegment p lo hi)
    (hits : ∀ v∈gap.block, G.secondSmallestDegree≤G.degree v → G.dist a v=2)
    (budget : (univ.filter (fun v => G.dist a v=2)).card≤G.secondSmallestDegree) :
    2*u+m≤G.secondSmallestDegree+3 := by
  classical
  let A := contactPositions p a
  let W := A.image (fun i => i+1) ∪ A.image (fun i => i-1)
  obtain ⟨sz,valid⟩ := double_shift_positions p hp longest off wide
  change W.card=2*A.card at sz
  have wc : W.card=2*u := sz.trans (congrArg (2*·) marks)
  let I := Ico (lo+1) (hi-1)
  let H := I.filter fun i => G.secondSmallestDegree≤G.degree (p.getVert i)
  let L := I.filter fun i => ¬G.secondSmallestDegree≤G.degree (p.getVert i)
  have inside {i} (h : i∈I) : lo < i ∧ i+1 < hi := by
    obtain ⟨lower,upper⟩ := mem_Ico.mp h
    omega
  have member {i} (lower : lo ≤ i) (upper : i < hi) : p.getVert i∈gap.block := by
    rw [coords]
    exact (segment_member p bound _).mpr ⟨i,lower,upper,rfl⟩
  have ls := p.length_support
  have low : L.card≤1 := card_le_one_iff.mpr (by
    intro i j ai aj
    obtain ⟨ri,ni⟩ := mem_filter.mp ai
    obtain ⟨rj,nj⟩ := mem_filter.mp aj
    by_contra diff
    have ir := (inside ri).2
    have jr := (inside rj).2
    have ne : p.getVert i≠p.getVert j := fun eq => diff (hp.getVert_injOn
      (by change i≤p.length; omega) (by change j≤p.length; omega) eq)
    exact (degree_pair (G:=G) _ _ ne).elim ni nj)
  have census : H.card+L.card=I.card := card_filter_add_card_filter_not (fun i => G.secondSmallestDegree≤G.degree (p.getVert i))
  have ic : I.card=hi-1-(lo+1) := Nat.card_Ico _ _
  have separate : Disjoint W H := by
    apply Finset.disjoint_left.mpr
    intro i wi ih
    obtain ⟨lt,gt⟩ := inside (mem_filter.mp ih).1
    rcases mem_union.mp wi with plus | minus
    · obtain ⟨j,hj,id⟩ := mem_image.mp plus
      change j+1=i at id
      exact gap.unmarked _ (member (by omega : lo ≤ j) (by omega : j<hi))
        ((mem_contactPositions p a _).mp hj).2.symm
    · obtain ⟨j,hj,id⟩ := mem_image.mp minus
      change j-1=i at id
      exact gap.unmarked _ (member (by omega : lo ≤ j) (by omega : j<hi))
        ((mem_contactPositions p a _).mp hj).2.symm
  have validBoth (i) (h : i∈W∪H) : i<p.support.length ∧ G.dist a (p.getVert i)=2 := by
    rcases mem_union.mp h with w | high
    · exact valid i w
    · obtain ⟨ii,degree⟩ := mem_filter.mp high
      obtain ⟨lt,gt⟩ := inside ii
      exact ⟨by omega,hits _ (member (by omega : lo ≤ i) (by omega : i < hi)) degree⟩
  have inclusion : (W∪H).image p.getVert ⊆ univ.filter (fun v => G.dist a v=2) := by
    intro v hv
    obtain ⟨i,h,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨mem_univ _,(validBoth i h).2⟩
  have total := (card_le_card inclusion).trans budget
  have inj : Set.InjOn p.getVert ((W∪H : Finset ℕ) : Set ℕ) := by
    intro i h j t eq
    have first := (validBoth i h).1
    have second := (validBoth j t).1
    exact hp.getVert_injOn (by change i≤p.length; omega) (by change j≤p.length; omega) eq
  rw [card_image_of_injOn inj,card_union_of_disjoint separate,wc] at total
  omega

#print axioms tight_gap_debit
end Graph189OrdinaryPathGap
