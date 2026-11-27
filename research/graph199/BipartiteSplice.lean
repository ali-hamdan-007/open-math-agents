import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.List.Nodup

namespace BalancedBipartite

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- A cyclic spanning vertex order. The degree-sum theorem uses this only for
orders at least four. It is also convenient when deleting one auxiliary vertex. -/
def HasSpanningCycle (G : SimpleGraph V) : Prop :=
  ∃ (l : List V) (a b : V), l.Nodup ∧ (∀ z : V, z ∈ l) ∧
    l.IsChain G.Adj ∧ l.head? = some a ∧ l.getLast? = some b ∧ G.Adj b a

theorem join_chain {L R : List V} {a b : V} (hl : L.IsChain G.Adj)
    (hr : R.IsChain G.Adj) (ha : L.getLast? = some a) (hb : R.head? = some b)
    (hab : G.Adj a b) : (L ++ R).IsChain G.Adj := by
  apply hl.append hr
  intro x hx y hy
  have hax : a = x := by simpa [ha] using hx
  have hby : b = y := by simpa [hb] using hy
  exact hax ▸ hby ▸ hab

theorem reverse_chain {l : List V} (hc : l.IsChain G.Adj) : l.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (hc.imp fun _ _ hh => hh.symm)

theorem pair_at (l : List V) (i : ℕ) (hi : i+1 < l.length) :
    ∃ P Q, l = P ++ l[i]'(by omega) :: l[i+1] :: Q := by
  refine ⟨l.take i, l.drop (i+2), ?_⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega : i < l.length), List.drop_eq_getElem_cons hi]

theorem alternating_color {col : V → Bool} (hcol : ∀ ⦃a b⦄, G.Adj a b → col a ≠ col b)
    {l : List V} {x : V} (hc : l.IsChain G.Adj) (hx : l.head? = some x)
    (i : ℕ) (hi : i < l.length) :
    col l[i] = if i % 2 = 0 then col x else !(col x) := by
  induction i with
  | zero =>
    have hne : l ≠ [] := by
      intro he
      simp [he] at hx
    have h0 : l[0] = x := by
      rw [← List.head_eq_getElem hne]
      exact List.head_of_head?_eq_some hx
    simp [h0]
  | succ i ih =>
    have hprev := ih (by omega)
    have hne := hcol (List.isChain_iff_getElem.mp hc i (by omega : i+1<l.length))
    by_cases he : i%2=0
    · have ho : (i+1)%2 ≠ 0 := by omega
      simp only [he, if_true] at hprev
      simp only [show i.succ%2 ≠ 0 from ho, if_false]
      rw [hprev] at hne
      cases h₁ : col x <;> cases h₂ : col l[i+1] <;> simp_all
    · have ho : (i+1)%2 = 0 := by omega
      simp only [he, if_false] at hprev
      simp only [show i.succ%2=0 from ho, if_true]
      rw [hprev] at hne
      cases h₁ : col x <;> cases h₂ : col l[i+1] <;> simp_all

private theorem color_eq_of_ne {a b c : Bool} (hab : a ≠ b) (hcb : c ≠ b) :
    c = a := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Close a spanning alternating path when its opposite-color endpoints
have total degree greater than the number of pairs along the path. -/
theorem cycle_of_spanning_path [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {col : V → Bool} (hcol : ∀ ⦃a b⦄, G.Adj a b → col a ≠ col b)
    {r : ℕ} {l : List V} {x y : V} (hlen : l.length = 2*r)
    (hn : l.Nodup) (hcover : ∀ z : V, z ∈ l) (hc : l.IsChain G.Adj)
    (hx : l.head? = some x) (hy : l.getLast? = some y) (hxy : col x ≠ col y)
    (hdeg : r+1 ≤ G.degree x + G.degree y) : HasSpanningCycle G := by
  classical
  let left (i : Fin r) : V := l[2*i.val]'(by have := i.isLt; omega)
  let right (i : Fin r) : V := l[2*i.val+1]'(by have := i.isLt; omega)
  let S : Finset (Fin r) := univ.filter fun i => G.Adj x (right i)
  let T : Finset (Fin r) := univ.filter fun i => G.Adj y (left i)
  have hS : G.degree x ≤ S.card := by
    have hsub : G.neighborFinset x ⊆ S.image right := by
      intro z hz
      have hzAdj := (G.mem_neighborFinset x z).mp hz
      obtain ⟨j,hj,hjz⟩ := List.getElem_of_mem (hcover z)
      have hcj := alternating_color hcol hc hx j hj
      rw [hjz] at hcj
      have hjOdd : j%2=1 := by
        by_contra! hbad
        have he : j%2=0 := by omega
        exact hcol hzAdj (by simpa only [he,if_true] using hcj.symm)
      let i : Fin r := ⟨j/2,by omega⟩
      have hr : right i = z := by
        have e : 2*(j/2)+1=j := by omega
        unfold right i
        simpa only [e] using hjz
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hr.symm ▸ hzAdj⟩,hr⟩
    exact (card_le_card hsub).trans card_image_le
  have hT : G.degree y ≤ T.card := by
    have hsub : G.neighborFinset y ⊆ T.image left := by
      intro z hz
      have hzAdj := (G.mem_neighborFinset y z).mp hz
      obtain ⟨j,hj,hjz⟩ := List.getElem_of_mem (hcover z)
      have hcj := alternating_color hcol hc hx j hj
      rw [hjz] at hcj
      have hxz : col z = col x := color_eq_of_ne hxy (hcol hzAdj).symm
      have hjEven : j%2=0 := by
        by_contra! hbad
        rw [if_neg hbad,hxz] at hcj
        have hbool : col x ≠ !(col x) := by
          cases col x <;> decide
        exact hbool hcj
      let i : Fin r := ⟨j/2,by omega⟩
      have hl : left i = z := by
        have e : 2*(j/2)=j := by omega
        unfold left i
        simpa only [e] using hjz
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hl.symm ▸ hzAdj⟩,hl⟩
    exact (card_le_card hsub).trans card_image_le
  obtain ⟨i,hiS,hiT⟩ : ∃ i, i ∈ S ∧ i ∈ T := by
    by_contra! h
    have hdis : Disjoint S T := disjoint_left.mpr h
    have hs := card_union_of_disjoint hdis
    have hb : (S∪T).card ≤ r := by simpa using card_le_univ (S∪T)
    omega
  have hxr : G.Adj x (right i) := (mem_filter.mp hiS).2
  have hyl : G.Adj y (left i) := (mem_filter.mp hiT).2
  obtain ⟨P,Q,hsplit⟩ := pair_at l (2*i.val) (by have := i.isLt; omega)
  change l = P ++ left i :: right i :: Q at hsplit
  let L := P ++ [left i]
  let R := right i :: Q
  have he : l = L ++ R := by simpa [L,R,List.append_assoc] using hsplit
  have hL : L.IsChain G.Adj := (he ▸ hc).left_of_append
  have hR : R.IsChain G.Adj := (he ▸ hc).right_of_append
  have hLne : L ≠ [] := by simp [L]
  have hRne : R ≠ [] := by simp [R]
  have hLn : L.head? = some x := by rwa [he,List.head?_append_of_ne_nil _ hLne] at hx
  have hRn : R.getLast? = some y := by rwa [he,List.getLast?_append_of_ne_nil _ hRne] at hy
  have hp : (L ++ R.reverse).Perm l := by
    rw [he]
    exact (List.reverse_perm R).append_left L
  refine ⟨L ++ R.reverse,x,right i,hp.nodup_iff.mpr hn,fun z => hp.mem_iff.mpr (hcover z),?_,?_,?_,hxr.symm⟩
  · have hlast : L.getLast? = some (left i) := by simp [L]
    have hhead : R.reverse.head? = some y := by rwa [List.head?_reverse]
    exact join_chain hL (reverse_chain hR) hlast hhead hyl.symm
  · rwa [List.head?_append_of_ne_nil _ hLne]
  · rw [List.getLast?_append_of_ne_nil _ (by simp [hRne]),List.getLast?_reverse]
    simp [R]

theorem HasSpanningCycle.traceable [DecidableEq V] (h : HasSpanningCycle G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨l,a,b,hn,hall,hc,ha,_,_⟩ := h
  have hne : l ≠ [] := fun he => by simp [he] at ha
  let p := Walk.ofSupport l hne hc
  have hs : p.support = l := Walk.support_ofSupport hne hc
  exact ⟨_, _, p, (Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun z => by
    rw [hs]
    exact hall z)⟩

#print axioms cycle_of_spanning_path
#print axioms HasSpanningCycle.traceable

end BalancedBipartite
