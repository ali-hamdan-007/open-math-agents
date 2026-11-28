import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace Graph189RootedPath
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {z u : V}

private theorem bound_list {v : V} (P : G.Walk z v)
    (longest : ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length)
    (L : List V) (h : L.head? = some z) (hc : L.IsChain G.Adj) (hn : L.Nodup) :
    L.length ≤ P.support.length := by
  have ne : L ≠ [] := by rintro rfl; simp at h
  have he : L.head ne = z := by simpa [List.head?_eq_some_head ne] using h
  subst z
  let Q := Walk.ofSupport L ne hc
  have qs : Q.support = L := Walk.support_ofSupport _ _
  have qp : Q.IsPath := Walk.IsPath.mk' (qs.symm ▸ hn)
  have le := longest Q qp
  have ql := Q.length_support
  rw [qs] at ql
  have pl := P.length_support
  omega

private def pos (L : List V) (i : ℕ) (d : V) : V := L[i]?.getD d

private theorem pos_eq (L : List V) (i : ℕ) (hi : i < L.length) (d : V) : pos L i d = L[i] := by
  simp [pos,List.getElem?_eq_getElem hi]

private theorem take_last (L : List V) (i : ℕ) (hi : i < L.length) (d : V) :
    (L.take (i+1)).getLast? = some (pos L i d) := by
  rw [List.getLast?_take, pos_eq _ _ hi _]
  simp [List.getElem?_eq_getElem hi]

private theorem drop_head (L : List V) (i : ℕ) (hi : i < L.length) (d : V) :
    (L.drop i).head? = some (pos L i d) := by
  rw [List.head?_drop, pos_eq _ _ hi _, List.getElem?_eq_getElem hi]

private theorem bridge {A B : List V} {a b : V} (ca : A.IsChain G.Adj) (cb : B.IsChain G.Adj)
    (ha : A.getLast? = some a) (hb : B.head? = some b) (e : G.Adj a b) :
    (A ++ B).IsChain G.Adj := by
  apply ca.append cb
  simpa [ha,hb] using e

private theorem insert_chain {L : List V} (hL : L.IsChain G.Adj) (i : ℕ) (hi : i < L.length)
    (X : List V) (x y : V) (hX : X.IsChain G.Adj) (hx : X.head? = some x)
    (hy : X.getLast? = some y) (d : V) (left : G.Adj (pos L i d) x)
    (right : i+1 < L.length → G.Adj y (pos L (i+1) d)) :
    ((L.take (i+1) ++ X) ++ L.drop (i+1)).IsChain G.Adj := by
  have pre := bridge (hL.take _) hX (take_last L i hi d) hx left
  apply pre.append (hL.drop _)
  intro a ha b hb
  have last : (L.take (i+1) ++ X).getLast? = some y := by simp [List.getLast?_append,hy]
  rw [last] at ha
  have eq : a = y := by simpa using ha.symm
  subst a
  by_cases hs : i+1 < L.length
  · rw [drop_head L _ hs d] at hb
    have eq : b = pos L (i+1) d := by simpa using hb.symm
    exact eq ▸ right hs
  · have emp : L.drop (i+1) = [] := by simp [List.drop_eq_nil_iff.mpr (by omega : L.length ≤ i+1)]
    simp [emp] at hb

private theorem forbid_insert {L : List V} (head : L.head? = some z) (chain : L.IsChain G.Adj)
    (nodup : L.Nodup) (maximal : ∀ K : List V, K.head? = some z → K.IsChain G.Adj → K.Nodup → K.length ≤ L.length)
    (i : ℕ) (hi : i < L.length) (X : List V) (x y : V) (hX : X.IsChain G.Adj)
    (hx : X.head? = some x) (hy : X.getLast? = some y) (hn : X.Nodup) (dis : X.Disjoint L)
    (left : G.Adj (pos L i z) x) (right : i+1 < L.length → G.Adj y (pos L (i+1) z)) : False := by
  let A := L.take (i+1)
  let B := L.drop (i+1)
  have split : A ++ B = L := List.take_append_drop _ _
  have perm : ((A ++ X) ++ B).Perm (X ++ L) := by
    rw [← split, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  have n := perm.nodup_iff.mpr (List.nodup_append'.mpr ⟨hn,nodup,dis⟩)
  have hd : ((A ++ X) ++ B).head? = some z := by simp [A,List.head?_append,List.head?_take,head]
  have le := maximal _ hd (insert_chain chain i hi X x y hX hx hy z left right) n
  have equal := perm.length_eq
  have nx : 0 < X.length := by cases X <;> simp_all
  rw [equal] at le
  simp only [List.length_append] at le
  omega

private theorem forbid_cross {L : List V} (head : L.head? = some z) (chain : L.IsChain G.Adj)
    (nodup : L.Nodup) (maximal : ∀ K : List V, K.head? = some z → K.IsChain G.Adj → K.Nodup → K.length ≤ L.length)
    (outside : u ∉ L) (i j : ℕ) (hij : i < j) (hj : j+1 < L.length)
    (left : G.Adj (pos L i z) u) (mid : G.Adj u (pos L j z))
    (chord : G.Adj (pos L (i+1) z) (pos L (j+1) z)) : False := by
  let A := L.take (i+1)
  let B := (L.take (j+1)).drop (i+1)
  let C := L.drop (j+1)
  have ab : A ++ B = L.take (j+1) := by
    have h := List.take_append_drop (i+1) (L.take (j+1))
    simpa [A,B,List.take_take,Nat.min_eq_left (by omega : i+1 ≤ j+1)] using h
  have split : (A ++ B) ++ C = L := by rw [ab]; exact List.take_append_drop _ _
  have blen : (L.take (j+1)).length = j+1 := by simp [Nat.min_eq_left (by omega : j+1 ≤ L.length)]
  have bst : B.head? = some (pos L (i+1) z) := by
    simp [B,List.head?_drop,show i+1 < j+1 by omega,
      List.getElem?_eq_getElem (by omega : i+1 < L.length),pos_eq _ _ (by omega : i+1 < L.length) _]
  have ben : B.getLast? = some (pos L j z) := by
    dsimp only [B]
    rw [List.getLast?_drop,if_neg (by rw [blen]; omega)]
    exact take_last L _ (by omega) _
  have br := List.isChain_reverse.mpr (((chain.take (j+1)).drop (i+1)).imp fun _ _ h => h.symm)
  have c1 := bridge (chain.take (i+1)) (List.isChain_singleton u) (take_last L i (by omega) z) (by simp) left
  have c2 : ((A ++ [u]) ++ B.reverse).IsChain G.Adj := by
    apply bridge c1 br (a := u) (b := pos L j z) (by simp) (by simpa using ben) mid
  have c3 : (((A ++ [u]) ++ B.reverse) ++ C).IsChain G.Adj := by
    apply bridge c2 (chain.drop _) (a := pos L (i+1) z) (b := pos L (j+1) z) _ (drop_head L _ hj z) chord
    rw [List.getLast?_append,List.getLast?_reverse,bst]
    rfl
  have p1 : ((A ++ [u]) ++ B.reverse).Perm ([u] ++ (A ++ B)) := by
    exact (List.perm_append_comm.append_right B.reverse).trans
      ((B.reverse_perm.append_left ([u] ++ A)).trans (by simp))
  have perm : (((A ++ [u]) ++ B.reverse) ++ C).Perm (u :: L) := by
    rw [← split]; simpa [List.append_assoc] using p1.append_right C
  have n := perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨outside,nodup⟩)
  have hd : (((A ++ [u]) ++ B.reverse) ++ C).head? = some z := by simp [A,List.head?_append,List.head?_take,head]
  have le := maximal _ hd c3 n
  have equal := perm.length_eq
  rw [equal] at le
  simp only [List.length_cons] at le
  omega

/-- Contacts and their oriented successors along a longest path with prescribed start. -/
theorem successors_of_rooted_longest {v : V} (P : G.Walk z v) (hp : P.IsPath)
    (longest : ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length)
    (outside : u ∉ P.support) (touches : ∃ w ∈ P.support, G.Adj u w) :
    ∃ (W : Finset V) (succ : V → V), W.Nonempty ∧ Set.InjOn succ (↑W : Set V) ∧
      (∀ w ∈ W, G.Adj u w) ∧ (∀ w ∈ W, succ w ≠ u ∧ ¬G.Adj u (succ w)) ∧
      (∀ a ∈ W, ∀ b ∈ W, ¬G.Adj (succ a) (succ b)) ∧
      (∀ w ∈ W, ∀ y, G.Adj u y → G.Adj (succ w) y → y ∈ W) ∧
      (∀ w ∈ W, G.Adj w (succ w) ∧ succ w ≠ z) ∧ u ≠ z := by
  classical
  let L := P.support
  have head : L.head? = some z := by cases P <;> rfl
  have chain : L.IsChain G.Adj := P.isChain_adj_support
  have nodup : L.Nodup := hp.support_nodup
  have maximal := bound_list P longest
  let W := L.toFinset.filter (G.Adj u)
  have memW (w : V) : w ∈ W ↔ w ∈ L ∧ G.Adj u w := by simp [W]
  let idx (w : V) := L.idxOf w
  have at_idx (w : V) (hw : w ∈ L) : ∃ h : idx w < L.length, L[idx w] = w := by
    have hi := List.idxOf_lt_length_iff.mpr hw
    exact ⟨hi,List.getElem_idxOf hi⟩
  have at_w (w : V) (hw : w ∈ W) : pos L (idx w) z = w := by
    obtain ⟨hi,eq⟩ := at_idx w ((memW w).mp hw).1
    exact (pos_eq _ _ hi _).trans eq
  have next_lt (w : V) (hw : w ∈ W) : idx w + 1 < L.length := by
    by_contra hn
    obtain ⟨hi,_⟩ := at_idx w ((memW w).mp hw).1
    exact forbid_insert head chain nodup maximal (idx w) hi [u] u u (by simp) (by simp) (by simp)
      (by simp) (by simpa using outside) (by rw [at_w w hw]; exact ((memW w).mp hw).2.symm) (fun h => (hn h).elim)
  let succ (w : V) := pos L (idx w+1) z
  have succmem (w : V) (hw : w ∈ W) : succ w ∈ L := by
    change pos L (idx w+1) z ∈ L
    rw [pos_eq _ _ (next_lt w hw) _]; exact List.getElem_mem _
  have noedge (w : V) (hw : w ∈ W) : ¬G.Adj u (succ w) := by
    intro e
    have hi := next_lt w hw
    exact forbid_insert head chain nodup maximal (idx w) (by omega) [u] u u (by simp) (by simp)
      (by simp) (by simp) (by simpa using outside)
      (by rw [at_w w hw]; exact ((memW w).mp hw).2.symm) (fun _ => e)
  have same (a b : V) (ha : a ∈ W) (hb : b ∈ W) (h : idx a = idx b) : a = b :=
    (at_w a ha).symm.trans ((congrArg (fun i => pos L i z) h).trans (at_w b hb))
  have no_cross (a b : V) (ha : a ∈ W) (hb : b ∈ W) (h : idx a < idx b) : ¬G.Adj (succ a) (succ b) := by
    intro e
    apply forbid_cross head chain nodup maximal outside (idx a) (idx b) h (next_lt b hb) _ _ e
    · rw [at_w a ha]; exact ((memW a).mp ha).2.symm
    · rw [at_w b hb]; exact ((memW b).mp hb).2
  obtain ⟨w₀,hw₀,e₀⟩ := touches
  refine ⟨W,succ,⟨w₀,(memW _).mpr ⟨hw₀,e₀⟩⟩,?_,fun w hw => ((memW w).mp hw).2,
    fun w hw => ⟨fun he => outside (he ▸ succmem w hw),noedge w hw⟩,?_,?_,?_,?_⟩
  · intro a ha b hb he
    change pos L (idx a+1) z = pos L (idx b+1) z at he
    rw [pos_eq _ _ (next_lt a ha) _,pos_eq _ _ (next_lt b hb) _] at he
    have h := nodup.getElem_inj_iff.mp he
    exact same a b ha hb (by omega)
  · intro a ha b hb e
    rcases lt_trichotomy (idx a) (idx b) with h | h | h
    · exact no_cross a b ha hb h e
    · have eq := same a b ha hb h
      subst b
      exact e.ne rfl
    · exact no_cross b a hb ha h e.symm
  · intro w hw y uy sy
    apply (memW _).mpr
    refine ⟨?_,uy⟩
    by_contra hy
    have hi := next_lt w hw
    apply forbid_insert head chain nodup maximal (idx w) (by omega) [u,y] u y
      (by simpa using uy) (by simp) (by simp) (by simp [uy.ne]) _ _ (fun _ => sy.symm)
    · simpa [List.disjoint_cons_left,hy] using (show u ∉ L from outside)
    · rw [at_w w hw]; exact ((memW w).mp hw).2.symm
  · intro w hw
    have hn := next_lt w hw
    have hi : idx w < L.length := by omega
    have gadj : G.Adj (pos L (idx w) z) (pos L (idx w+1) z) := by
      rw [pos_eq _ _ hi _,pos_eq _ _ hn _]
      exact chain.getElem _ hn
    refine ⟨?_,?_⟩
    · rw [at_w w hw] at gadj
      exact gadj
    · intro he
      have h0 : 0 < L.length := by omega
      have hz : pos L 0 z = z := by
        have eq := drop_head L 0 h0 z
        simpa [head] using eq.symm
      change pos L (idx w+1) z = z at he
      rw [← hz,pos_eq _ _ hn _,pos_eq _ _ h0 _] at he
      have eq := nodup.getElem_inj_iff.mp he
      omega
  · intro h
    apply outside
    rw [h]
    exact P.start_mem_support

/-- A longest path starting at the prescribed vertex exists in every finite graph. -/
theorem exists_rooted_longest [Fintype V] (G : SimpleGraph V) (z : V) :
    ∃ (v : V) (P : G.Walk z v), P.IsPath ∧
      ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length := by
  classical
  let Good (m : ℕ) := ∃ (v : V) (P : G.Walk z v), P.IsPath ∧ P.length = m
  have base : Good 0 := ⟨z,.nil,by simp,rfl⟩
  obtain ⟨v,P,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨v,P,hp,?_⟩
  intro b Q hQ
  rw [hlen]
  have card := hQ.support_nodup.length_le_card
  have size := Q.length_support
  exact Nat.le_findGreatest (by omega) (show Good Q.length from ⟨b,Q,hQ,rfl⟩)

/-- Connectivity supplies an omitted vertex that touches any nonspanning rooted path. -/
theorem exists_exterior_contact {v : V} (P : G.Walk z v) (connected : G.Connected)
    (missing : ∃ x, x ∉ P.support) : ∃ u ∉ P.support, ∃ w ∈ P.support, G.Adj u w := by
  obtain ⟨x,hx⟩ := missing
  obtain ⟨R⟩ := connected z x
  obtain ⟨d,_,hin,hout⟩ := R.exists_boundary_dart {y | y ∈ P.support} P.start_mem_support hx
  exact ⟨d.snd,hout,d.fst,hin,d.adj.symm⟩

#print axioms exists_rooted_longest
#print axioms exists_exterior_contact
#print axioms successors_of_rooted_longest
end Graph189RootedPath
