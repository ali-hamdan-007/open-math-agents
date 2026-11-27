import Graph199Independent

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

private theorem chain_join {L R : List V} {x y : V}
    (hL : L.IsChain G.Adj) (hR : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y) (hxy : G.Adj x y) :
    (L ++ R).IsChain G.Adj := by
  apply hL.append hR
  intro a ha b hb
  have he : x = a := by simpa [hx] using ha
  have he' : y = b := by simpa [hy] using hb
  exact he ▸ he' ▸ hxy

/-- A longest vertex list may be chosen by maximizing its length. -/
theorem exists_longest_chain [Fintype V] [Nonempty V] :
    ∃ L : List V, L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length := by
  classical
  let T : Set ℕ := {n | ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ l.length = n}
  have hf : T.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro _ ⟨l,hl,_,rfl⟩
    change l.length ≤ _
    simpa only [List.toFinset_card_of_nodup hl] using card_le_univ l.toFinset)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨n,⟨L,hn,hc,hlen⟩,hmax⟩ := hf.exists_maximal
    ⟨1,[x],by simp,List.IsChain.singleton x,rfl⟩
  refine ⟨L,?_,hn,hc,?_⟩
  · intro he
    have hh : n ≤ 1 → 1 ≤ n := hmax ⟨[x],by simp,List.IsChain.singleton x,rfl⟩
    simp [he] at hlen
    omega
  · intro Q hQn hQc
    have hh := hmax ⟨Q,hQn,hQc,rfl⟩
    omega

/-- Neither endpoint of a longest path has a neighbor off the path. -/
theorem longest_chain_endpoints {L : List V} (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    {x : V} (hx : x ∉ L) :
    (∀ a ∈ L.head?, ¬ G.Adj a x) ∧ (∀ a ∈ L.getLast?, ¬ G.Adj a x) := by
  constructor
  · intro a ha hax
    have h := hm (x :: L) (List.nodup_cons.mpr ⟨hx,hn⟩) (hc.cons (by
      intro b hb
      rw [ha] at hb
      have he : a = b := by simpa using hb
      exact he ▸ hax.symm))
    simp at h
  · intro a ha hax
    have hn' : (L ++ [x]).Nodup := by
      refine List.nodup_append.mpr ⟨hn,by simp,?_⟩
      intro y hy z hz
      have he : z = x := by simpa using hz
      exact fun h => hx ((h.trans he) ▸ hy)
    have hc' := chain_join hc (List.IsChain.singleton x)
      ha (by simp : ([x] : List V).head? = some x) hax
    have h := hm (L ++ [x]) hn' hc'
    simp at h

/-- The start of a longest path cannot see the successor of a vertex with an
off-path neighbor. -/
theorem longest_chain_head_misses_successor (P B : List V) (a x y c : V)
    (hhead : (P ++ x :: y :: B).head? = some a)
    (hn : (P ++ x :: y :: B).Nodup) (hc : (P ++ x :: y :: B).IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ (P ++ x :: y :: B).length)
    (hco : c ∉ P ++ x :: y :: B) (hxc : G.Adj x c) : ¬ G.Adj a y := by
  intro hay
  let A := P ++ [x]
  let D := y :: B
  have hsplit : A ++ D = P ++ x :: y :: B := by simp [A,D,List.append_assoc]
  have hAn : A.Nodup := (hsplit ▸ hn : (A ++ D).Nodup).of_append_left
  have hDn : D.Nodup := (hsplit ▸ hn : (A ++ D).Nodup).of_append_right
  have hAc : A.IsChain G.Adj := (hsplit ▸ hc : (A ++ D).IsChain G.Adj).left_of_append
  have hDc : D.IsChain G.Adj := (hsplit ▸ hc : (A ++ D).IsChain G.Adj).right_of_append
  have hAl : A.getLast? = some x := by simp [A]
  have hAh : A.head? = some a := by
    have hAne : A ≠ [] := by simp [A]
    rw [← List.head?_append_of_ne_nil _ hAne, hsplit, hhead]
  have hR : A.reverse.IsChain G.Adj :=
    List.isChain_reverse.mpr (hAc.imp fun _ _ h => h.symm)
  have hR' : (A.reverse ++ D).IsChain G.Adj :=
    chain_join hR hDc (by simpa using hAh) rfl hay
  have hc' : (c :: (A.reverse ++ D)).IsChain G.Adj := by
    apply hR'.cons
    intro z hz
    have hAne : A.reverse ≠ [] := by simp [A]
    rw [List.head?_append_of_ne_nil _ hAne, List.head?_reverse, hAl] at hz
    have he : x = z := by simpa using hz
    exact he ▸ hxc.symm
  have hn' : (A.reverse ++ D).Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr hAn,hDn,?_⟩
    intro u hu z hz
    exact (List.nodup_append.mp (hsplit ▸ hn : (A ++ D).Nodup)).2.2
      u (List.mem_reverse.mp hu) z hz
  have hcc : c ∉ A.reverse ++ D := by
    simpa only [List.mem_append,List.mem_reverse,hsplit.symm] using hco
  have hh := hm _ (List.nodup_cons.mpr ⟨hcc,hn'⟩) hc'
  rw [← hsplit] at hh
  simp at hh

/-- An off-path connecting path may replace any split into two consecutive
pieces, contradicting maximality. -/
theorem longest_chain_no_detour_gap {A D M : List V} {x y c d : V}
    (hAn : A.Nodup) (hDn : D.Nodup) (hMn : M.Nodup)
    (hAc : A.IsChain G.Adj) (hDc : D.IsChain G.Adj) (hMc : M.IsChain G.Adj)
    (hAD : A.Disjoint D) (hAM : A.Disjoint M) (hMD : M.Disjoint D)
    (hAl : A.getLast? = some x) (hDh : D.head? = some y)
    (hMh : M.head? = some c) (hMl : M.getLast? = some d)
    (hxc : G.Adj x c) (hdy : G.Adj d y)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ (A ++ D).length) : False := by
  have hAMn := hAn.append hMn hAM
  have hAMc := chain_join hAc hMc hAl hMh hxc
  have hAMl : (A ++ M).getLast? = some d := by simp [hMl]
  have hAMD : (A ++ M).Disjoint D := by
    intro z hz hz'
    exact (List.mem_append.mp hz).elim (fun h => hAD h hz') (fun h => hMD h hz')
  have h := hm ((A ++ M) ++ D) (hAMn.append hDn hAMD)
    (chain_join hAMc hDc hAMl hDh hdy)
  have hne : M ≠ [] := by intro he; simp [he] at hMh
  have hp : 0 < M.length := List.length_pos_iff.mpr hne
  simp only [List.length_append] at h
  omega

/-- The successors of two separated attachments cannot see each other. A
detour joins the attachments and the intervening piece is traversed backwards. -/
theorem longest_chain_no_detour_chord {A B D M : List V} {x y z t c d : V}
    (hA : A.getLast? = some x) (hB : B.head? = some y) (hB' : B.getLast? = some z)
    (hD : D.head? = some t) (hM : M.head? = some c) (hM' : M.getLast? = some d)
    (hn : ((A ++ B) ++ D).Nodup) (hc : ((A ++ B) ++ D).IsChain G.Adj)
    (hMn : M.Nodup) (hMc : M.IsChain G.Adj)
    (hdis : M.Disjoint ((A ++ B) ++ D)) (hxc : G.Adj x c) (hdz : G.Adj d z)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj →
      Q.length ≤ ((A ++ B) ++ D).length) : ¬ G.Adj y t := by
  intro hyt
  have hAc := hc.left_of_append.left_of_append
  have hBc := hc.left_of_append.right_of_append
  have hDc := hc.right_of_append
  have hR : B.reverse.IsChain G.Adj := List.isChain_reverse.mpr (hBc.imp fun _ _ h => h.symm)
  have hAMc := chain_join hAc hMc hA hM hxc
  have hAMl : (A ++ M).getLast? = some d := by simp [hM']
  have hARc := chain_join hAMc hR hAMl (by simpa using hB') hdz
  have hARl : ((A ++ M) ++ B.reverse).getLast? = some y := by simp [hB]
  have hnewc := chain_join hARc hDc hARl hD hyt
  have hperm : (((A ++ M) ++ B.reverse) ++ D).Perm (((A ++ B) ++ D) ++ M) := by
    calc
      (((A ++ M) ++ B.reverse) ++ D).Perm (((A ++ M) ++ B) ++ D) :=
        ((List.reverse_perm B).append_left (A ++ M)).append_right D
      _ = A ++ (M ++ (B ++ D)) := by simp [List.append_assoc]
      (A ++ (M ++ (B ++ D))).Perm (A ++ ((B ++ D) ++ M)) := (show (M ++ (B ++ D)).Perm ((B ++ D) ++ M) from List.perm_append_comm).append_left A
      _ = (((A ++ B) ++ D) ++ M) := by simp [List.append_assoc]
  have hnewn := hperm.nodup_iff.mpr (hn.append hMn hdis.symm)
  have h := hm _ hnewn hnewc
  have hne : M ≠ [] := by intro he; simp [he] at hM
  have hp : 0 < M.length := List.length_pos_iff.mpr hne
  simp only [List.length_append,List.length_reverse] at h
  omega

#print axioms exists_longest_chain
#print axioms longest_chain_endpoints
#print axioms longest_chain_head_misses_successor
#print axioms longest_chain_no_detour_gap
#print axioms longest_chain_no_detour_chord
end Graph199
