import Graph199BlockChain

namespace Graph199
open SimpleGraph Finset

/-- Insert an arbitrary finite family of mutually compatible path pieces
after an anchor. The first vertex is preserved, and the last vertex belongs
either to the anchor's possible ends or to a port of an inserted piece. -/
theorem append_indexed_blocks {V ι : Type*} [DecidableEq ι] {G : SimpleGraph V}
    (I : Finset ι) (U E : Set V) (carrier port : ι → Set V)
    (L : List V) (a b : V)
    (hhead : L.head? = some a) (hlast : L.getLast? = some b) (hb : b ∈ E)
    (hn : L.Nodup) (hc : L.IsChain G.Adj) (hm : ∀ x, x ∈ L ↔ x ∈ U)
    (pieces : ∀ i ∈ I, ∃ s ∈ port i, ∃ t ∈ port i, ∃ P : List V,
      P.head? = some s ∧ P.getLast? = some t ∧ P.Nodup ∧ P.IsChain G.Adj ∧
      (∀ x, x ∈ P ↔ x ∈ carrier i))
    (apart : ∀ i ∈ I, Disjoint U (carrier i))
    (separate : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (carrier i) (carrier j))
    (starts : ∀ i ∈ I, ∀ x ∈ E, ∀ y ∈ port i, G.Adj x y)
    (joins : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ x ∈ port i, ∀ y ∈ port j, G.Adj x y) :
    ∃ d : V, ∃ W : List V, (d ∈ E ∨ ∃ i ∈ I, d ∈ port i) ∧
      W.head? = some a ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔ x ∈ U ∨ ∃ i ∈ I, x ∈ carrier i) := by
  classical
  let good (J : Finset ι) := ∃ d : V, ∃ W : List V, (d ∈ E ∨ ∃ i ∈ J, d ∈ port i) ∧
      W.head? = some a ∧ W.getLast? = some d ∧ W.Nodup ∧ W.IsChain G.Adj ∧
      (∀ x, x ∈ W ↔ x ∈ U ∨ ∃ i ∈ J, x ∈ carrier i)
  have build (J : Finset ι) : J ⊆ I → good J := by
    induction J using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨b,L,Or.inl hb,hhead,hlast,hn,hc,fun x => by simpa using hm x⟩
    | @insert i J hi ih =>
      intro hsub
      have hiI := hsub (mem_insert_self i J)
      have hJI : J ⊆ I := fun j hj => hsub (mem_insert_of_mem hj)
      obtain ⟨e,Q,he,hQh,hQl,hQn,hQc,hQm⟩ := ih hJI
      obtain ⟨s,hs,t,ht,P,hPh,hPl,hPn,hPc,hPm⟩ := pieces i hiI
      have hQP : Q.Disjoint P := by
        intro x hx hx'
        have hxi := (hPm x).mp hx'
        rcases (hQm x).mp hx with hxU | ⟨j,hj,hxj⟩
        · exact Set.disjoint_left.mp (apart i hiI) hxU hxi
        · have hne : j ≠ i := fun h => hi (h ▸ hj)
          exact Set.disjoint_left.mp (separate j (hJI hj) i hiI hne) hxj hxi
      have hes : G.Adj e s := by
        rcases he with heE | ⟨j,hj,hej⟩
        · exact starts i hiI e heE s hs
        · exact joins j (hJI hj) i hiI (fun h => hi (h ▸ hj)) e hej s hs
      have hQne : Q ≠ [] := fun h => by simp [h] at hQh
      have hPne : P ≠ [] := fun h => by simp [h] at hPh
      refine ⟨t,Q ++ P,Or.inr ⟨i,mem_insert_self i J,ht⟩,?_,?_,?_,?_,?_⟩
      · rwa [List.head?_append_of_ne_nil _ hQne]
      · simp [List.getLast?_append, hPl]
      · exact List.nodup_append.mpr ⟨hQn,hPn,fun x hx y hy heq => hQP hx (heq ▸ hy)⟩
      · apply hQc.append hPc
        intro x hx y hy
        have he' : e = x := by simpa [hQl] using hx
        have hs' : s = y := by simpa [hPh] using hy
        exact he' ▸ hs' ▸ hes
      · intro x
        simp only [List.mem_append,hQm,hPm,Finset.mem_insert]
        aesop
  exact build I (fun _ h => h)

#print axioms append_indexed_blocks
end Graph199
