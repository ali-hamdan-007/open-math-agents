import Graph199H1Bridge
import Graph199BlockChain
import Graph199Prefix
import Graph199Middle

namespace Graph199
open SimpleGraph Finset

universe u
variable {V : Type u} {G : SimpleGraph V}
  {v w : V} {A B : Set V}

private def Dangling (D : H1FarData G v w A) (i : Fin D.n) : Prop :=
  ∃ a, D.near i = {a}

private theorem choose_dangling_cases (D : H1FarData G v w A) :
    (∀ i, ¬ Dangling D i) ∨
    (∃ i, Dangling D i ∧ ∀ j, j ≠ i → ¬ Dangling D j) ∨
    (∃ i j, i ≠ j ∧ Dangling D i ∧ Dangling D j ∧
      ∀ k, k ≠ i → k ≠ j → ¬ Dangling D k) := by
  classical
  by_cases h : ∃ i, Dangling D i
  · obtain ⟨i, hi⟩ := h
    by_cases h' : ∃ j, j ≠ i ∧ Dangling D j
    · obtain ⟨j, hji, hj⟩ := h'
      refine Or.inr (Or.inr ⟨i,j,hji.symm,hi,hj,?_⟩)
      intro k hki hkj hk
      have hlt : 2 < {l | ∃ a, D.near l = {a}}.ncard :=
        (Set.two_lt_ncard_iff (s := {l | ∃ a, D.near l = {a}})).mpr
          ⟨i,j,k,hi,hj,hk,hji.symm,hki.symm,hkj.symm⟩
      exact (not_lt_of_ge D.at_most_two_singleton) hlt
    · exact Or.inr (Or.inl ⟨i,hi,fun j hji hj => h' ⟨j,hji,hj⟩⟩)
  · exact Or.inl (fun i hi => h ⟨i,hi⟩)

private def Core (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) : Set V :=
  if short then D.near i else D.near i ∪ D.far i

private def InitialFar (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) : Set V :=
  if short then D.far i else ∅

private def Middle (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) : Set V :=
  (D.spare ∪ Core D i short) ∪ {x | ∃ j ∈ I, x ∈ D.near j ∪ D.far j}

private def MiddlePorts (D : H1FarData G v w A) (i : Fin D.n) (I : Finset (Fin D.n)) : Set V :=
  (D.spare ∪ D.near i) ∪ {x | ∃ j ∈ I, x ∈ D.near j}

private theorem core_sub (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) :
    Core D i short ⊆ D.near i ∪ D.far i := by
  cases short <;> simp [Core]

private theorem initial_sub (D : H1FarData G v w A) (i : Fin D.n) (short : Bool) :
    InitialFar D i short ⊆ D.far i := by
  cases short <;> simp [InitialFar]

private theorem near_far_disjoint (D : H1FarData G v w A) (i j : Fin D.n) :
    Disjoint (D.near i) (D.far j) := by
  rw [Set.disjoint_left]
  exact fun x hx hy => (D.far_facts j x hy).2 (D.near_facts i x hx).2

private theorem block_disjoint (D : H1FarData G v w A) {i j : Fin D.n} (hij : i ≠ j) :
    Disjoint (D.near i ∪ D.far i) (D.near j ∪ D.far j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact D.near_disjoint hij hx hy
  · exact Set.disjoint_left.mp (near_far_disjoint D i j) hx hy
  · exact Set.disjoint_left.mp (near_far_disjoint D j i) hy hx
  · exact (D.far_separated hij hx hy).1 rfl

private theorem spare_block_disjoint (D : H1FarData G v w A) (i : Fin D.n) :
    Disjoint D.spare (D.near i ∪ D.far i) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hy with hy | hy
  · exact D.spare_disjoint i x hx hy
  · exact (D.far_facts i x hy).2 (D.spare_facts x hx).2

private theorem block_subset (D : H1FarData G v w A) (i : Fin D.n) :
    D.near i ∪ D.far i ⊆ A := by
  intro x hx
  exact hx.elim (fun h => (D.near_facts i x h).1) (fun h => (D.far_facts i x h).1)

private theorem middle_subset (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) :
    Middle D i short I ⊆ A := by
  intro x hx
  rcases hx with (hx | hx) | ⟨j,_,hx⟩
  · exact (D.spare_facts x hx).1
  · exact block_subset D i (core_sub D i short hx)
  · exact block_subset D j hx

private theorem initial_middle_disjoint (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) (hI : i ∉ I) :
    Disjoint (InitialFar D i short) (Middle D i short I) := by
  cases short with
  | false => simp [InitialFar]
  | true =>
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x ∈ D.far i := initial_sub D i true hx
    rcases hy with (hy | hy) | ⟨j,hj,hy⟩
    · exact Set.disjoint_left.mp (spare_block_disjoint D i) hy (Or.inr hx')
    · exact Set.disjoint_left.mp (near_far_disjoint D i i) (by simpa [Core] using hy) hx'
    · have hij : i ≠ j := fun he => hI (he.symm ▸ hj)
      exact Set.disjoint_left.mp (block_disjoint D hij) (Or.inr hx') hy

private theorem middle_terminal_disjoint (D : H1FarData G v w A) (i j : Fin D.n)
    (short : Bool) (I : Finset (Fin D.n)) (hij : i ≠ j) (hjI : j ∉ I) :
    Disjoint (Middle D i short I) (D.near j ∪ D.far j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with (hx | hx) | ⟨k,hk,hx⟩
  · exact Set.disjoint_left.mp (spare_block_disjoint D j) hx hy
  · exact Set.disjoint_left.mp (block_disjoint D hij) (core_sub D i short hx) hy
  · have hkj : k ≠ j := fun he => hjI (he ▸ hk)
    exact Set.disjoint_left.mp (block_disjoint D hkj) hx hy

private theorem initial_core_cover (D : H1FarData G v w A) (i : Fin D.n)
    (short : Bool) {x : V} (hx : x ∈ D.near i ∪ D.far i) :
    x ∈ InitialFar D i short ∨ x ∈ Core D i short := by
  cases short <;> simpa [InitialFar, Core, or_comm] using hx

private theorem cuts_disjoint_A (houtA : v ∉ A ∧ w ∉ A)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y) :
    Disjoint (insert w (insert v B)) A := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [Set.mem_insert_iff] at hx
  rcases hx with rfl | rfl | hx
  · exact houtA.2 hy
  · exact houtA.1 hy
  · exact hsep x hy x hx rfl

private theorem list_disjoint_of_support {L R : List V} {S T : Set V}
    (hL : ∀ x, x ∈ L ↔ x ∈ S) (hR : ∀ x, x ∈ R ↔ x ∈ T)
    (hST : Disjoint S T) : L.Disjoint R :=
  fun x hx hy => Set.disjoint_left.mp hST ((hL x).mp hx) ((hR x).mp hy)

variable [Fintype V]

private theorem prefix_exists (D : H1FarData G v w A) (i : Fin D.n) (short : Bool)
    (hshort : short = true → Dangling D i)
    (hvw : v ≠ w) (houtA : v ∉ A ∧ w ∉ A) (houtB : v ∉ B ∧ w ∉ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y)
    (hB : B.Nonempty) (hcl : G.IsClique B) (hvb : ∀ x ∈ B, G.Adj v x ∧ G.Adj w x) :
    ∃ L : List V, L ≠ [] ∧ L.getLast? = some v ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ x, x ∈ L ↔ x ∈ InitialFar D i short ∪ insert w (insert v B)) := by
  cases short with
  | false =>
    obtain ⟨L,hh,ht,hn,hc,hm⟩ := clique_bridge w v hvw.symm houtB.2 houtB.1 hB hcl
      (fun x h => (hvb x h).2) (fun x h => (hvb x h).1)
    have hne : L ≠ [] := by intro he; simp [he] at hh
    exact ⟨L,hne,ht,hn,hc,by simpa [InitialFar] using hm⟩
  | true =>
    obtain ⟨a,ha⟩ := hshort rfl
    obtain ⟨x,hx,hxw⟩ := D.singleton_hooks i a ha
    have hTw : w ∉ D.far i := fun h => houtA.2 (D.far_facts i w h).1
    have hTv : v ∉ D.far i := fun h => houtA.1 (D.far_facts i v h).1
    have hTB : Disjoint (D.far i) B := Set.disjoint_left.mpr
      (fun x hx hy => hsep x (D.far_facts i x hx).1 x hy rfl)
    simpa [InitialFar] using clique_prefix_bridge w v hvw.symm houtB.2 houtB.1 hB hcl
      (fun x h => (hvb x h).2) (fun x h => (hvb x h).1) hx (D.far_clique i) hTw hTv hTB hxw.symm

private theorem terminal_exists (D : H1FarData G v w A) (j : Fin D.n)
    (hj : Dangling D j) :
    ∃ a ∈ D.near j, ∃ L : List V, L.head? = some a ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      (∀ x, x ∈ L ↔ x ∈ D.near j ∪ D.far j) := by
  obtain ⟨a,ha⟩ := hj
  have ha' : a ∈ D.near j := by simp [ha]
  obtain ⟨x,hx⟩ := D.far_nonempty j
  obtain ⟨L,hh,hn,hc,hm⟩ := clique_list_starting hx (D.far_clique j)
  have hn' : a ∉ L := fun h => Set.disjoint_left.mp (near_far_disjoint D j j) ha' ((hm a).mp h)
  refine ⟨a,ha',a::L,rfl, List.nodup_cons.mpr ⟨hn',hn⟩, ?_, ?_⟩
  · cases L with
    | nil => simp
    | cons y ys =>
      apply List.isChain_cons_cons.mpr
      exact ⟨D.same_attachment_complete j a y ha' ((hm y).mp (by simp)), hc⟩
  · intro y
    simp [hm,ha]

private theorem finish_from_middle [DecidableEq V]
    (D : H1FarData G v w A) (i : Fin D.n) (short : Bool)
    (I : Finset (Fin D.n)) (terminal : Option (Fin D.n))
    (hshort : short = true → Dangling D i)
    (hiI : i ∉ I) (hit : terminal ≠ some i)
    (hrest : ∀ j, j ≠ i → j ∉ I → terminal = some j)
    (hterm : ∀ j, terminal = some j → j ∉ I ∧ Dangling D j)
    (hvw : v ≠ w) (houtA : v ∉ A ∧ w ∉ A) (houtB : v ∉ B ∧ w ∉ B)
    (hcover : ∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y)
    (hB : B.Nonempty) (hcl : G.IsClique B) (hvb : ∀ x ∈ B, G.Adj v x ∧ G.Adj w x)
    (hM : ∃ a ∈ D.spare ∪ D.near i, ∃ d : V, ∃ W : List V,
      d ∈ MiddlePorts D i I ∧ W.head? = some a ∧ W.getLast? = some d ∧
      W.Nodup ∧ W.IsChain G.Adj ∧ (∀ x, x ∈ W ↔ x ∈ Middle D i short I)) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  let _ : Nonempty V := ⟨v⟩
  obtain ⟨P,hPne,hPt,hPn,hPc,hPm⟩ :=
    prefix_exists D i short hshort hvw houtA houtB hsep hB hcl hvb
  obtain ⟨a,ha,d,W,hd,hWh,hWt,hWn,hWc,hWm⟩ := hM
  have hWne : W ≠ [] := by intro he; simp [he] at hWh
  have hcuts := cuts_disjoint_A houtA hsep
  have hpw : P.Disjoint W := by
    apply list_disjoint_of_support hPm hWm
    rw [Set.disjoint_left]
    intro x hx hy
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp (initial_middle_disjoint D i short I hiI) hx hy
    · exact Set.disjoint_left.mp hcuts hx (middle_subset D i short I hy)
  have startAdj : G.Adj v a := ha.elim
    (fun h => (D.spare_facts a h).2) (fun h => (D.near_facts i a h).2)
  have linkPW : ∀ a' ∈ P.getLast?, ∀ b' ∈ W.head?, G.Adj a' b' := by
    intro x hx y hy
    have hxv : v = x := by simpa [hPt] using hx
    have hya : a = y := by simpa [hWh] using hy
    exact hxv ▸ hya ▸ startAdj
  have allCovered (x : V) :
      x ∈ P ∨ x ∈ W ∨ ∃ j, terminal = some j ∧ x ∈ D.near j ∪ D.far j := by
    by_cases hxv : x = v
    · exact Or.inl ((hPm x).2 (Or.inr (by simp [hxv])))
    by_cases hxw : x = w
    · exact Or.inl ((hPm x).2 (Or.inr (by simp [hxw])))
    rcases hcover x hxv hxw with hx | hx
    · rcases D.blocks_cover x hx with hs | ⟨j,hj⟩
      · exact Or.inr (Or.inl ((hWm x).2 (Or.inl (Or.inl hs))))
      · have hblock : x ∈ D.near j ∪ D.far j := hj.symm
        by_cases hji : j = i
        · subst j
          rcases initial_core_cover D i short hblock with hp | hm
          · exact Or.inl ((hPm x).2 (Or.inl hp))
          · exact Or.inr (Or.inl ((hWm x).2 (Or.inl (Or.inr hm))))
        · by_cases hjI : j ∈ I
          · exact Or.inr (Or.inl ((hWm x).2 (Or.inr ⟨j,hjI,hblock⟩)))
          · exact Or.inr (Or.inr ⟨j,hrest j hji hjI,hblock⟩)
    · exact Or.inl ((hPm x).2 (Or.inr (by simp [hx])))
  cases terminal with
  | none =>
    refine hamiltonian_of_ordered_blocks [P,W] ?_ ?_ ?_ ?_
    · intro L hL
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
      rcases hL with rfl | rfl
      · exact ⟨hPne,hPn,hPc⟩
      · exact ⟨hWne,hWn,hWc⟩
    · simp [hpw]
    · intro x
      rcases allCovered x with hx | hx | ⟨j,hj,_⟩
      · exact ⟨P,by simp,hx⟩
      · exact ⟨W,by simp,hx⟩
      · cases hj
    · exact List.isChain_cons_cons.mpr ⟨linkPW, by simp⟩
  | some j =>
    have hij : i ≠ j := fun h => hit (congrArg some h.symm)
    obtain ⟨hjI,hj⟩ := hterm j rfl
    obtain ⟨b,hb,T,hTh,hTn,hTc,hTm⟩ := terminal_exists D j hj
    have hTne : T ≠ [] := by intro he; simp [he] at hTh
    have hpt : P.Disjoint T := by
      apply list_disjoint_of_support hPm hTm
      rw [Set.disjoint_left]
      intro x hx hy
      rcases hx with hx | hx
      · exact Set.disjoint_left.mp (block_disjoint D hij)
          (Or.inr (initial_sub D i short hx)) hy
      · exact Set.disjoint_left.mp hcuts hx (block_subset D j hy)
    have hwt : W.Disjoint T :=
      list_disjoint_of_support hWm hTm (middle_terminal_disjoint D i j short I hij hjI)
    have endAdj : G.Adj d b := by
      rcases hd with (hs | hs) | ⟨k,hk,hs⟩
      · exact D.spare_attachment_complete j d b hs hb
      · exact D.cross_attachment_complete hij hs hb
      · have hkj : k ≠ j := fun he => hjI (he ▸ hk)
        exact D.cross_attachment_complete hkj hs hb
    have linkWT : ∀ a' ∈ W.getLast?, ∀ b' ∈ T.head?, G.Adj a' b' := by
      intro x hx y hy
      have hxd : d = x := by simpa [hWt] using hx
      have hyb : b = y := by simpa [hTh] using hy
      exact hxd ▸ hyb ▸ endAdj
    refine hamiltonian_of_ordered_blocks [P,W,T] ?_ ?_ ?_ ?_
    · intro L hL
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
      rcases hL with rfl | rfl | rfl
      · exact ⟨hPne,hPn,hPc⟩
      · exact ⟨hWne,hWn,hWc⟩
      · exact ⟨hTne,hTn,hTc⟩
    · simp [hpw,hpt,hwt]
    · intro x
      rcases allCovered x with hx | hx | ⟨k,hk,hx⟩
      · exact ⟨P,by simp,hx⟩
      · exact ⟨W,by simp,hx⟩
      · have he : j = k := Option.some.inj hk
        exact ⟨T,by simp,(hTm x).2 (he.symm ▸ hx)⟩
    · exact List.isChain_cons_cons.mpr ⟨linkPW, List.isChain_cons_cons.mpr ⟨linkWT, by simp⟩⟩

/-- Assemble the prefix, covered middle, and possible terminal dangling block. -/
theorem hamiltonian_of_h1FarData [DecidableEq V]
    (G : SimpleGraph V) (v w : V) (A B : Set V) (hvw : v ≠ w)
    (houtA : v ∉ A ∧ w ∉ A) (houtB : v ∉ B ∧ w ∉ B)
    (hcover : ∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, x ≠ y)
    (hB : B.Nonempty) (hcl : G.IsClique B)
    (hvb : ∀ x ∈ B, G.Adj v x ∧ G.Adj w x)
    (D : H1FarData G v w A) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  have assemble (i : Fin D.n) (short : Bool) (terminal : Option (Fin D.n))
      (hcore : if short then Dangling D i else ¬ Dangling D i)
      (hit : terminal ≠ some i) (hterm : ∀ j, terminal = some j → Dangling D j)
      (hregular : ∀ j, j ≠ i → terminal ≠ some j → ¬ Dangling D j) :
      ∃ x y : V, ∃ p : G.Walk x y, p.IsHamiltonian := by
    let I := (univ : Finset (Fin D.n)).filter fun j => j ≠ i ∧ terminal ≠ some j
    have hmem (j : Fin D.n) : j ∈ I ↔ j ≠ i ∧ terminal ≠ some j := by simp [I]
    have hI (j : Fin D.n) (hj : j ∈ I) : j ≠ i ∧ ¬ Dangling D j :=
      let hh := (hmem j).mp hj
      ⟨hh.1,hregular j hh.1 hh.2⟩
    have hiI : i ∉ I := fun hi => ((hmem i).mp hi).1 rfl
    have hrest (j : Fin D.n) (hji : j ≠ i) (hjI : j ∉ I) : terminal = some j := by
      by_contra hn
      exact hjI ((hmem j).mpr ⟨hji,hn⟩)
    have hterm' (j : Fin D.n) (hj : terminal = some j) : j ∉ I ∧ Dangling D j :=
      ⟨fun hin => ((hmem j).mp hin).2 hj,hterm j hj⟩
    have hshort (h : short = true) : Dangling D i := by simpa [h] using hcore
    have hM := middle_of_far_data D i I hI short hcore
    have hM' : ∃ a ∈ D.spare ∪ D.near i, ∃ d : V, ∃ W : List V,
        d ∈ MiddlePorts D i I ∧ W.head? = some a ∧ W.getLast? = some d ∧
        W.Nodup ∧ W.IsChain G.Adj ∧ (∀ x, x ∈ W ↔ x ∈ Middle D i short I) := hM
    exact finish_from_middle D i short I terminal hshort hiI hit hrest hterm'
      hvw houtA houtB hcover hsep hB hcl hvb hM'
  rcases choose_dangling_cases D with hnone | ⟨i,hi,honly⟩ | ⟨i,j,hij,hi,hj,honly⟩
  · exact assemble ⟨0,D.positive⟩ false none (hnone _) (by simp)
      (by simp) (fun j _ _ => hnone j)
  · exact assemble i true none hi (by simp) (by simp) (fun j hji _ => honly j hji)
  · refine assemble i true (some j) hi (by simpa using hij.symm) ?_ ?_
    · intro k hk
      obtain rfl := Option.some.inj hk
      exact hj
    · intro k hki hkj
      exact honly k hki (fun h => hkj (congrArg some h.symm))

theorem h1_two_component_step : TwoComponentStep.{u} :=
  two_component_step_of_far_data hamiltonian_of_h1FarData

#print axioms h1_two_component_step
end Graph199
