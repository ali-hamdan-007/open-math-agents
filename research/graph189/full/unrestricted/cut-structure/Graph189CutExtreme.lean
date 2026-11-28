module

public import Graph189CutMiddle
import all Graph189CutMiddle
import all Graph189CutCore

public section
namespace Graph189CutExtreme
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

-- Equal-size alternating-chain construction from OMA Graph 189 R1, also
-- used in the earlier bipartite branch of the conjecture.
/-- Alternate between equally sized sets of vertices, starting at an additional
vertex with a neighbor in the first set if that set is nonempty. -/
theorem alternating_chain (left right : Finset V) (z : V)
    (hcard : left.card = right.card)
    (hdisj : ∀ x ∈ left, x ∉ right)
    (hzl : z ∉ left) (hzr : z ∉ right)
    (hcross : ∀ y ∈ right, ∀ x ∈ left, G.Adj y x)
    (hstart : left.Nonempty → ∃ x ∈ left, G.Adj z x) :
    ∃ L : List V, L.head? = some z ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ b, b ∈ L ↔ b = z ∨ b ∈ left ∨ b ∈ right := by
  by_cases hn : left.Nonempty
  · obtain ⟨x,hxl,hzx⟩ := hstart hn
    have hright : right.Nonempty := Finset.card_pos.mp (hcard ▸ Finset.card_pos.mpr hn)
    obtain ⟨y,hyr⟩ := hright
    have hyl : y ∉ left := fun hy => hdisj y hy hyr
    have hyx : G.Adj y x := hcross y hyr x hxl
    have hc' : (left.erase x).card = (right.erase y).card := by
      rw [Finset.card_erase_of_mem hxl, Finset.card_erase_of_mem hyr, hcard]
    obtain ⟨L,hhead,hnodup,hchain,hcover⟩ :=
      alternating_chain (left.erase x) (right.erase y) y hc'
        (fun b hb hr => hdisj b (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hr))
        (fun he => hyl (Finset.mem_of_mem_erase he)) (Finset.notMem_erase _ _)
        (fun b hb a ha => hcross b (Finset.mem_of_mem_erase hb) a (Finset.mem_of_mem_erase ha))
        (fun hempty => let ⟨a,ha⟩ := hempty
                       ⟨a,ha,hcross y hyr a (Finset.mem_of_mem_erase ha)⟩)
    have hxy : x ≠ y := fun e => hyl (e ▸ hxl)
    have hxright := hdisj x hxl
    have hxnot : x ∉ L := by
      rw [hcover]
      simp [hxy, hxright]
    have hzxne : z ≠ x := fun e => hzl (e.symm ▸ hxl)
    have hzyne : z ≠ y := fun e => hzr (e.symm ▸ hyr)
    have hznot : z ∉ L := by rw [hcover]; simp [hzyne, hzl, hzr]
    have hchain' : (x :: L).IsChain G.Adj := hchain.cons (by simpa [hhead] using hyx.symm)
    refine ⟨z :: x :: L, rfl, ?_, hchain'.cons (by simpa using hzx), ?_⟩
    · simp [hzxne, hznot, hxnot, hnodup]
    · intro b
      simp only [List.mem_cons, hcover, Finset.mem_erase]
      by_cases qx : b = x <;> by_cases qy : b = y <;> simp_all
  · have el : left = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have er : right = ∅ := Finset.card_eq_zero.mp (by simpa [el] using hcard.symm)
    subst left
    subst right
    exact ⟨[z],rfl,by simp,by simp,by simp⟩
termination_by left.card
decreasing_by rw [Finset.card_erase_of_mem hxl]; have hpos := Finset.card_pos.mpr hn; omega

omit [DecidableEq V] in
private theorem dist_two_of_two_edges (hc : G.Connected) {a b x : V}
    (hab : G.Adj a b) (hbx : G.Adj b x) (hne : a ≠ x) (hn : ¬ G.Adj a x) :
    G.dist a x = 2 := by
  have hlt := hc.one_lt_dist_of_ne_of_not_adj hne hn
  have hle : G.dist a x ≤ 2 := G.dist_le (.cons hab (.cons hbx .nil))
  omega

omit [DecidableEq V] in
private theorem contact_universal (hc : G.Connected) {A : Finset V}
    (ha : (G.induce (A : Set V)).Connected) {x : V} (hx : x ∈ A)
    (hn : ∀ y ∈ A, G.dist x y ≠ 2) {v : V} (hv : v ∈ A) (hnv : x ≠ v) :
    G.Adj x v := by
  by_contra hvn
  let F : Set (A : Set V) := {w | x ≠ w.val ∧ ¬ G.Adj x w.val}
  obtain ⟨P⟩ := ha (⟨v,hv⟩ : (A : Set V)) ⟨x,hx⟩
  have notx : (⟨x,hx⟩ : (A : Set V)) ∉ F := fun h => h.1 rfl
  obtain ⟨b,_,hi,ho⟩ := P.exists_boundary_dart F ⟨hnv,hvn⟩ notx
  have he : G.Adj b.fst.val b.snd.val := b.adj
  have hnext : G.Adj x b.snd.val := by
    by_contra h
    by_cases hh : x = b.snd.val
    · exact hi.2 (hh ▸ he.symm)
    · exact ho ⟨hh,h⟩
  exact hn b.fst.val b.fst.property (dist_two_of_two_edges hc hnext he.symm hi.1 hi.2)

variable [Fintype V] [DecidableRel G.Adj]

/-- A component of order exactly twice the second-degree threshold has a
spanning path starting at its gate. -/
theorem rooted_at_two_k {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) {c : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G c B) (hAB : Disjoint A B)
    (hconn : (G.induce (A : Set V)).Connected) (hsize : A.card = 2*k)
    (hb : k ≤ B.card) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  classical
  have pb := hB.parity_bound hc hσ
  have hsub : insert c A ⊆ Bᶜ := by
    intro x hx
    apply mem_compl.mpr
    rcases mem_insert.mp hx with rfl | hx
    · exact hB.outside
    · exact Finset.disjoint_left.mp hAB hx
  have hcount := card_le_card hsub
  rw [card_insert_of_notMem hA.outside] at hcount
  have hBcontact : ∀ x ∈ B, G.Adj c x :=
    Graph189CutMiddle.all_contacts_of_empty_even hB hc (by omega)
  have hfull {x : V} (hx : x ∈ A) (hcx : G.Adj c x) {v : V} (hv : v ∈ A)
      (hne : x ≠ v) : G.Adj x v := by
    apply contact_universal hc hconn hx _ hv hne
    intro y hy hdy
    have hxb := Finset.disjoint_left.mp hAB hx
    have hyb := Finset.disjoint_left.mp hAB hy
    have hxy : x ≠ y := by rintro rfl; simp at hdy
    have hs : insert y (insert x B) ⊆ univ.filter (fun z => Even (G.dist x z)) := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · simp [hdy]
      rcases mem_insert.mp hz with rfl | hz
      · simp
      · have hd := hA.dist_add hc hx (fun h => Finset.disjoint_left.mp hAB h hz)
        simp [hd,dist_eq_one_iff_adj.mpr hcx.symm,dist_eq_one_iff_adj.mpr (hBcontact z hz)]
    have cap := (card_le_card hs).trans (hσ x)
    rw [card_insert_of_notMem (by simp [hxy.symm,hyb]),card_insert_of_notMem hxb] at cap
    omega
  let P := A.filter (G.Adj c ·)
  let Q := A \ P
  have hPA : P ⊆ A := filter_subset _ _
  obtain ⟨a,ha,hac⟩ := hA.contact hc
  have hQsub : insert c Q ⊆ univ.filter (fun y => Even (G.dist c y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp
    · obtain ⟨hyA,hyP⟩ := mem_sdiff.mp hy
      have hcy : ¬ G.Adj c y := fun he => hyP (mem_filter.mpr ⟨hyA,he⟩)
      have hay : a ≠ y := fun e => hcy (e ▸ hac.symm)
      have hdy := dist_two_of_two_edges hc hac.symm (hfull ha hac.symm hyA hay)
        (fun e => hA.outside (e ▸ hyA)) hcy
      simp [hdy]
  have hq := (card_le_card hQsub).trans (hσ c)
  rw [card_insert_of_notMem (fun h => hA.outside (mem_sdiff.mp h).1)] at hq
  have hsum : Q.card + P.card = A.card := card_sdiff_add_card_eq_card hPA
  change Q.card + 1 ≤ 1+k at hq
  rw [hsize] at hsum
  obtain ⟨T,hTP,hT⟩ := exists_subset_card_eq (s := P) (n := k) (by omega)
  have hTA := hTP.trans hPA
  have hTR := card_sdiff_add_card_eq_card hTA
  rw [hT,hsize] at hTR
  obtain ⟨L,hl,hn,hch,hcov⟩ := alternating_chain (G:=G) T (A \ T) c
    (by omega) (fun x hx hy => (mem_sdiff.mp hy).2 hx)
    (fun h => hA.outside (hTA h)) (fun h => hA.outside (mem_sdiff.mp h).1)
    (fun y hy x hx => (hfull (hTA hx) (mem_filter.mp (hTP hx)).2 (mem_sdiff.mp hy).1
      (fun e => (mem_sdiff.mp hy).2 (e ▸ hx))).symm)
    (fun ⟨x,hx⟩ => ⟨x,hx,(mem_filter.mp (hTP hx)).2⟩)
  refine ⟨L,hl,hn,hch,?_⟩
  intro z
  rw [hcov]
  simp only [mem_sdiff]
  have hz : z ∈ T → z ∈ A := fun h => hTA h
  tauto

#print axioms rooted_at_two_k
end Graph189CutExtreme
