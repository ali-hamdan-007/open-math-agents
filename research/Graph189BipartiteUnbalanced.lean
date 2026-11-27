import Graph189BipartiteStructure
import Graph199BlockChain

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

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

/-- The unbalanced bipartite case of DeLaViña's Written on the Wall II conjecture 189. -/
theorem hamiltonian_unbalanced [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.Connected) (C : G.Coloring (Fin 2))
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    {c d : Fin 2} (hcd : c ≠ d) (hc : (part C c).Nonempty)
    (hsize : (part C c).card < (part C d).card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨hcard,z,hzd,hcomplete⟩ := unbalanced_part_complete_off_one h C hσ hcd hc hsize
  have hzl : z ∉ part C c := fun hz =>
    hcd (((mem_part C c z).mp hz).symm.trans ((mem_part C d z).mp hzd))
  have hdisjoint (x : V) (hx : x ∈ part C c) : x ∉ (part C d).erase z := by
    intro hr
    exact hcd (((mem_part C c x).mp hx).symm.trans
      ((mem_part C d x).mp (Finset.mem_of_mem_erase hr)))
  obtain ⟨L,hhead,hnodup,hchain,hcover⟩ :=
    alternating_chain (part C c) ((part C d).erase z) z
      (by rw [Finset.card_erase_of_mem hzd,hcard]; omega)
      hdisjoint hzl (Finset.notMem_erase _ _)
      (fun y hy => hcomplete y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
      (fun _ => by
        obtain ⟨x,hzx⟩ := h.preconnected.exists_adj_of_nontrivial z
        exact ⟨x, neighborFinset_subset_part C hcd.symm hzd ((G.mem_neighborFinset z x).mpr hzx), hzx⟩)
  have hne : L ≠ [] := by intro he; simp [he] at hhead
  let p := Walk.ofSupport L hne hchain
  have hs : p.support = L := Walk.support_ofSupport hne hchain
  refine ⟨_,_,p,(Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem ?_⟩
  intro v
  rw [hs,hcover]
  have hm : C v = c ∨ C v = d := by
    generalize C v = e
    fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all
  rcases hm with hv | hv
  · exact Or.inr (Or.inl ((mem_part C c v).mpr hv))
  · by_cases hvz : v = z
    · exact Or.inl hvz
    · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hvz,(mem_part C d v).mpr hv⟩))

#print axioms hamiltonian_unbalanced
end Graph189Bipartite
