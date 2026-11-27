import Graph189BipartiteSmall
import Graph189BipartiteUnbalanced
import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Graph189Leaf
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] in
/-- Remove the self contribution from the even-distance budget. -/
private theorem layer_bound {x : V} (S : Finset V) (hx : x ∉ S)
    (hS : ∀ y ∈ S, G.dist x y = 2) (h : G.distEven x ≤ 1 + G.secondSmallestDegree) :
    S.card ≤ G.secondSmallestDegree := by
  classical
  have hi : insert x S ⊆ Finset.univ.filter (fun y => Even (G.dist x y)) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simp
    · simp [hS y hy]
  have hh := Finset.card_le_card hi
  rw [Finset.card_insert_of_notMem hx] at hh
  change (Finset.univ.filter (fun y => Even (G.dist x y))).card ≤ _ at h
  omega

omit [DecidableEq V] [Nontrivial V] in
/-- The two inner layers of a leaf and its neighbor have the same size budget. -/
theorem leaf_layers (hc : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree) {z v : V}
    (hz : G.neighborFinset z = {v}) :
    ∃ A B : Finset V,
      (∀ x, x ∈ A ↔ x ≠ z ∧ G.Adj v x) ∧
      (∀ x, x ∈ B ↔ x ≠ z ∧ x ≠ v ∧ ¬ G.Adj v x) ∧
      A.card ≤ G.secondSmallestDegree ∧ B.card ≤ G.secondSmallestDegree ∧
      A.card + B.card + 2 = Fintype.card V ∧ G.degree v = A.card + 1 := by
  classical
  let _ : Nonempty V := ⟨z⟩
  have hleaf (x : V) : G.Adj z x ↔ x = v := by
    rw [← mem_neighborFinset, hz, Finset.mem_singleton]
  have hzv := (hleaf v).mpr rfl
  let A := (G.neighborFinset v).erase z
  let B := (Finset.univ.erase z).erase v \ A
  have ha (x : V) : x ∈ A ↔ x ≠ z ∧ G.Adj v x := by simp [A]
  have hb (x : V) : x ∈ B ↔ x ≠ z ∧ x ≠ v ∧ ¬ G.Adj v x := by
    simp [B, ha]; tauto
  have hA : A.card ≤ G.secondSmallestDegree := by
    apply layer_bound A (fun h => (ha z).mp h |>.1 rfl) _ (hσ z)
    intro x h
    obtain ⟨hx,hvx⟩ := (ha x).mp h
    let p : G.Walk z x := .cons hzv (.cons hvx .nil)
    have hle : G.dist z x ≤ 2 := G.dist_le p
    have hn := fun (e : G.dist z x = 1) => hvx.ne ((hleaf x).mp (dist_eq_one_iff_adj.mp e)).symm
    have hpos : 0 < G.dist z x := Nat.pos_of_ne_zero (fun e => hx (p.reachable.dist_eq_zero_iff.mp e).symm)
    by_contra bad
    exact hn (by omega)
  have hB : B.card ≤ G.secondSmallestDegree := by
    apply layer_bound B (fun h => ((hb v).mp h).2.1 rfl) _ (hσ v)
    intro x h
    obtain ⟨hxz,hxv,hn⟩ := (hb x).mp h
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist z x
    have hlen := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := z) (v := x)).trans hd
    have hle : G.dist v x ≤ 2 := by
      cases p with
      | nil => exact (hxz rfl).elim
      | cons hzy q =>
        have ey := (hleaf _).mp hzy
        cases ey
        have hq := G.dist_le q
        rw [Walk.length_cons] at hp
        omega
    have hpos : 0 < G.dist v x := Nat.pos_of_ne_zero (fun e => hxv ((hc v x).dist_eq_zero_iff.mp e).symm)
    have hne := fun (e : G.dist v x = 1) => hn (dist_eq_one_iff_adj.mp e)
    by_contra bad
    exact hne (by omega)
  have hAinc : A ⊆ ((Finset.univ.erase z).erase v : Finset V) := by
    intro x hx
    obtain ⟨h1,h2⟩ := (ha x).mp hx
    simp [h1,h2.ne.symm]
  have hcard := Finset.card_sdiff_add_card_eq_card hAinc
  have hne := hzv.ne
  have hc1 := Finset.card_erase_add_one (Finset.mem_univ z)
  have hc2 := Finset.card_erase_add_one (show v ∈ (Finset.univ.erase z : Finset V) by simp [hne.symm])
  have hdeg := Finset.card_erase_add_one (show z ∈ G.neighborFinset v from (G.mem_neighborFinset _ _).mpr hzv.symm)
  rw [card_neighborFinset_eq_degree] at hdeg
  refine ⟨A,B,ha,hb,hA,hB,?_,hdeg.symm⟩
  change B.card + A.card = _ at hcard
  rw [Finset.card_univ] at hc1
  omega
omit [Nontrivial V] in
/-- A graph saturated under the path degree-sum closure contains a spanning
path as soon as it contains the two leaf layers with their degree bounds. -/
theorem traceable_saturated_leaf {H : SimpleGraph V} [DecidableRel H.Adj]
    (hsub : G ≤ H)
    (hsat : ∀ x y : V, x ≠ y → Fintype.card V ≤ H.degree x + H.degree y + 1 → H.Adj x y)
    {z v : V} (hzv : G.Adj z v) {s : ℕ} (hdeg : ∀ x, x ≠ z → s ≤ G.degree x)
    (A B : Finset V)
    (ha : ∀ x, x ∈ A ↔ x ≠ z ∧ G.Adj v x)
    (hb : ∀ x, x ∈ B ↔ x ≠ z ∧ x ≠ v ∧ ¬ G.Adj v x)
    (hA : A.card ≤ s) (hB : B.card ≤ s)
    (horder : A.card + B.card + 2 = Fintype.card V)
    (hdv : G.degree v = A.card + 1) :
    ∃ a b : V, ∃ p : H.Walk a b, p.IsHamiltonian := by
  classical
  have monot (x : V) : G.degree x ≤ H.degree x := degree_le_of_le hsub
  have high (x : V) (hx : x ≠ z) : s ≤ H.degree x := (hdeg x hx).trans (monot x)
  by_cases hn : Fintype.card V ≤ 2 * s + 1
  · have clique {x y : V} (hx : x ≠ z) (hy : y ≠ z) (hne : x ≠ y) : H.Adj x y :=
      hsat x y hne (by have := high x hx; have := high y hy; omega)
    let C := ((Finset.univ.erase z).erase v : Finset V)
    let L := v :: C.toList
    have hnv : v ∉ C := Finset.notMem_erase _ _
    have hc (x : V) : x ∈ C ↔ x ≠ v ∧ x ≠ z := by simp [C]
    have hnd : L.Nodup := by simp [L,hnv,C.nodup_toList]
    have hmem : ∀ x ∈ L, x ≠ z := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hzv.ne.symm
      · exact ((hc _).mp (Finset.mem_toList.mp hx)).2
    have hpair : L.Pairwise H.Adj :=
      List.Pairwise.imp_of_mem (fun hx hy hne => clique (hmem _ hx) (hmem _ hy) hne) hnd
    have hchain : (z :: L).IsChain H.Adj := hpair.isChain.cons (by simpa [L] using hsub hzv)
    have hcs := Finset.card_erase_add_one (Finset.mem_univ z)
    have hcv := Finset.card_erase_add_one (show v ∈ (Finset.univ.erase z : Finset V) by simp [hzv.ne.symm])
    have hlen : (z :: L).length = Fintype.card V := by
      simp only [L,List.length_cons,Finset.length_toList]
      rw [Finset.card_univ] at hcs
      change C.card + 1 = _ at hcv
      omega
    exact Graph189Bipartite.hamiltonian_of_chain _ (by simp) hchain
      (List.nodup_cons.mpr ⟨fun h => hmem z h rfl,hnd⟩) hlen
  have hca : A.card = s := by omega
  have hcb : B.card = s := by omega
  have hvb (x : V) (hx : x ∈ B) : H.Adj v x := by
    obtain ⟨hxz,hxv,_⟩ := (hb x).mp hx
    exact hsat v x hxv.symm (by have := monot v; have := high x hxz; omega)
  have hraise (x : V) (hx : x ∈ B) : s + 1 ≤ H.degree x := by
    obtain ⟨hxz,_,hmiss⟩ := (hb x).mp hx
    have hstrict : G.neighborFinset x ⊂ H.neighborFinset x := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
      · intro y hy
        exact (H.mem_neighborFinset _ _).mpr (hsub ((G.mem_neighborFinset _ _).mp hy))
      · intro eq
        have hmem : v ∈ H.neighborFinset x := (H.mem_neighborFinset _ _).mpr (hvb x hx).symm
        rw [← eq] at hmem
        exact hmiss ((G.mem_neighborFinset _ _).mp hmem).symm
    have hgt := Finset.card_lt_card hstrict
    simp only [card_neighborFinset_eq_degree] at hgt
    have := hdeg x hxz
    omega
  have hdisj (x : V) (hx : x ∈ B) (h : x ∈ A) := ((hb x).mp hx).2.2 ((ha x).mp h).2
  have hcross (y : V) (hy : y ∈ A) (x : V) (hx : x ∈ B) : H.Adj y x := by
    have hne : y ≠ x := fun e => hdisj x hx (e ▸ hy)
    exact hsat y x hne (by have := high y ((ha _).mp hy).1; have := hraise x hx; omega)
  have hvA : v ∉ A := fun h => ((ha v).mp h).2.ne rfl
  have hvB : v ∉ B := fun h => ((hb v).mp h).2.1 rfl
  obtain ⟨L,hhead,hnd,hch,hmem⟩ := Graph189Bipartite.alternating_chain B A v
    (hcb.trans hca.symm) hdisj hvB hvA hcross (by rintro ⟨x,hx⟩; exact ⟨x,hx,hvb x hx⟩)
  have hznot : z ∉ L := by
    rw [hmem]; push Not
    exact ⟨hzv.ne,fun h => ((hb _).mp h).1 rfl,fun h => ((ha _).mp h).1 rfl⟩
  have hd : (z :: L).Nodup := List.nodup_cons.mpr ⟨hznot,hnd⟩
  have hall : (z :: L).toFinset = Finset.univ := by
    ext x
    simp only [List.mem_toFinset, List.mem_cons, hmem, Finset.mem_univ, iff_true]
    by_cases f : x = z
    · exact Or.inl f
    by_cases g : x = v
    · exact Or.inr (Or.inl g)
    by_cases t : G.Adj v x
    · exact Or.inr (Or.inr (Or.inr ((ha x).mpr ⟨f,t⟩)))
    · exact Or.inr (Or.inr (Or.inl ((hb x).mpr ⟨f,g,t⟩)))
  have hlen := List.toFinset_card_of_nodup hd
  rw [hall,Finset.card_univ] at hlen
  exact Graph189Bipartite.hamiltonian_of_chain _ (by simp)
    (hch.cons (by simpa [hhead] using hsub hzv)) hd hlen.symm

end Graph189Leaf
