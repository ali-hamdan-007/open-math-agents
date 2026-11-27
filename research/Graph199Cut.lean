import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem star_tree (v : V) (S : Finset V)
    (hind : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b)) (hadj : ∀ x ∈ S, G.Adj v x) :
    (G.induce (↑(insert v S) : Set V)).IsTree := by
  induction S using Finset.induction_on with
  | empty =>
    have hs : (↑(insert v (∅ : Finset V)) : Set V) = {v} := by ext y; simp
    rw [hs]
    let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
    let _ : Subsingleton ↥({v} : Set V) := ⟨fun a b => Subtype.ext
      ((Set.mem_singleton_iff.mp a.property).trans (Set.mem_singleton_iff.mp b.property).symm)⟩
    exact IsTree.of_subsingleton
  | @insert x S hx ih =>
    have hvx := hadj x (mem_insert_self x S)
    have hS : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b) :=
      hind.mono (by simpa only [coe_insert] using Set.subset_insert x (S : Set V))
    have hT := ih hS (fun y hy => hadj y (mem_insert_of_mem hy))
    rw [insert_comm]
    apply hT.induce_insert_of_unique_adj (by simp [hx, hvx.ne.symm])
      (mem_insert_self v S) hvx.symm
    intro y hy hxy
    rcases mem_insert.mp hy with rfl | hy
    · rfl
    exact (hind (mem_insert_self x S) (mem_insert_of_mem hy) hxy.ne hxy).elim

/-- An independent subset of a neighborhood extends to an induced star. -/
theorem star_bound (v : V) (S : Finset V) (hind : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b))
    (hadj : ∀ x ∈ S, G.Adj v x) : S.card + 1 ≤ largestInducedTreeSize G := by
  have hvS : v ∉ S := fun h => (hadj v h).ne rfl
  simpa only [card_insert_of_notMem hvS] using
    card_le_largestInducedTreeSize (star_tree v S hind hadj)

private theorem dist_le_two (hG : G.Connected) (ht : largestInducedTreeSize G ≤ 3)
    (x y : V) : G.dist x y ≤ 2 := by
  obtain ⟨p, hp, hlen⟩ := (hG x y).exists_path_of_dist
  have hc := card_le_largestInducedTreeSize (p.induce_support_isTree_of_length_eq_dist hlen)
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support, hlen] at hc
  omega

omit [Fintype V] [DecidableEq V] in
private theorem adj_of_cross_walk {v x y : V} (L : Set V)
    (hx : x ∈ L) (hy : y ∉ L) (hyv : y ≠ v)
    (hcross : ∀ a ∈ L, ∀ b ∉ L, b ≠ v → ¬ G.Adj a b)
    (p : G.Walk x y) (hp : p.length ≤ 2) : G.Adj x v ∧ G.Adj v y := by
  cases p with
  | nil => exact (hy hx).elim
  | @cons _ z _ hxz q =>
    cases q with
    | nil => exact (hcross _ hx _ hy hyv hxz).elim
    | @cons _ w _ hzw r =>
      cases r with
      | nil =>
        by_cases hz : z ∈ L
        · exact (hcross _ hz _ hy hyv hzw).elim
        · have hzv : z = v := by
            by_contra hne
            exact hcross _ hx _ hz hne hxz
          subst z
          exact ⟨hxz, hzw⟩
      | cons _ _ =>
        simp at hp


private theorem no_star_three (v a b c : V) (ht : largestInducedTreeSize G ≤ 3)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnab : ¬ G.Adj a b) (hnac : ¬ G.Adj a c) (hnbc : ¬ G.Adj b c) : False := by
  have hind : ((↑({a, b, c} : Finset V)) : Set V).Pairwise (fun a b => ¬ G.Adj a b) := by
    intro x hx y hy hne
    simp only [mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact hnab | exact hnac | exact hnbc | exact (fun h => hnab h.symm)
            | exact (fun h => hnac h.symm) | exact (fun h => hnbc h.symm) | contradiction
  have h := star_bound v {a, b, c} hind (by simp [ha, hb, hc])
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
      card_singleton]
  omega

private theorem hamiltonian_of_cut_partition (v : V) (L : Set V)
    (hG : G.Connected) (ht : largestInducedTreeSize G ≤ 3)
    (hv : v ∉ L) (hL : L.Nonempty) (hR : ∃ y ∉ L, y ≠ v)
    (hcross : ∀ a ∈ L, ∀ b ∉ L, b ≠ v → ¬ G.Adj a b) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x, hx⟩ := hL
  obtain ⟨y, hy, hyv⟩ := hR
  have cross_adj {a b : V} (ha : a ∈ L) (hb : b ∉ L) (hbv : b ≠ v) :
      G.Adj a v ∧ G.Adj v b := by
    obtain ⟨p, plen⟩ := (hG a b).exists_walk_length_eq_dist
    exact adj_of_cross_walk L ha hb hbv hcross p (by rw [plen]; exact dist_le_two hG ht a b)
  have hall {a : V} (ha : a ≠ v) : G.Adj v a := by
    by_cases haL : a ∈ L
    · exact (cross_adj haL hy hyv).1.symm
    · exact (cross_adj hx haL ha).2
  have hleft {a b : V} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : G.Adj a b := by
    by_contra hn
    have hav : a ≠ v := fun h => hv (h ▸ ha)
    have hbv : b ≠ v := fun h => hv (h ▸ hb)
    exact no_star_three v a b y ht (hall hav) (hall hbv) (hall hyv) hab
      (fun h => hy (h ▸ ha)) (fun h => hy (h ▸ hb)) hn
      (hcross a ha y hy hyv) (hcross b hb y hy hyv)
  have hright {a b : V} (ha : a ∉ L) (hav : a ≠ v) (hb : b ∉ L) (hbv : b ≠ v)
      (hab : a ≠ b) : G.Adj a b := by
    by_contra hn
    have hxv : x ≠ v := fun h => hv (h ▸ hx)
    exact no_star_three v x a b ht (hall hxv) (hall hav) (hall hbv)
      (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx)) hab
      (hcross x hx a ha hav) (hcross x hx b hb hbv) hn
  let left := (univ.filter (· ∈ L)).toList
  let right := (univ.filter (fun a => a ∉ L ∧ a ≠ v)).toList
  have memLeft {a : V} : a ∈ left ↔ a ∈ L := by simp [left]
  have memRight {a : V} : a ∈ right ↔ a ∉ L ∧ a ≠ v := by simp [right]
  have ndLeft : left.Nodup := nodup_toList _
  have ndRight : right.Nodup := nodup_toList _
  have lc : left.IsChain G.Adj := by
    apply List.Pairwise.isChain
    apply List.pairwise_iff_get.mpr
    intro i j hij
    exact hleft (memLeft.mp (List.get_mem _ _)) (memLeft.mp (List.get_mem _ _))
      (List.pairwise_iff_get.mp ndLeft i j hij)
  have rc : right.IsChain G.Adj := by
    apply List.Pairwise.isChain
    apply List.pairwise_iff_get.mpr
    intro i j hij
    obtain ⟨hni, hiv⟩ := memRight.mp (List.get_mem right i)
    obtain ⟨hnj, hjv⟩ := memRight.mp (List.get_mem right j)
    exact hright hni hiv hnj hjv (List.pairwise_iff_get.mp ndRight i j hij)
  let l := left ++ v :: right
  have hchain : l.IsChain G.Adj := by
    apply lc.append
    · apply rc.cons
      intro z hz
      exact hall (memRight.mp (List.mem_of_mem_head? hz)).2
    · intro a ha b hb
      have hav : a ≠ v := fun h => hv (h ▸ memLeft.mp (List.mem_of_mem_getLast? ha))
      have hbv : v = b := by simpa using hb
      simpa [hbv] using (hall hav).symm
  have hn : l.Nodup := by
    refine List.nodup_append'.mpr ⟨ndLeft, List.nodup_cons.mpr ⟨?_, ndRight⟩, ?_⟩
    · exact fun h => (memRight.mp h).2 rfl
    · intro z hz hz'
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hv (memLeft.mp hz)
      · exact (memRight.mp hz').1 (memLeft.mp hz)
  have hmem (z : V) : z ∈ l := by
    by_cases hz : z ∈ L
    · exact List.mem_append_left _ (memLeft.mpr hz)
    · apply List.mem_append_right
      by_cases hzv : z = v
      · simp [hzv]
      · exact List.mem_cons_of_mem _ (memRight.mpr ⟨hz, hzv⟩)
  have hne : l ≠ [] := fun he => by simpa [he] using hmem v
  let p := Walk.ofSupport l hne hchain
  have hs : p.support = l := Walk.support_ofSupport hne hchain
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hs]
  exact ⟨_, _, p, hp.isHamiltonian_of_mem (fun z => by rw [hs]; exact hmem z)⟩

/-- In a connected graph with a cut vertex, induced-tree order at most three forces a
Hamiltonian path. The two sides of the cut are cliques, and the cut vertex joins both. -/
theorem hamiltonian_of_cut_vertex [Nontrivial V] (hG : G.Connected)
    (ht : largestInducedTreeSize G ≤ 3) (v : V)
    (hcut : ¬ (G.induce ({v} : Set V)ᶜ).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x, hx⟩ := exists_ne v
  let a : ↥(({v} : Set V)ᶜ) := ⟨x, by simpa using hx⟩
  let K := G.induce ({v} : Set V)ᶜ
  obtain ⟨b, hb⟩ : ∃ b, ¬ K.Reachable a b := by
    by_contra! h
    let _ : Nonempty ↥(({v} : Set V)ᶜ) := ⟨a⟩
    have hc : K.Connected := ⟨fun c d => (h c).symm.trans (h d)⟩
    exact hcut hc
  let L : Set V := {z | ∃ c : ↥(({v} : Set V)ᶜ), c.val = z ∧ K.Reachable a c}
  have hv : v ∉ L := by
    rintro ⟨⟨z, hz⟩, he, -⟩
    change z = v at he
    exact hz (Set.mem_singleton_iff.mpr he)
  have hL : L.Nonempty := ⟨x, a, rfl, Reachable.refl _⟩
  have hR : ∃ y ∉ L, y ≠ v := by
    refine ⟨b.val, ?_, fun he => b.property (Set.mem_singleton_iff.mpr he)⟩
    rintro ⟨c, hc, hac⟩
    exact hb ((Subtype.ext hc) ▸ hac)
  have hcross : ∀ u ∈ L, ∀ w ∉ L, w ≠ v → ¬ G.Adj u w := by
    rintro u ⟨c, rfl, hac⟩ w hw hwv hcw
    let d : ↥(({v} : Set V)ᶜ) := ⟨w, by simpa using hwv⟩
    have hcd : K.Adj c d := hcw
    exact hw ⟨d, rfl, hac.trans hcd.reachable⟩
  exact hamiltonian_of_cut_partition v L hG ht hv hL hR hcross

/-- The cut-vertex case of Written on the Wall II conjecture 199. -/
theorem conjecture199_of_cut_vertex [Nontrivial V] (hG : G.Connected)
    (hκ : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) (v : V)
    (hcut : ¬ (G.induce ({v} : Set V)ᶜ).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hk : vertexConnectivity G ≤ 1 := by
    unfold vertexConnectivity
    split_ifs
    · omega
    · apply csInf_le'
      refine ⟨{v}, by simp, Or.inl ?_⟩
      rwa [coe_singleton]
  exact hamiltonian_of_cut_vertex hG (by omega) v hcut

private theorem hamiltonian_of_card_two [Nontrivial V] (hG : G.Connected)
    (hn : Fintype.card V = 2) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  obtain ⟨p, hp⟩ := (hG a b).exists_isPath
  have hin : ({a, b} : Finset V) ⊆ p.support.toFinset := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr p.start_mem_support
    · exact List.mem_toFinset.mpr p.end_mem_support
  have hc := card_le_card hin
  rw [card_insert_of_notMem (by simpa using hab), card_singleton] at hc
  have hs : p.support.toFinset = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simpa [hn] using hc
  exact ⟨a, b, p, hp.isHamiltonian_of_mem (fun x => List.mem_toFinset.mp (by simp [hs]))⟩

/-- Written on the Wall II conjecture 199 holds at vertex connectivity at most one. -/
theorem conjecture199_of_connectivity_le_one [Nontrivial V] (hG : G.Connected)
    (hκ : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (hκ1 : vertexConnectivity G ≤ 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have hn : 1 < Fintype.card V := Fintype.one_lt_card
  by_cases hn2 : Fintype.card V = 2
  · exact hamiltonian_of_card_two hG hn2
  let A : Set ℕ := {k | ∃ S : Finset V, S.card = k ∧
    (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1)}
  have hkn : vertexConnectivity G = sInf A := by
    unfold vertexConnectivity
    rw [if_neg hn.not_ge]
  have hA : A.Nonempty := by
    let v : V := Classical.choice hG.nonempty
    exact ⟨Fintype.card V - 1, univ.erase v, by simp, Or.inr (by simp)⟩
  obtain ⟨S, hS, hcut | hcard⟩ := Nat.sInf_mem hA
  · rw [← hkn] at hS
    have hS1 : S.card = 1 := by
      by_contra hne
      have hz : S.card = 0 := by omega
      have hempty : S = ∅ := card_eq_zero.mp hz
      apply hcut
      rw [hempty, coe_empty, Set.compl_empty]
      exact G.induceUnivIso.connected_iff.mpr hG
    obtain ⟨v, rfl⟩ := card_eq_one.mp hS1
    exact conjecture199_of_cut_vertex hG hκ v (by rwa [coe_singleton] at hcut)
  · rw [← hkn] at hS
    omega

end Graph199

#print axioms Graph199.conjecture199_of_cut_vertex
#print axioms Graph199.conjecture199_of_connectivity_le_one
