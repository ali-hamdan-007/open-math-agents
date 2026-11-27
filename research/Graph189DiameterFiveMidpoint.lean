import Graph189DistanceLayers

namespace Graph189DiameterFiveMidpoint
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A portion X of b's closed neighborhood is within two steps of a
neighbor v of b. After excluding v and its direct neighbors, all
remaining vertices of X are at distance two from v. -/
private theorem remote_side {v b : V} {X : Finset V}
    (hb : G.Adj v b) (hvX : v ∉ X)
    (hX : X ⊆ insert b (G.neighborFinset b)) :
    ∀ x ∈ X \ G.neighborFinset v, G.dist v x = 2 := by
  intro x hx
  obtain ⟨hxX,hmiss⟩ := mem_sdiff.mp hx
  have hmiss' : ¬ G.Adj v x := fun h => hmiss ((G.mem_neighborFinset v x).mpr h)
  rcases mem_insert.mp (hX hxX) with e | hn
  · exact False.elim (hmiss' (e.symm ▸ hb))
  · exact Graph189LowDegreeTwo.two_edges hb ((G.mem_neighborFinset b x).mp hn)
      (fun h => hvX (h.symm ▸ hxX)) hmiss'

/-- Count the two disjoint end portions of the closed neighborhoods
of neighbors of a midpoint. This applies with X=N[b]∩(A∪B) on one
side and Y=N[d]∩(D∪F) on the other. -/
theorem midpoint_support_sum {v b d : V} {X Y : Finset V} {s p q : ℕ}
    (hb : G.Adj v b) (hd : G.Adj v d) (hvX : v ∉ X) (hvY : v ∉ Y)
    (hX : X ⊆ insert b (G.neighborFinset b)) (hY : Y ⊆ insert d (G.neighborFinset d))
    (hdis : Disjoint X Y) (hp : (X ∩ G.neighborFinset v).card ≤ p)
    (hq : (Y ∩ G.neighborFinset v).card ≤ q)
    (hcap : (univ.filter (fun x => G.dist v x = 2)).card ≤ s) :
    X.card + Y.card ≤ s + p + q := by
  let X' := X \ G.neighborFinset v
  let Y' := Y \ G.neighborFinset v
  have hsub : X' ∪ Y' ⊆ univ.filter (fun x => G.dist v x = 2) := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(mem_union.mp hx).elim (remote_side hb hvX hX x)
      (remote_side hd hvY hY x)⟩
  have hdj : Disjoint X' Y' := hdis.mono sdiff_subset sdiff_subset
  have hbound := (card_le_card hsub).trans hcap
  rw [card_union_of_disjoint hdj] at hbound
  have h1 := card_sdiff_add_card_inter X (G.neighborFinset v)
  have h2 := card_sdiff_add_card_inter Y (G.neighborFinset v)
  change (X \ G.neighborFinset v).card + (Y \ G.neighborFinset v).card ≤ s at hbound
  omega

/-- Large midpoint support on one side forces all its endpoint vertices
to reach the midpoint in two steps. -/
theorem end_layer_two {v : V} {A B : Finset V} {i : ℕ}
    (hmiss : ∀ x ∈ A, (B \ G.neighborFinset x).card ≤ i)
    (hsupp : i < (B ∩ G.neighborFinset v).card)
    (hv : v ∉ A) (hn : ∀ x ∈ A, ¬ G.Adj v x) :
    ∀ x ∈ A, G.dist v x = 2 := by
  intro x hx
  have hex : ∃ y ∈ B ∩ G.neighborFinset v, G.Adj x y := by
    by_contra! hh
    have hsub : B ∩ G.neighborFinset v ⊆ B \ G.neighborFinset x := by
      intro y hy
      exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1,
        fun h => hh y hy ((G.mem_neighborFinset x y).mp h)⟩
    have h₁ := (card_le_card hsub).trans (hmiss x hx)
    omega
  obtain ⟨y,hy,hyx⟩ := hex
  exact Graph189LowDegreeTwo.two_edges ((G.mem_neighborFinset v y).mp (mem_inter.mp hy).2)
    hyx.symm (fun h => hv (h.symm ▸ hx)) (hn x hx)

/-- The end-layer dichotomy from the midpoint support inequality. -/
theorem midpoint_end_dichotomy {v : V} {A B D F : Finset V} {i j : ℕ}
    (hA : ∀ x ∈ A, (B \ G.neighborFinset x).card ≤ i)
    (hF : ∀ x ∈ F, (D \ G.neighborFinset x).card ≤ j)
    (hsum : i+j < (B ∩ G.neighborFinset v).card + (D ∩ G.neighborFinset v).card)
    (hvA : v ∉ A) (hvF : v ∉ F) (hnA : ∀ x ∈ A, ¬ G.Adj v x)
    (hnF : ∀ x ∈ F, ¬ G.Adj v x) :
    (∀ x ∈ A, G.dist v x = 2) ∨ (∀ x ∈ F, G.dist v x = 2) := by
  by_cases h : i < (B ∩ G.neighborFinset v).card
  · exact Or.inl (end_layer_two hA h hvA hnA)
  · exact Or.inr (end_layer_two hF (by omega) hvF hnF)

/-- At least s+1-c of a high-degree vertex's closed neighborhood belong
to the side X when at most c of the closed neighbors are in the middle. -/
private theorem side_size {b : V} {X C : Finset V} {s c : ℕ}
    (hcover : insert b (G.neighborFinset b) ⊆ X ∪ C) (hdeg : s ≤ G.degree b)
    (hC : ((insert b (G.neighborFinset b)) ∩ C).card ≤ c) :
    s+1 ≤ (X ∩ insert b (G.neighborFinset b)).card + c := by
  let K := insert b (G.neighborFinset b)
  have hs : K \ C ⊆ X ∩ K := by
    intro x hx
    obtain ⟨hk,hn⟩ := mem_sdiff.mp hx
    exact mem_inter.mpr ⟨(mem_union.mp (hcover hk)).resolve_right hn,hk⟩
  have hle := card_le_card hs
  have hsum := card_sdiff_add_card_inter K C
  have hc : K.card = G.degree b + 1 := by
    simp [K,card_insert_of_notMem (G.notMem_neighborFinset_self b)]
  change (K ∩ C).card ≤ c at hC
  change s+1 ≤ (X ∩ K).card + c
  omega

/-- End-layer dichotomy with the actual degree, incidence and cap
hypotheses used at the center of a five-edge geodesic. Here C is the
central layer and L,H are the two sides A∪B,D∪F. The side caps hLeft,
hRight result from the opposite end layer already lying at distance four. -/
theorem geodesic_midpoint_covers_an_end
    {v b d : V} {A B C D F : Finset V} {s i j hLeft hRight : ℕ}
    (hb : G.Adj v b) (hd : G.Adj v d)
    (hdegB : s ≤ G.degree b) (hdegD : s ≤ G.degree d)
    (hcB : insert b (G.neighborFinset b) ⊆ (A ∪ B) ∪ C)
    (hcD : insert d (G.neighborFinset d) ⊆ (D ∪ F) ∪ C)
    (hhB : (insert b (G.neighborFinset b) ∩ C).card ≤ hLeft)
    (hhD : (insert d (G.neighborFinset d) ∩ C).card ≤ hRight)
    (hsep : Disjoint (A ∪ B) (D ∪ F)) (hvL : v ∉ A ∪ B) (hvR : v ∉ D ∪ F)
    (hnA : ∀ x ∈ A, ¬ G.Adj v x) (hnF : ∀ x ∈ F, ¬ G.Adj v x)
    (hmissA : ∀ x ∈ A, (B \ G.neighborFinset x).card ≤ i)
    (hmissF : ∀ x ∈ F, (D \ G.neighborFinset x).card ≤ j)
    (harith : i+j+hLeft+hRight < s+2)
    (hcap : (univ.filter (fun x => G.dist v x = 2)).card ≤ s) :
    (∀ x ∈ A, G.dist v x = 2) ∨ (∀ x ∈ F, G.dist v x = 2) := by
  let X := (A ∪ B) ∩ insert b (G.neighborFinset b)
  let Y := (D ∪ F) ∩ insert d (G.neighborFinset d)
  have hX := side_size hcB hdegB hhB
  have hY := side_size hcD hdegD hhD
  change s+1 ≤ X.card + hLeft at hX
  change s+1 ≤ Y.card + hRight at hY
  have hsep' : Disjoint X Y := hsep.mono inter_subset_left inter_subset_left
  have hX' : X ∩ G.neighborFinset v ⊆ B ∩ G.neighborFinset v := by
    intro x hx
    obtain ⟨hxX,hxv⟩ := mem_inter.mp hx
    have hab := (mem_union.mp (mem_inter.mp hxX).1).resolve_left
      (fun h => hnA x h ((G.mem_neighborFinset v x).mp hxv))
    exact mem_inter.mpr ⟨hab,hxv⟩
  have hY' : Y ∩ G.neighborFinset v ⊆ D ∩ G.neighborFinset v := by
    intro x hx
    obtain ⟨hxY,hxv⟩ := mem_inter.mp hx
    have hdf := (mem_union.mp (mem_inter.mp hxY).1).resolve_right
      (fun h => hnF x h ((G.mem_neighborFinset v x).mp hxv))
    exact mem_inter.mpr ⟨hdf,hxv⟩
  have hsum := midpoint_support_sum hb hd (fun h => hvL (mem_inter.mp h).1)
    (fun h => hvR (mem_inter.mp h).1) inter_subset_right inter_subset_right
    hsep' (card_le_card hX') (card_le_card hY') hcap
  change X.card + Y.card ≤ s + (B ∩ G.neighborFinset v).card + (D ∩ G.neighborFinset v).card at hsum
  exact midpoint_end_dichotomy hmissA hmissF (by omega)
    (fun h => hvL (mem_union_left B h)) (fun h => hvR (mem_union_right D h)) hnA hnF

end Graph189DiameterFiveMidpoint

#print axioms Graph189DiameterFiveMidpoint.midpoint_support_sum
#print axioms Graph189DiameterFiveMidpoint.geodesic_midpoint_covers_an_end
