import Graph189SaturatedDistance

namespace Graph189PrivateSaturation

open SimpleGraph Finset Graph189SaturatedDistance

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The remote witnesses from the gate argument are disjoint from the fixed witnesses. -/
theorem private_witness_budget {w : V} {R N : Finset V} {a c k e : ℕ}
    (hR : ∀ v ∈ R, G.dist w v = 2) (hN : ∀ v ∈ N, G.dist w v = 2)
    (hdis : Disjoint R N) (hcap : (evenBall G w).card ≤ k + 1)
    (hremote : c - k - e ≤ R.card) (hfixed : a + 2 ≤ N.card) :
    c + a + 2 ≤ 2 * k + e := by
  have := card_add_le_of_disjoint_distance_two G hR hN hdis hcap
  omega

theorem private_saturation_contradiction {w : V} {R N : Finset V} {a c k : ℕ}
    (hR : ∀ v ∈ R, G.dist w v = 2) (hN : ∀ v ∈ N, G.dist w v = 2)
    (hdis : Disjoint R N) (hcap : (evenBall G w).card ≤ k + 1)
    (hremote : c - k ≤ R.card) (hfixed : a + 2 ≤ N.card)
    (hc : 2 * k - 3 ≤ c) (ha : 2 ≤ a) :
    False := by
  have hbound := private_witness_budget G (e := 0) hR hN hdis hcap
    (by simpa using hremote) hfixed
  omega

theorem private_near_saturation_contradiction {w : V} {R N : Finset V} {a c k : ℕ}
    (hR : ∀ v ∈ R, G.dist w v = 2) (hN : ∀ v ∈ N, G.dist w v = 2)
    (hdis : Disjoint R N) (hcap : (evenBall G w).card ≤ k + 1)
    (hremote : c - k - 1 ≤ R.card) (hfixed : a + 2 ≤ N.card)
    (hc : 2 * k - 3 ≤ c) (ha : 3 ≤ a) :
    False := by
  have hbound := private_witness_budget G hR hN hdis hcap hremote hfixed
  omega

/-- Apply the metric gate theorem separately to each outsider seen by the solo. -/
theorem private_gate_contradiction
    {p w : V} {S gates R N : Finset V} {a c k e : ℕ}
    (hS : ∀ v ∈ S, G.dist p v = 2) (hcard : S.card = k)
    (hcapP : (evenBall G p).card ≤ k + 1)
    (hfar : ∀ m ∈ R, 3 ≤ G.dist p m) (hnear : ∀ m ∈ R, G.dist p m ≤ 4)
    (hgate : ∀ m ∈ R, ∀ u ∈ S, G.Adj u m → u ∈ gates)
    (hsolo : ∀ u ∈ gates, G.Adj w u)
    (hne : ∀ m ∈ R, w ≠ m) (hnadj : ∀ m ∈ R, ¬ G.Adj w m)
    (hN : ∀ v ∈ N, G.dist w v = 2) (hdis : Disjoint R N)
    (hcapW : (evenBall G w).card ≤ k + 1)
    (hremote : c - k - e ≤ R.card) (hfixed : a + 2 ≤ N.card)
    (hc : 2 * k - 3 ≤ c) (ha : e + 2 ≤ a) :
    False := by
  have hR (m : V) (hm : m ∈ R) : G.dist w m = 2 :=
    solo_dist_two_of_saturation G hS hcard hcapP (hfar m hm) (hnear m hm)
      (hgate m hm) hsolo (hne m hm) (hnadj m hm)
  have hbound := private_witness_budget G hR hN hdis hcapW hremote hfixed
  omega

section Support

omit [Fintype V]

/-- A support that meets the lower bound with equality contains the triple
remote and attains both the neighborhood and boundary bounds. -/
theorem support_endpoint [DecidableEq V]
    {R H : Finset V} {t : V} {a k : ℕ}
    (hRH : R ⊆ H) (hh : k ≤ H.card) (hD : (H \ R).card ≤ a + 1)
    (hS : (R.erase t).card + a + 2 ≤ k) :
    t ∈ R ∧ H.card = k ∧ (H \ R).card = a + 1 ∧
      (R.erase t).card + a + 2 = k := by
  have hsplit := card_sdiff_add_card_eq_card hRH
  by_cases ht : t ∈ R
  · have herase := card_erase_add_one ht
    exact ⟨ht, by omega, by omega, by omega⟩
  · rw [erase_eq_of_notMem ht] at hS
    omega

/-- At the next endpoint, a neighborhood of size at least (k+1) still
forces the triple remote into the support and attains the boundary bound. -/
theorem support_next_endpoint [DecidableEq V]
    {R H : Finset V} {t : V} {a k : ℕ}
    (hRH : R ⊆ H) (hh : k + 1 ≤ H.card) (hD : (H \ R).card ≤ a + 1)
    (hS : (R.erase t).card + a + 2 ≤ k + 1) :
    t ∈ R ∧ H.card = k + 1 ∧ (H \ R).card = a + 1 ∧
      (R.erase t).card + a + 2 = k + 1 := by
  exact support_endpoint (k := k + 1) hRH hh hD hS

/-- A solo avoiding the triple remote sees the full boundary at either
endpoint. Its closed remote neighborhood has size at least (k). -/
theorem boundary_subset_of_solo_avoiding_triple [DecidableEq V]
    {R H U : Finset V} {t : V} {a k : ℕ}
    (hRH : R ⊆ H) (hU : U ⊆ H) (hkU : k ≤ U.card) (htU : t ∉ U)
    (hD : (H \ R).card ≤ a + 1)
    (hS : (R.erase t).card + a + 2 ≤ k + 1) :
    (H \ R).card = a + 1 ∧ H \ R ⊆ U ∧
      ((t ∈ R ∧ H.card = k + 1 ∧ U = H.erase t) ∨
        (t ∉ H ∧ H.card = k ∧ U = H)) := by
  have hsplit := card_sdiff_add_card_eq_card hRH
  have hh := card_le_card hU
  by_cases ht : t ∈ R
  · have htH := hRH ht
    have hsub : U ⊆ H.erase t := by
      intro v hv
      apply mem_erase.mpr
      exact ⟨fun he => htU (he ▸ hv), hU hv⟩
    have hle := card_le_card hsub
    have hErase := card_erase_add_one htH
    have hNext := support_next_endpoint hRH (by omega) hD hS
    have hEq : U = H.erase t := eq_of_subset_of_card_le hsub (by omega)
    refine ⟨hNext.2.2.1, ?_, Or.inl ⟨ht, hNext.2.1, hEq⟩⟩
    rw [hEq]
    intro v hv
    obtain ⟨hvH, hvR⟩ := mem_sdiff.mp hv
    exact mem_erase.mpr ⟨fun he => hvR (he.symm ▸ ht), hvH⟩
  · rw [erase_eq_of_notMem ht] at hS
    have hEq : U = H := eq_of_subset_of_card_le hU (by omega)
    have htH : t ∉ H := hEq ▸ htU
    refine ⟨by omega, ?_, Or.inr ⟨htH, by omega, hEq⟩⟩
    rw [hEq]
    exact sdiff_subset

/-- The smaller neighborhood can lose the triple remote, while the larger
neighborhood already contains it. Both leave at least (c-k-1) outsiders. -/
theorem nontriple_outsider_lower_bound [DecidableEq V]
    {L H : Finset V} {t : V} {k : ℕ} (hHL : H ⊆ L)
    (hcase : (t ∈ H ∧ H.card ≤ k + 1) ∨ H.card ≤ k) :
    L.card - k - 1 ≤ ((L \ H).erase t).card := by
  have hsplit := card_sdiff_add_card_eq_card hHL
  rcases hcase with ⟨htH, hcard⟩ | hcard
  · have ht : t ∉ L \ H := fun ht => (mem_sdiff.mp ht).2 htH
    rw [erase_eq_of_notMem ht]
    omega
  · by_cases ht : t ∈ L \ H
    · have hErase := card_erase_add_one ht
      omega
    · rw [erase_eq_of_notMem ht]
      omega

end Support

/-- For a solo that avoids the triple remote, use the boundary equalities
to discharge gate adjacency and count every nontriple outsider. -/
theorem near_endpoint_gate_contradiction [DecidableEq V]
    {p w t : V} {S R H U L N : Finset V} {a k : ℕ}
    (hRH : R ⊆ H) (hHL : H ⊆ L) (hU : U ⊆ H)
    (hkU : k ≤ U.card) (htU : t ∉ U)
    (hD : (H \ R).card ≤ a + 1)
    (hSupport : (R.erase t).card + a + 2 ≤ k + 1)
    (hwR : w ∈ R) (hAdjU : ∀ u ∈ U, u ≠ w → G.Adj w u)
    (hS : ∀ v ∈ S, G.dist p v = 2) (hcard : S.card = k)
    (hcapP : (evenBall G p).card ≤ k + 1)
    (hfar : ∀ m ∈ (L \ H).erase t, 3 ≤ G.dist p m)
    (hnear : ∀ m ∈ (L \ H).erase t, G.dist p m ≤ 4)
    (hgate : ∀ m ∈ (L \ H).erase t, ∀ u ∈ S, G.Adj u m → u ∈ H \ R)
    (hnadj : ∀ m ∈ (L \ H).erase t, ¬ G.Adj w m)
    (hN : ∀ v ∈ N, G.dist w v = 2) (hdis : Disjoint ((L \ H).erase t) N)
    (hcapW : (evenBall G w).card ≤ k + 1)
    (hfixed : a + 2 ≤ N.card) (hc : 2 * k - 3 ≤ L.card) (ha : 3 ≤ a) :
    False := by
  obtain ⟨_, hDU, hcase⟩ :=
    boundary_subset_of_solo_avoiding_triple hRH hU hkU htU hD hSupport
  have hbound : L.card - k - 1 ≤ ((L \ H).erase t).card := by
    apply nontriple_outsider_lower_bound hHL
    rcases hcase with ⟨htR, hh, _⟩ | ⟨_, hh, _⟩
    · exact Or.inl ⟨hRH htR, hh.le⟩
    · exact Or.inr hh.le
  have hsolo (u : V) (hu : u ∈ H \ R) : G.Adj w u :=
    hAdjU u (hDU hu) (fun he => (mem_sdiff.mp hu).2 (he.symm ▸ hwR))
  have hne (m : V) (hm : m ∈ (L \ H).erase t) : w ≠ m :=
    fun he => (mem_sdiff.mp (mem_erase.mp hm).2).2 (he ▸ hRH hwR)
  exact private_gate_contradiction G (e := 1) hS hcard hcapP hfar hnear hgate
    hsolo hne hnadj hN hdis hcapW hbound hfixed hc ha

#print axioms private_saturation_contradiction
#print axioms private_near_saturation_contradiction
#print axioms private_gate_contradiction
#print axioms support_endpoint
#print axioms support_next_endpoint
#print axioms boundary_subset_of_solo_avoiding_triple
#print axioms near_endpoint_gate_contradiction

end Graph189PrivateSaturation
