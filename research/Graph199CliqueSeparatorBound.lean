import Graph199CliqueSeparator
import Graph199Incidence

namespace Graph199
open SimpleGraph Finset

/-- Under the induced-tree bound in WOWII #199, removing any clique leaves
at most one more component than the clique's order. -/
theorem clique_separator_component_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (U : Finset V) (hU : G.IsClique (U : Set V))
    (hk : 0 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
  let W := ↥((U : Set V)ᶜ)
  let K := G.induce ((U : Set V)ᶜ)
  let I := K.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  change Nat.card I ≤ _
  rw [Nat.card_eq_fintype_card]
  rcases subsingleton_or_nontrivial I with hs | hi
  · have h : Fintype.card I ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega
  let C (i : I) : Set V := Subtype.val '' i.supp
  have hCn (i : I) : (C i).Nonempty :=
    ⟨i.out.val,i.out,i.out_eq,rfl⟩
  have hCo (i : I) (x : V) (hx : x ∈ C i) : x ∉ U := by
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  have hCc (x : V) (hx : x ∉ U) : ∃ i, x ∈ C i := by
    let y : W := ⟨x,hx⟩
    exact ⟨K.connectedComponentMk y,y,rfl,rfl⟩
  have hCs {i j : I} {x y : V} (hij : i ≠ j)
      (hx : x ∈ C i) (hy : y ∈ C j) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    change K.connectedComponentMk a = i at ha
    change K.connectedComponentMk b = j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by rwa [ha,hb]
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj (show K.Adj a b from he))⟩
  obtain ⟨R,hcol,hrow,hdist⟩ := clique_separator_incidence U hU C hCn hCo hCc
    (fun he hx hy => hCs he hx hy) ht
  simpa only [Fintype.card_coe] using incidence_clique_bound R (vertexConnectivity G) hk hcol hrow hdist

/-- The catalogue's connected, nontrivial graphs have positive vertex connectivity. -/
theorem vertexConnectivity_pos_of_connected {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} (hc : G.Connected) :
    0 < vertexConnectivity G := by
  classical
  have hn : 1 < Fintype.card V := Fintype.one_lt_card
  let A : Set ℕ := {k | ∃ S : Finset V, S.card = k ∧
    (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1)}
  have he : vertexConnectivity G = sInf A := by
    unfold vertexConnectivity
    rw [if_neg hn.not_ge]
  have hA : A.Nonempty := by
    let v : V := Classical.choice hc.nonempty
    exact ⟨Fintype.card V - 1, univ.erase v, by simp, Or.inr (by simp)⟩
  by_contra! hk
  have hz : sInf A = 0 := by omega
  obtain ⟨S, hS, hcut | hcard⟩ := Nat.sInf_mem hA
  · have hs : S = ∅ := card_eq_zero.mp (hS.trans hz)
    apply hcut
    rw [hs, coe_empty, Set.compl_empty]
    exact G.induceUnivIso.connected_iff.mpr hc
  · omega

/-- Connected graphs satisfying WOWII #199's size hypothesis obey the clique
separator component condition. -/
theorem clique_separator_component_bound_of_connected {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} (hc : G.Connected)
    (U : Finset V) (hU : G.IsClique (U : Set V))
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 :=
  clique_separator_component_bound U hU (vertexConnectivity_pos_of_connected hc) ht

#print axioms clique_separator_component_bound_of_connected
#print axioms clique_separator_component_bound
end Graph199
