import Graph189ResidualPrivateExists
import Graph189PrivatePortBand

namespace Graph189ResidualPrivatePort
open Finset SimpleGraph Graph189FiniteDomain
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V}

/-- A high vertex missing a separator neighbor gives the extra unit needed
to avoid the tight lower endpoint of the smaller high population. -/
theorem missing_label_population (sides : Graph189CutSides.CutSides G A B S)
    {a i : V} (ha : a ∈ A) (hh : G.secondSmallestDegree ≤ G.degree a)
    (hi : i ∈ S) (miss : ¬ G.Adj a i) :
    G.secondSmallestDegree+1 ≤ S.card+(A.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card := by
  classical
  let X := A.filter (fun y => G.secondSmallestDegree ≤ G.degree y)
  let L := A.filter (fun y => ¬ G.secondSmallestDegree ≤ G.degree y)
  have lows : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra neq
    exact (degree_pair (G := G) u v neq).elim (mem_filter.mp hu).2 (mem_filter.mp hv).2
  have parts : X.card+L.card=A.card :=
    A.card_filter_add_card_filter_not (fun y => G.secondSmallestDegree ≤ G.degree y)
  have sub : G.neighborFinset a ⊆ A.erase a ∪ S.erase i := by
    intro y hy
    have ay := (G.mem_neighborFinset _ _).mp hy
    rcases sides.cover y with ya | yb | ys
    · exact mem_union_left _ (mem_erase.mpr ⟨ay.ne.symm,ya⟩)
    · exact (sides.no_cross a ha y yb ay).elim
    · exact mem_union_right _ (mem_erase.mpr ⟨fun e => miss (e ▸ ay),ys⟩)
  have degree := (card_le_card sub).trans (card_union_le _ _)
  rw [G.card_neighborFinset_eq_degree] at degree
  have := card_erase_add_one ha
  have := card_erase_add_one hi
  change _ ≤ S.card+X.card
  omega

/-- Genuine final contradiction for the residual-singleton branch of a
terminal band, including the contact and degree conditions for the second cut. -/
theorem terminal_of_missing_label (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ y, G.distEven y ≤ 1+G.secondSmallestDegree)
    (minimum : S.card = G.vertexConnectivity) {r : Band} (ok : valid r = true)
    (rs : r.s = (S.card : ℤ)) (rk : r.k = (G.secondSmallestDegree : ℤ))
    (order : r.low ≤ (Fintype.card V : ℤ))
    (C : Finset V) (cs : C ⊆ S) (three : 3 ≤ C.card) (two : 2 ≤ (S \ C).card)
    (contacts : ∀ i ∈ S \ C, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (common : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → ∀ i ∈ C, G.Adj a i)
    (single : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a \ C).card ≤ 1)
    (missing : ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ ∃ j ∈ S, ¬ G.Adj a j)
    (big : S.card*G.secondSmallestDegree <
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    (uniform : ∀ W F T : Finset V, Graph189CutSides.CutSides G W F T → T.card = G.vertexConnectivity →
      (W.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card ≤
      (F.filter (fun y => G.secondSmallestDegree ≤ G.degree y)).card →
      ∀ y ∈ W, G.secondSmallestDegree ≤ G.degree y → 2 ≤ (T.filter (G.Adj y)).card) : False := by
  classical
  let D := S \ C
  obtain ⟨a,ha,ah,t,ts,at'⟩ := missing
  have bound : 2*D.card ≤ G.secondSmallestDegree := by
    have good := ok
    simp only [valid,decide_eq_true_eq] at good
    obtain ⟨hs,hd,_⟩ := good
    rw [rs] at hs hd
    rw [rk] at hd
    have ds : D.card ≤ S.card := card_le_card sdiff_subset
    omega
  have smaller (T : Finset V) (lt : T.card < S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G := G) T (lt.trans_eq minimum)
  obtain ⟨i,ic,v,hv,vh,private'⟩ := private_exists hc sides smaller C cs three two bound
    (fun y => by simpa only [Nat.add_comm 1] using cap y)
    contacts common single big
  have pop := missing_label_population sides ha ah ts at'
  exact sides.private_port_terminal_band hc cap minimum ok rs rk order uniform hv vh private'
    (Graph189CutSides.CutSides.common_label_contacts (fun x hx hh => common x hx hh i ic) pop)

#print axioms missing_label_population
#print axioms terminal_of_missing_label
end Graph189ResidualPrivatePort
