import Graph189FourCutCommon
import Graph189TwoRootRecut
import Graph189ResidualTerminal
import Graph189MissingLabels
import Graph189GraphPopulation
import Graph189FullLabelExit
import Graph189LowConnectivityLift
import Graph189MinimumDeletionReplay

open Finset SimpleGraph
namespace Graph189FourCut
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A qualifying graph of vertex connectivity four satisfies both explicit
order cutoffs, regardless of traceability or the number of components. -/
theorem exclude (hc : G.Connected) (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (four : G.vertexConnectivity=4)
    (region : Range G.secondSmallestDegree (Fintype.card V)) : False := by
  classical
  let k := G.secondSmallestDegree
  let H (P : Finset V) := P.filter (fun v => k ≤ G.degree v)
  let core (P T : Finset V) := T.filter (fun i => ∀ a ∈ P, k ≤ G.degree a → G.Adj a i)
  have bigOrder : 4*k+5 ≤ Fintype.card V := by
    rcases region with ⟨hg,hn⟩|⟨hg,hn⟩ <;> dsimp only [k] <;> omega
  have hk26 : 26≤k := by
    rcases region with ⟨hg,_⟩|⟨hg,_⟩ <;> dsimp only [k] <;> omega
  have room : G.vertexConnectivity < Fintype.card V-1 := by omega
  have uniform {W F T : Finset V} (cut : Graph189CutSides.CutSides G W F T)
      (eq : T.card = G.vertexConnectivity) (small : (H W).card ≤ (H F).card) :
      2 ≤ (core W T).card :=
    (two_common hc cut deletion eq (eq.trans four) cap small region).2.2
  have allTwo (W F T : Finset V) (cut : Graph189CutSides.CutSides G W F T)
      (eq : T.card = G.vertexConnectivity) (small : (H W).card ≤ (H F).card)
      (y : V) (yw : y ∈ W) (yh : k ≤ G.degree y) : 2 ≤ (T.filter (G.Adj y)).card := by
    have sub : core W T ⊆ T.filter (G.Adj y) := by
      intro i hi
      obtain ⟨it,common⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨it,common y yw yh⟩
    have sz := uniform cut eq small
    have b := card_le_card sub
    omega
  obtain ⟨U,F,S,minimum,sides⟩ := Graph189GraphPopulation.minimum_sides (G:=G) room
  have select : ∃ A B : Finset V, Graph189CutSides.CutSides G A B S ∧ (H A).card ≤ (H B).card := by
    rcases le_total (H U).card (H F).card with h | h
    · exact ⟨U,F,sides,h⟩
    · exact ⟨F,U,sides.swap,h⟩
  obtain ⟨A,B,cut,orient⟩ := select
  let C := core A S
  have cs : C ⊆ S := filter_subset _ _
  have c2 : 2 ≤ C.card := uniform cut minimum orient
  have ns : S.card=4 := minimum.trans four
  have ss : 2 ≤ S.card := by omega
  have small (T : Finset V) (lt : T.card < S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have common (a : V) (aa : a ∈ A) (ah : k ≤ G.degree a) (j : V) (jc : j ∈ C) :=
    (mem_filter.mp jc).2 a aa ah
  obtain ⟨big,order,_⟩ := two_common hc cut deletion minimum ns cap orient region
  have cap' (v : V) : G.distEven v ≤ k+1 := by simpa [k,Nat.add_comm] using cap v
  have contact {j : V} (js : j∈S) : ∃ a∈A, k≤G.degree a ∧ G.Adj a j :=
    Graph189HighLabel.all_labels_in_order_range hc cut deletion small cap'
      (big.trans_le (card_le_card (filter_subset _ _))) order js
  obtain ⟨i,ic⟩ := card_pos.mp (show 0<C.card by omega)
  by_cases full : ∃ a ∈ A, k≤G.degree a ∧ ∀ j ∈ S, G.Adj a j
  · obtain ⟨a,aa,ah,whole⟩ := full
    obtain ⟨j,_,b,hb,bh,support,many⟩ := Graph189FullLabelExit.full_exit hc cut cap' ss big aa ah whole
      (cs ic) (fun v va vh => common v va vh i ic)
    exact private_recut hc cut minimum cap (by omega) hb bh support many allTwo
  push Not at full
  have each (j : V) (js : j∈S) : ∃ x∈H A, G.Adj x j := by
    obtain ⟨x,xa,xh,edge⟩ := contact js
    exact ⟨x,mem_filter.mpr ⟨xa,xh⟩,edge⟩
  obtain ⟨a,ax,_⟩ := each i (cs ic)
  have notFull (x : V) (hx : x ∈ H A) : ¬∀ j ∈ S, G.Adj x j := by
    obtain ⟨j,js,lack⟩ := full x (mem_filter.mp hx).1 (mem_filter.mp hx).2
    exact fun all => lack (all j js)
  have two := Graph189MissingLabels.two_residual (show (H A).Nonempty from ⟨a,ax⟩) each
    (fun x hx => common x (mem_filter.mp hx).1 (mem_filter.mp hx).2) notFull
  have part := card_sdiff_add_card_eq_card cs
  have dd : (S \ C).card=2 := by omega
  have cc : C.card=2 := by omega
  have singles (x : V) (xa : x∈A) (xh : k≤G.degree x) :
      (Graph189PortLabels.support G S x \ C).card≤1 :=
    Graph189MissingLabels.at_most_one (common x xa xh) (notFull x (mem_filter.mpr ⟨xa,xh⟩)) (by omega)
  have privatePort : ∃ j∈C, ∃ v∈B, k≤G.degree v ∧ S.filter (G.Adj v)={j} := by
    by_contra absent
    have bound := Graph189ResidualPrivatePort.absent_bound hc cut C cs two cap'
      (fun j hj => contact (mem_sdiff.mp hj).1) common singles absent
    change 2*(H B).card ≤ (2*(S \ C).card+C.card)*k+(H A).card+(S \ C).card*(C.card+1) at bound
    obtain ⟨v,vb,vi⟩ := (cut.contacts_of_minimum small (cs ic)).2
    have xb := Graph189PortDifference.common_label_capacity hc cut (X:=H A) (filter_subset _ _)
      (fun a ha => common a (mem_filter.mp ha).1 (mem_filter.mp ha).2 i ic) vb vi cap'
    have hk : 6≤k := by rcases region with ⟨hg,hn⟩|⟨hg,hn⟩ <;> dsimp only [k] <;> omega
    change S.card*k<(H B).card at big
    rw [ns] at big
    rw [dd,cc] at bound
    omega
  obtain ⟨j,jc,v,vb,vh,support⟩ := privatePort
  obtain ⟨t,ts,missing⟩ := full a (mem_filter.mp ax).1 (mem_filter.mp ax).2
  have cnt := Graph189ResidualPrivatePort.missing_label_population cut
    (mem_filter.mp ax).1 (mem_filter.mp ax).2 ts missing
  have many := Graph189CutSides.CutSides.common_label_contacts
    (fun x xa xh => common x xa xh j jc) cnt
  exact private_recut hc cut minimum cap (by omega) vb vh support many allTwo

#print axioms exclude
end Graph189FourCut

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189FourCut

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The four-cut upper-order bound and the minimum-deletion lower-order
bound prove the original statement at connectivity four and degree at least 33. -/
theorem traceable_of_33 (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (four : G.vertexConnectivity=4) (large : 33≤G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have least : G.degree z=G.minDegree := hz.symm
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  by_contra fail
  by_cases near : ∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b,p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := near
    have d4 := Graph189RootedSplice.connectivity_le_degree (G:=G) z
    exact fail (Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion hc cap
      (by omega) z least (by omega) p hp)
  · obtain ⟨u,ne⟩ := exists_ne z
    have size : G.secondSmallestDegree<Fintype.card V := by
      rcases degree_pair (G:=G) u z ne with h|h
      · exact lt_of_le_of_lt h (G.degree_lt_card_verts u)
      · exact lt_of_le_of_lt h (G.degree_lt_card_verts z)
    have lower := Graph189LowConnectivityLift.minimum_deletion hc z least
      (by omega) (by omega) (by omega) (Or.inr (by omega)) point (by omega) fail near
    rw [four] at lower
    have lowerN : 6*G.secondSmallestDegree≤Fintype.card V+19 := by norm_num at lower; omega
    have lowerZ : 6*(G.secondSmallestDegree:ℤ)≤(Fintype.card V:ℤ)+19 := by exact_mod_cast lowerN
    have largeZ : (33:ℤ)≤G.secondSmallestDegree := by exact_mod_cast large
    have deletion (u : V) : (G.induce {v : V | v≠u}).Connected := by
      have eq : {v : V | v∉({u} : Finset V)} = {v : V | v≠u} := by
        ext v
        simp
      rw [←eq]
      exact Graph189CutSides.connected_after_smaller_deletion ({u} : Finset V) (by simp [four])
    exact exclude hc (fun v => by simpa only [Nat.add_comm 1] using point v) deletion four
      (Or.inr ⟨largeZ,by omega⟩)

/-- The original all-order threshold for connectivity four. -/
theorem traceable_of_36 (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (four : G.vertexConnectivity=4) (large : 36≤G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian :=
  traceable_of_33 hc cap four (by omega)

/-- The original all-order threshold for connectivity four. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (four : G.vertexConnectivity=4) (large : 37≤G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian :=
  traceable_of_36 hc cap four (by omega)

#print axioms traceable_of_33
#print axioms traceable_of_36
#print axioms traceable
end Graph189FourCut
