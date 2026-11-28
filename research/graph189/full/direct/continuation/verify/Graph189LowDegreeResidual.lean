import Graph189R1Metric
import Graph189LowDegreeTwo

namespace Graph189LowDegreeResidual
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Deleting a single vertex cannot disconnect the graph, so every nonzero
intermediate distance layer contains at least two vertices. -/
theorem two_in_layer (hc : G.Connected)
    (uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected)
    {x y : V} {l : ℕ} (pos : 0 < l) (far : l < G.dist x y) :
    2 ≤ (univ.filter (fun v => G.dist x v = l)).card := by
  classical
  let L := univ.filter (fun v => G.dist x v = l)
  obtain ⟨walk,hlen⟩ := hc.exists_walk_length_eq_dist x y
  let z := walk.getVert l
  have hz : G.dist x z = l := by
    simpa [z] using geodesic hc walk hlen 0 l (by omega) (by omega)
  by_contra! small
  change L.card < 2 at small
  have lone : L.card ≤ 1 := by omega
  have xz : x ≠ z := by
    intro eq
    have h0 : G.dist x z = 0 := by rw [← eq]; simp
    omega
  have yz : y ≠ z := by
    intro eq
    have hh := congrArg (G.dist x) eq
    omega
  let x' : {v : V // v ≠ z} := ⟨x,xz⟩
  let y' : {v : V // v ≠ z} := ⟨y,yz⟩
  let U : Set {v : V // v ≠ z} := {v | G.dist x v.val < l}
  have xi : x' ∈ U := by change G.dist x x < l; simpa using pos
  have yo : y' ∉ U := by change ¬ G.dist x y < l; omega
  obtain ⟨p⟩ := uncut z x' y'
  obtain ⟨d,_,hin,hout⟩ := p.exists_boundary_dart U xi yo
  have adj : G.Adj d.fst.val d.snd.val := d.adj
  have h1 : G.dist x d.fst.val < l := hin
  have h2 : ¬ G.dist x d.snd.val < l := hout
  have h3 := hc.dist_triangle (u := x) (v := d.fst.val) (w := d.snd.val)
  rw [dist_eq_one_iff_adj.mpr adj] at h3
  have hL : d.snd.val ∈ L := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hZ : z ∈ L := mem_filter.mpr ⟨mem_univ _,hz⟩
  exact d.snd.property (card_le_one.mp lone _ hL _ hZ)

/-- A graph which stays connected after deletion of any vertex and has at most
two other vertices at positive even distance from each vertex has diameter at most three. -/
theorem diam_le_three (hc : G.Connected)
    (uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected)
    (cap : ∀ v, G.distEven v ≤ 3) : G.diam ≤ 3 := by
  classical
  let : Nonempty V := hc.nonempty
  by_contra! hgt
  obtain ⟨x,y,hxy⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  let w := p.getVert 4
  have hw : G.dist x w = 4 := by
    simpa [w] using geodesic hc p hp 0 4 (by decide) (by omega)
  let L := univ.filter (fun z => G.dist x z = 2)
  have big : 2 ≤ L.card := two_in_layer hc uncut (x := x) (y := y) (by decide) (by omega)
  have wout : w ∉ L := by simp [L,hw]
  have xw : x ≠ w := by
    intro eq
    have h0 : G.dist x w = 0 := by rw [← eq]; simp
    omega
  have xout : x ∉ insert w L := by simp [L,xw]
  have sub : insert x (insert w L) ⊆ univ.filter (fun z => Even (G.dist x z)) := by
    intro z hz
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hz with rfl | h
    · simp
    · rcases mem_insert.mp h with rfl | member
      · rw [hw]; decide
      · rw [(mem_filter.mp member).2]; decide
  have bound := card_le_card sub
  rw [card_insert_of_notMem xout, card_insert_of_notMem wout] at bound
  change _ ≤ G.distEven x at bound
  have := cap x
  omega

variable [Nontrivial V] [DecidableRel G.Adj]

/-- All remaining two-connected low-degree graphs in the registered parent
reduction. The parent already supplies the smaller orders and cut-vertex case. -/
theorem low_degree_residual (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected)
    (hlarge : 2*G.secondSmallestDegree+3 ≤ Fintype.card V)
    (hk : G.secondSmallestDegree ≤ 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let ds := G.degreeSequence
  have len : 1 < ds.length := by simpa [ds,degreeSequence] using Fintype.one_lt_card (α := V)
  have mem : G.secondSmallestDegree ∈ ds := by
    change ds.getD 1 0 ∈ ds
    cases h : ds with
    | nil => simp [h] at len
    | cons a t =>
      cases h' : t with
      | nil => simp [h,h'] at len
      | cons b t => simp
  have hm : G.secondSmallestDegree ∈ univ.val.map (fun v : V => G.degree v) := by
    simpa [ds,degreeSequence] using mem
  obtain ⟨z,_,hz⟩ := Multiset.mem_map.mp hm
  have hmin : G.minDegree ≤ G.secondSmallestDegree := hz ▸ G.minDegree_le_degree z
  have cap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hcap
  have order := order_bound hc cap
  have k2 : G.secondSmallestDegree = 2 := by
    by_contra! hn
    have ub : (G.minDegree+1)*(G.secondSmallestDegree+1) ≤ (G.secondSmallestDegree+1)*2 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have min2 : G.minDegree = 2 := by
    rw [k2] at order hmin
    omega
  exact Graph189LowDegreeTwo.traceable_min_two_sigma_two hc
    (diam_le_three hc uncut (fun v => by have hh := cap v; omega))
    min2 k2 (by omega) hcap

#print axioms two_in_layer
#print axioms diam_le_three
#print axioms low_degree_residual
end Graph189LowDegreeResidual
