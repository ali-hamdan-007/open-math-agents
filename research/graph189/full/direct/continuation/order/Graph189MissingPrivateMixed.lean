import Graph189ShallowCommonOrder
import Graph189OnePortThreeCut
import Graph189CleanSideCounts
import Graph189PrivateContactProfile
import Graph189DegreeTwoOriginal
import Graph189TwoCutShallow

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189MissingPrivateMixed
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- In the shallow mixed case one missing private type leaves exactly
k−1 contacts of the other anchor, or an immediate short-order proof.
The genuine recut applies to whichever side the global selector chose. -/
theorem sizes_above_moderate (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (nBig : 3*G.secondSmallestDegree+2<Fintype.card V) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (pair : S={p,q}) (ne : p≠q)
    (connectedB : (G.induce (B:Set V)).Connected)
    (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x)
    (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (missing : ∀x∈A,G.Adj x q → G.Adj x p)
    (chosen : (∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) ∨ B.card≤A.card) :
    A.card≤G.secondSmallestDegree ∧ B.card≤2*G.secondSmallestDegree+1 := by
  classical
  let k := G.secondSmallestDegree
  have sz : S.card=2 := by simp [pair,ne]
  have two : 2≤G.vertexConnectivity := by omega
  have ps : p∈S := by simp [pair]
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have smaller (T : Finset V) (ht : T.card<2) : (G.induce {x : V | x∉T}).Connected :=
    Graph189CutSides.connected_after_smaller_deletion T (ht.trans_le two)
  obtain ⟨_,⟨y,yb,yp⟩⟩ := sides.contacts_of_minimum (fun T h => smaller T (h.trans_eq sz)) ps
  have bound := Graph189PrivateContactProfile.ports hc sides.swap pair ne sc point yb yp
    (fun yq => freeB y yb ⟨yp,yq⟩)
  let P := A.filter (G.Adj p)
  change P.card+1≤k at bound
  have all (x : V) (xa : x∈A) (port : ∃i∈S,G.Adj i x) : G.Adj x p := by
    obtain ⟨i,si,ix⟩ := port
    rcases (show i=p ∨ i=q by simpa [pair] using si) with h|h
    · exact (h ▸ ix).symm
    · exact missing x xa (h ▸ ix).symm
  have allHigh (x : V) (xa : x∈A) (high : k≤G.degree x) := all x xa (shallow x xa high)
  by_cases highA : ∃x∈A,k≤G.degree x
  swap
  · obtain ⟨z,_,degree⟩ := Graph189ShallowCommonOrder.no_high sides sc sz highA
    have h := minimum.trans (G.minDegree_le_degree z)
    omega
  have equivalent : A.filter (fun x => ∃i∈S,G.Adj i x)=P := by
    ext x
    constructor
    · intro h
      obtain ⟨xa,port⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨xa,(all x xa port).symm⟩
    · intro h
      obtain ⟨xa,px⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨xa,p,ps,px⟩
  by_cases few : P.card+2≤k
  · have h := Graph189ShallowCommonOrder.few_ports hc sides sz point shallow highA (by rwa [equivalent])
    omega
  have exactP : P.card+1=k := by omega
  have one : (A\P).card≤1 := card_le_one.mpr (by
    intro x hx y hy
    by_contra ne
    have low (v : V) (h : v∈A\P) (hi : k≤G.degree v) : False := by
      obtain ⟨va,out⟩ := mem_sdiff.mp h
      exact out (mem_filter.mpr ⟨va,(allHigh v va hi).symm⟩)
    exact (degree_pair (G:=G) x y ne).elim (low x hx) (low y hy))
  have count := card_sdiff_add_card_eq_card (show P⊆A from filter_subset _ _)
  have upperA : A.card≤k := by omega
  have lowerA : k≤A.card+1 := by
    have inA := card_le_card (show P⊆A from filter_subset _ _)
    omega
  by_cases bBig : 2*k+1<B.card
  swap
  · exact ⟨upperA,by omega⟩
  have minimal := chosen.resolve_right (show ¬B.card≤A.card by omega)
  have cut : Graph189CutSides.CutSides G A B {p,q} := pair ▸ sides
  have short := Graph189TwoCutShallow.order_bound hc (fun v => by simpa only [Nat.add_comm] using point v)
    cut ne smaller connectedB (fun x y e => Graph189CleanSideCounts.edge_triangle hc point nBig e)
    (by change 4≤k; omega) lowerA bBig exactP allHigh minimal
  change Fintype.card V≤3*k+2 at short
  omega

theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 9≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (sc : S.card≤G.vertexConnectivity) (pair : S={p,q}) (ne : p≠q)
    (connectedB : (G.induce (B:Set V)).Connected)
    (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x)
    (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (missing : ∀x∈A,G.Adj x q → G.Adj x p)
    (chosen : (∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) ∨ B.card≤A.card) :
    ∃x y, ∃r : G.Walk x y,r.IsHamiltonian := by
  classical
  have sz : S.card=2 := by simp [pair,ne]
  have conn : 2≤G.vertexConnectivity := by omega
  by_cases minimum : 3≤G.minDegree
  swap
  · obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
    have lower := Graph189CutSides.connectivity_le_degree (G:=G) z
    exact Graph189DegreeTwoOriginal.traceable hc cap conn z (by omega) (by omega)
  apply Graph189OnePortCover.below_four hc cap conn large
  by_cases big : 3*G.secondSmallestDegree+2<Fintype.card V
  swap
  · omega
  obtain ⟨a,b⟩ := sizes_above_moderate hc cap (by omega) minimum big sides sc pair ne connectedB shallow freeB missing chosen
  have cover : univ ⊆ (A∪B)∪S := by
    intro x _
    rcases sides.cover x with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
  have n := (card_le_card cover).trans (card_union_le _ _)
  rw [card_univ,sz] at n
  have ab := card_union_le A B
  omega

#print axioms sizes_above_moderate
#print axioms traceable
end Graph189MissingPrivateMixed
