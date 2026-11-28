import Graph189SmallMixedOrders
import Graph189MissingPrivateMixed

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189SmallMixedPair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V} {p q : V}

/-- When one private type is missing, a shallow side has order at most k.
The least-cut recut bounds its opposite side by 2k+1. -/
private theorem missing_orders (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V) (sides : Graph189CutSides.CutSides G A B S)
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
    have := G.minDegree_le_degree z
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
  refine ⟨upperA,?_⟩
  by_contra! bBig
  have minimal := chosen.resolve_right (show ¬B.card≤A.card by omega)
  have cut : Graph189CutSides.CutSides G A B {p,q} := pair ▸ sides
  have short := Graph189TwoCutShallow.order_bound hc (fun v => by simpa only [Nat.add_comm] using point v)
    cut ne smaller connectedB (fun x y e => Graph189CleanSideCounts.edge_triangle hc point big e)
    (by change 4≤k; omega) lowerA bBig exactP allHigh minimal
  change Fintype.card V≤3*k+2 at short
  omega

private theorem missing_small (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (minimum : 3≤G.minDegree) (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (ne : p≠q) (nonadj : ¬G.Adj p q)
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x)
    (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q)) (missing : ∀x∈A,G.Adj x q → G.Adj x p)
    (chosen : (∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) ∨ B.card≤A.card) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  obtain ⟨a,b⟩ := missing_orders hc cap large minimum big sides sc pair ne conB shallow free missing chosen
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  let P := B.filter (G.Adj p)
  let Q := B.filter (G.Adj q)
  have mp : 2≤P.card := Graph189BalancedPair.two_contacts hc point sides.swap sc pair nonadj big
  have mq : 2≤Q.card := Graph189BalancedPair.two_contacts hc point sides.swap sc (pair.trans (Finset.pair_comm _ _)) (fun e => nonadj e.symm) big
  have apart : Disjoint P Q := disjoint_left.mpr (fun {v} hp hq =>
    free v (mem_filter.mp hp).1 ⟨(mem_filter.mp hp).2.symm,(mem_filter.mp hq).2.symm⟩)
  have sub : P∪Q⊆ports G B S := by
    intro x h
    rcases mem_union.mp h with hp|hq
    · exact mem_filter.mpr ⟨(mem_filter.mp hp).1,p,by simp [pair],(mem_filter.mp hp).2⟩
    · exact mem_filter.mpr ⟨(mem_filter.mp hq).1,q,by simp [pair],(mem_filter.mp hq).2⟩
  have four := card_le_card sub
  rw [card_union_of_disjoint apart] at four
  have n := total sides (by simp [pair,ne])
  apply mixed hc cap large minimum big (by omega) sides pair ne sc nonadj free conA conB
  · exact Or.inr ⟨by omega,by omega⟩
  · omega

/-- The entire shallow one-common case of the selected nonadjacent separating
pair, through all remaining second degrees seven through nine. -/
theorem shallow_from_seven (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7≤G.secondSmallestDegree) (small : G.secondSmallestDegree≤10) (minimum : 3≤G.minDegree)
    (big : 3*G.secondSmallestDegree+2<Fintype.card V)
    (sides : Graph189CutSides.CutSides G A B S) (sc : S.card≤G.vertexConnectivity)
    (pair : S={p,q}) (ne : p≠q) (nonadj : ¬G.Adj p q)
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected)
    (shallow : ∀x∈A,G.secondSmallestDegree≤G.degree x → ∃i∈S,G.Adj i x)
    (common : ∃x∈A,∀i∈S,G.Adj x i) (free : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (chosen : (∀ C D T, Graph189CutSides.CutSides G C D T → T.card=2 → A.card≤C.card) ∨ B.card≤A.card) :
    ∃u v, ∃r : G.Walk u v,r.IsHamiltonian := by
  classical
  by_cases qOnly : ∃x∈A,G.Adj x q ∧ ¬G.Adj x p
  swap
  · exact missing_small hc cap large minimum big sides sc pair ne nonadj conA conB shallow free
      (fun x xa xq => by by_contra xp; exact qOnly ⟨x,xa,xq,xp⟩) chosen
  by_cases pOnly : ∃x∈A,G.Adj x p ∧ ¬G.Adj x q
  swap
  · exact missing_small hc cap large minimum big sides sc (pair.trans (Finset.pair_comm _ _)) ne.symm
      (fun e => nonadj e.symm) conA conB shallow (fun x xb h => free x xb h.symm)
      (fun x xa xp => by by_contra xq; exact pOnly ⟨x,xa,xp,xq⟩) chosen
  by_cases wide : 2*G.secondSmallestDegree≤B.card
  · exact large_shallow hc cap large small minimum big sides pair ne sc nonadj free conA conB shallow wide common pOnly qOnly
  let k := G.secondSmallestDegree
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  let R := A.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)
  have small : R.card≤1 := card_le_one.mpr (by
    intro x hx y hy
    by_contra diff
    have low {w : V} (hr : w∈R) (hi : k≤G.degree w) : False := by
      obtain ⟨wa,wp,wq⟩ := mem_filter.mp hr
      obtain ⟨i,si,iw⟩ := shallow w wa hi
      have d := dist_eq_one_iff_adj.mpr iw
      rcases (show i=p ∨ i=q by simpa [pair] using si) with eq|eq
      · exact wp (eq ▸ d)
      · exact wq (eq ▸ d)
    exact (degree_pair (G:=G) x y diff).elim (low hx) (low hy))
  obtain ⟨_,other⟩ := Graph189PrivateContactProfile.population hc sides.swap pair ne sc point free
  change A.card≤2*k-2+R.card at other
  apply balanced hc cap large minimum big sides pair ne sc nonadj free conA conB
  · change A.card+1≤2*k
    change 7≤k at large
    omega
  · omega

#print axioms shallow_from_seven
end Graph189SmallMixedPair
