import Graph189CleanPairOrder
import Graph189PrivateContactProfile
import Graph189CleanSideRoute
import Graph189TwoSoleNearest
import Graph189OnePortThreeCut
import Graph189OrdinaryOmission

open Finset SimpleGraph Graph189DenseSideRoute
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189CleanPrivatePair
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

/-- The clean case of the two common-free sides in the original
separating-pair paper, at all orders for k≥26 and with any low vertex. -/
theorem traceable (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 26≤G.secondSmallestDegree) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (clean : Graph189CleanSideCounts.Clean G A p q) (freeB : ∀x∈B,¬(G.Adj x p ∧ G.Adj x q))
    (conA : (G.induce (A:Set V)).Connected) (conB : (G.induce (B:Set V)).Connected) :
    ∃u v, ∃w : G.Walk u v,w.IsHamiltonian := by
  classical
  by_contra bad
  let k := G.secondSmallestDegree
  let R (W : Finset V) := (W.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card
  have size : S.card=2 := by simp [pair,ne]
  have conn : 2≤G.vertexConnectivity := size ▸ sc
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  have lower : 4*k≤Fintype.card V+5 := by
    by_cases higher : 3≤G.vertexConnectivity
    · have h := Graph189RotationLinked.base_order bad point (l:=3) (by decide) higher (by omega)
      change 4*(k-3+2)≤Fintype.card V+1 at h
      change 26≤k at large
      omega
    · have eq : G.vertexConnectivity=2 := by omega
      have h := Graph189OnePortCover.additional_index hc cap conn (by rw [eq]; omega) bad
      rw [eq] at h
      change 4*(k-3+2)≤Fintype.card V+1 at h
      change 26≤k at large
      omega
  change 26≤k at large
  have up := Graph189CleanPairOrder.nonport_order hc point sides pair ne sc
    (by change 3*k+2<Fintype.card V; omega) clean
  change Fintype.card V+R A+R B+_ ≤4*k+2 at up
  have few : R A+R B≤7 := by omega
  obtain ⟨missA,ordA⟩ := Graph189PrivateContactProfile.population hc sides.swap pair ne sc point freeB
  obtain ⟨missB,ordB⟩ := Graph189PrivateContactProfile.population hc sides pair ne sc point clean.private_ports
  change (A.filter (fun x => ¬G.Adj p x)).card≤k-1+R A at missA
  change (B.filter (fun x => ¬G.Adj p x)).card≤k-1+R B at missB
  change A.card≤2*k-2+R A at ordA
  change B.card≤2*k-2+R B at ordB
  have all : (univ : Finset V)⊆(A∪B)∪S := by
    intro x _
    rcases sides.cover x with h|h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ h
  have total := (card_le_card all).trans (card_union_le _ _)
  rw [card_univ,size] at total
  have sum := card_union_le A B
  have countsA := card_filter_add_card_filter_not (s:=A) (p:=G.Adj p)
  have countsB := card_filter_add_card_filter_not (s:=B) (p:=G.Adj p)
  have marksA : 4≤(A.filter (G.Adj p)).card := by omega
  have marksB : 4≤(B.filter (G.Adj p)).card := by omega
  have getHigh {X Y : Finset V} (cut : Graph189CutSides.CutSides G X Y S)
      (free : ∀x∈X,¬(G.Adj x p ∧ G.Adj x q)) (con : (G.induce (X:Set V)).Connected)
      (ord : X.card≤2*k-2+R X) (marks : 4≤(X.filter (G.Adj p)).card)
      (miss : (X.filter (fun x => ¬G.Adj p x)).card≤k-1+R X) (rx : R X≤7)
      (high : ∀x∈X,k≤G.degree x) : Route G X p (2*R X+1) :=
    Graph189CleanSideRoute.high_route X p large rx con (fun v => by
      have := Graph189CleanSideRoute.loss cut pair free v
      have := high v.val v.property
      omega) ord marks miss
  have getLow {X Y : Finset V} (cut : Graph189CutSides.CutSides G X Y S)
      (free : ∀x∈X,¬(G.Adj x p ∧ G.Adj x q)) (con : (G.induce (X:Set V)).Connected)
      (ord : X.card≤2*k-2+R X) (marks : 4≤(X.filter (G.Adj p)).card)
      (miss : (X.filter (fun x => ¬G.Adj p x)).card≤k-1+R X) (rx : R X≤7)
      {z : V} (za : z∈X) (low : G.degree z<k) : Route G X p (2*R X+3) :=
    Graph189CleanSideRoute.low_route X p large rx con za (fun v diff => by
      have := Graph189CleanSideRoute.loss cut pair free v
      have high := (degree_pair (G:=G) v.val z diff).resolve_right (not_le.mpr low)
      change k≤G.degree v.val at high
      omega) ord marks miss
  have join {a b : ℕ} (la : Route G A p a) (lb : Route G B p b) (budget : a+b≤18) : False := by
    obtain ⟨x,y,w,hw,near⟩ := Graph189TwoSoleNearest.join_routes sides (show p∈S by simp [pair]) la lb
    rw [size] at near
    exact bad (Graph189OrdinaryOmission.traceable_of_near hc cap conn large w hw (by
      change Fintype.card V≤w.support.length+k+1-(k+2)/4
      omega))
  by_cases highA : ∀ x∈A,k≤G.degree x
  · have la := getHigh sides clean.private_ports conA ordA marksA missA (by omega) highA
    by_cases highB : ∀ x∈B,k≤G.degree x
    · exact join la (getHigh sides.swap freeB conB ordB marksB missB (by omega) highB) (by omega)
    push_neg at highB
    obtain ⟨z,zb,low⟩ := highB
    exact join la (getLow sides.swap freeB conB ordB marksB missB (by omega) zb low) (by omega)
  push_neg at highA
  obtain ⟨z,za,low⟩ := highA
  have highB (x : V) (xb : x∈B) : k≤G.degree x := (degree_pair (G:=G) x z
    (fun eq => Finset.disjoint_left.mp sides.apart za (eq ▸ xb))).resolve_right (not_le.mpr low)
  exact join (getLow sides clean.private_ports conA ordA marksA missA (by omega) za low)
    (getHigh sides.swap freeB conB ordB marksB missB (by omega) highB) (by omega)

#print axioms traceable
end Graph189CleanPrivatePair
