import Graph189BoundaryDebit
import Graph189PrivateRepresentativeBound
import Graph189MinimumCutOrder

open Finset SimpleGraph
namespace Graph189PrivateContactProfile
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A B S : Finset V} {p q : V}

/-- A private contact on one side leaves at most k−1 contacts of
its own anchor on the other side, whether or not the two anchors touch. -/
theorem ports (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    {u : V} (ua : u∈A) (up : G.Adj u p) (uq : ¬G.Adj u q) :
    (B.filter (G.Adj p)).card+1≤G.secondSmallestDegree := by
  classical
  let X := B.filter (G.Adj p)
  have sz : S.card=2 := by simp [pair,ne]
  have supp : Graph189PortLabels.support G S u={p} := by
    ext i
    simp only [Graph189PortLabels.support,pair,mem_filter,mem_insert,mem_singleton]
    constructor
    · rintro ⟨h,e⟩
      rcases h with h|h
      · exact h
      · subst i
        exact False.elim (uq e)
    · rintro rfl
      exact ⟨Or.inl rfl,up⟩
  have h := Graph189BoundaryDebit.even_quota hc sides (fun T lt =>
    Graph189CutSides.connected_after_smaller_deletion T (lt.trans_le sc)) cap
    (show X⊆B from filter_subset _ _) ua
  have yes : X.filter (fun v => Even (G.dist u v))=X := filter_eq_self.mpr (by
    intro y hy
    obtain ⟨yb,py⟩ := mem_filter.mp hy
    rw [Graph189PortDifference.cross_two hc sides ua yb up py]
    decide)
  rw [yes,supp,sz,card_singleton] at h
  change X.card+1≤G.secondSmallestDegree
  omega

/-- Local counts used to rotate a side path to a contact of p.
The restrictions concern only the opposite side and the minimum separator. -/
theorem population (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (pair : S={p,q}) (ne : p≠q) (sc : S.card≤G.vertexConnectivity)
    (cap : ∀v,G.distEven v≤G.secondSmallestDegree+1)
    (free : ∀x∈A,¬(G.Adj x p ∧ G.Adj x q)) :
    let r := (B.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)).card
    (B.filter (fun x => ¬G.Adj p x)).card≤G.secondSmallestDegree-1+r ∧
      B.card≤2*G.secondSmallestDegree-2+r := by
  classical
  let R := B.filter (fun x => G.dist p x≠1 ∧ G.dist q x≠1)
  have contact (i : V) (si : i∈S) := (sides.contacts_of_minimum (fun T lt =>
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_le sc)) si).1
  obtain ⟨u,ua,up⟩ := contact p (by simp [pair])
  obtain ⟨v,va,vq⟩ := contact q (by simp [pair])
  have P := ports hc sides pair ne sc cap ua up (fun uq => free u ua ⟨up,uq⟩)
  have Q := ports hc sides (p:=q) (q:=p) (by simpa [Finset.pair_comm] using pair) ne.symm sc cap va vq
    (fun vp => free v va ⟨vp,vq⟩)
  have sub : B.filter (fun x => ¬G.Adj p x) ⊆ B.filter (G.Adj q)∪R := by
    intro x hx
    obtain ⟨xb,np⟩ := mem_filter.mp hx
    by_cases e : G.Adj q x
    · exact mem_union_left _ (mem_filter.mpr ⟨xb,e⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨xb,fun h => np (dist_eq_one_iff_adj.mp h),fun h => e (dist_eq_one_iff_adj.mp h)⟩)
  have remote := (card_le_card sub).trans (card_union_le _ _)
  have total := card_filter_add_card_filter_not (s:=B) (p:=G.Adj p)
  change _≤G.secondSmallestDegree-1+R.card ∧ B.card≤2*G.secondSmallestDegree-2+R.card
  constructor <;> omega

#print axioms ports
#print axioms population
end Graph189PrivateContactProfile
