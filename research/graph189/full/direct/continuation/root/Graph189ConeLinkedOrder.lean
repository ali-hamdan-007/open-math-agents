import Graph189BondyOrder
import Graph189MinimumOrderViaCycles
import Graph189CompletionLinked

namespace Graph189ConeLinkedOrder
open SimpleGraph Finset Graph189ExteriorDegreeCycle Graph189UniversalCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Order estimate from the accepted upstream linked-set theorem applied to a
longest cycle of a genuine graph. The supplied degree lower bound may be weaker
than the minimum degree of the completion. -/
theorem order (K : SimpleGraph V) [DecidableRel K.Adj] (r : V) {l d : ℕ}
    (two : 2≤l) (lower : l≤d) (minimum : d≤K.minDegree) (conn : l≤K.vertexConnectivity)
    (witness : ∀ a, ∀ C : K.Walk a a, C.IsCycle →
       (∀ v (R : K.Walk v v), R.IsCycle → R.length≤C.length) →
       Graph189LinkedExterior.Linked (K.induce {v : V | v∉C.support}) l) :
    (l+1)*(d-l+2)-1≤Fintype.card V := by
  classical
  obtain ⟨u,R,hR,_⟩ := cycle_of_degree (G:=K) r (d:=2) (by decide)
    (fun v => two.trans (lower.trans (minimum.trans (K.minDegree_le_degree v))))
  obtain ⟨a,C,hC,longest⟩ := exists_longest_cycle K ⟨u,R,hR⟩
  have h := OMA.BondyK.graph189_order_of_linked (by omega : 1≤l) (lower.trans minimum)
    (fun T small => Graph189CutSides.connected_after_smaller_deletion T (small.trans_le conn))
    C hC longest (witness a C hC longest)
  have monotone := Nat.mul_le_mul_left (l+1)
    (show d-l+2≤K.minDegree-l+2 by omega)
  omega

theorem minimum (w : V) (minw : G.degree w=G.minDegree)
    (notTrace : ¬∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬∃ a b, ∃ p : (G.induce {x : V | x≠w}).Walk a b,p.IsHamiltonian)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree)
    {l : ℕ} (which : l=G.vertexConnectivity ∨ l=G.vertexConnectivity+1)
    (conn : l≤(completeAt G w).vertexConnectivity) :
    (l+1)*(G.secondSmallestDegree-l+2)-1≤Fintype.card V := by
  apply order (completeAt G w) w (by rcases which with eq|eq <;> omega)
    (by rcases which with eq|eq <;> omega) (secondDegree_le_completeAt_minDegree (G:=G) w minw) conn
  intro a C hc longest
  rcases which with eq|eq
  · subst l
    exact Graph189CompletionLinked.minimum w minw C hc longest notTrace notH cap hs hk ratio
  · subst l
    exact Graph189CompletionLinked.minimum_lift w minw C hc longest notTrace notH cap hs hk ratio

theorem critical (notTrace : ¬∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree)
    (room : G.vertexConnectivity<Fintype.card V-1)
    (critical : 3*G.vertexConnectivity<2*(G.minDegree+1))
    (enough : G.secondSmallestDegree+2*G.vertexConnectivity+2≤2*G.minDegree) :
    (G.vertexConnectivity+2)*(G.minDegree-(G.vertexConnectivity+1)+2)-1≤Fintype.card V := by
  classical
  obtain ⟨w,conn⟩ := Graph189CriticalConnectivity.exists_completion room critical
  apply order (completeAt G w) w (l:=G.vertexConnectivity+1) (by omega) (by omega)
    (minDegree_le_completeAt (G:=G) w) conn
  exact fun _ C hc max => Graph189CompletionLinked.critical w C hc max notTrace cap hs hk ratio enough

#print axioms minimum
#print axioms critical
end Graph189ConeLinkedOrder
