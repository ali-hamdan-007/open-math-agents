import Graph189MarkedCycleEntry
import Graph189MarkedRotation
import Graph189SidePathDegree

open SimpleGraph Finset
namespace Graph189ConnectedMarkedRoute
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A dense connected side supplies a long path from a mark even when its
few marked vertices are all outside the cycle obtained by rotating an
unmarked longest path. Only unmarked endpoints need the stronger degree. -/
theorem route (hc : G.Connected) (P : Finset V) (some : P.Nonempty) {d u loss : ℕ}
    (pos : 1≤d) (minimum : ∀v,d≤G.degree v) (unmarked : ∀v,v∉P → u≤G.degree v)
    (size : Fintype.card V≤2*d+1+loss) (room : Fintype.card V<2*u+P.card) :
    ∃x∈P, ∃y, ∃q : G.Walk x y,q.IsPath ∧ Fintype.card V≤q.support.length+(loss+1) := by
  classical
  obtain ⟨a,b,p,hp,longest,bound⟩ := Graph189SidePathDegree.longest_order hc pos minimum
  have near : Fintype.card V≤p.support.length+loss := by rcases bound with h|h <;> omega
  by_cases aP : a∈P
  · exact ⟨a,aP,b,p,hp,by omega⟩
  by_cases bP : b∈P
  · exact ⟨b,bP,a,p.reverse,hp.reverse,by simpa using (show Fintype.card V≤p.support.length+(loss+1) by omega)⟩
  apply Graph189MarkedRotation.from_longest_with p hp longest P near (by
    have := unmarked a aP
    have := unmarked b bP
    omega)
  intro x y r hr close enough
  obtain ⟨z,zP⟩ := some
  obtain ⟨w,t,ht,length⟩ := Graph189MarkedCycleEntry.enter hc z r hr close
  exact ⟨z,zP,w,t,ht,by omega⟩

#print axioms route
end Graph189ConnectedMarkedRoute
