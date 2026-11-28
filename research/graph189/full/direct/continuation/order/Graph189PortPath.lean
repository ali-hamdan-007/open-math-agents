import Graph189SmallRoot
import Graph189PrescribedBatch
import Mathlib.Order.Interval.Finset.Nat

open SimpleGraph Finset
namespace Graph189PortPath
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- In a traceable graph some path starts at a marked vertex and loses at
most half of the unmarked vertices. -/
theorem from_port {a b : V} (p : G.Walk a b) (hp : p.IsHamiltonian)
    (P : Finset V) (port : P.Nonempty) :
    ∃ x∈P, ∃ y, ∃ q : G.Walk x y, q.IsPath ∧
      Fintype.card V≤q.support.length+(Fintype.card V-P.card)/2 := by
  classical
  let n := Fintype.card V
  let h := (n-P.card)/2
  have len := hp.length_support
  have len' := p.length_support
  change p.support.length=n at len
  have position (x : P) : ∃ i, p.getVert i=x.val ∧ i≤p.length :=
    Walk.mem_support_iff_exists_getVert.mp (hp.mem_support x.val)
  choose atPort val inRange using position
  have near : ∃ x : P, atPort x ≤ h ∨ p.length ≤ atPort x+h := by
    by_contra! far
    let emb : P ↪ ℕ := ⟨atPort,fun a b eq => Subtype.ext
      ((val a).symm.trans ((congrArg p.getVert eq).trans (val b)))⟩
    have sub : (univ : Finset P).map emb ⊆ Icc (h+1) (p.length-h-1) := by
      intro i hi
      obtain ⟨x,_,rfl⟩ := mem_map.mp hi
      obtain ⟨l,r⟩ := far x
      apply mem_Icc.mpr
      change h+1≤atPort x ∧ atPort x≤p.length-h-1
      omega
    have count := card_le_card sub
    rw [card_map,card_univ,Fintype.card_coe,Nat.card_Icc] at count
    have nonzero := port.card_pos
    dsimp [h] at count
    omega
  obtain ⟨x,left|right⟩ := near
  · refine ⟨p.getVert (atPort x),(val x).symm ▸ x.property,_,p.drop (atPort x),hp.isPath.drop _,?_⟩
    rw [Walk.length_support,Walk.drop_length]
    change n≤p.length-atPort x+1+h
    omega
  · refine ⟨p.getVert (atPort x),(val x).symm ▸ x.property,_,(p.take (atPort x)).reverse,
      (hp.isPath.take _).reverse,?_⟩
    rw [Walk.length_support,Walk.length_reverse,Walk.take_length,Nat.min_eq_left (inRange x)]
    change n≤atPort x+1+h
    omega

/-- The usual Ore traceability threshold for a graph of positive order
and at least two vertices. -/
theorem of_degree [DecidableRel G.Adj] [Nontrivial V] {d : ℕ}
    (min : ∀ v, d≤G.degree v) (order : Fintype.card V≤2*d+1) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  apply Graph189SmallRoot.trace_of_clique_extension (fun _ => True) d order (fun v _ => min v)
  intro K _ clique
  have eq : K=⊤ := top_unique (fun a b e => clique a b trivial trivial ((top_adj _ _).mp e))
  subst K
  obtain ⟨a,b,ne⟩ := exists_pair_ne V
  obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.complete_prescribed a b ne
  exact ⟨a,b,q,hq⟩

#print axioms from_port
#print axioms of_degree
end Graph189PortPath
