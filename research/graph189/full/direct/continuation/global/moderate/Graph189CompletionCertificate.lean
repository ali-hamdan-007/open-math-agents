import Graph189Completion

namespace Graph189Completion
open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V]

/-- Every admissible completion must satisfy the two path lengths, all degree
lower bounds, connectivity after each one-vertex deletion, and the even cap. -/
structure Feasible (G : SimpleGraph V) (z : V) (full afterDelete k : ℕ)
    (required : V→ℕ) : Prop where
  short : ¬TooLong G z full afterDelete
  degrees : ∀ v, required v≤G.degree v
  connected : ∀ v, (G.induce {u | u≠v}).Connected
  even : ∀ v, G.distEven v≤k+1

/-- These are the precise vertex-count thresholds of the moderate checker.
The longest deletion path has p vertices. Every original path omits at least
h+2 vertices under the contrary near-spanning-path assumption. -/
theorem checker_path_bounds {G : SimpleGraph V} (z : V) (h p : ℕ)
    (gap : ∀ {a b} (P : G.Walk a b), P.IsPath → h+2≤Fintype.card V-(P.length+1))
    (longest : ∀ {a b} (P : (G.induce {u | u≠z}).Walk a b), P.IsPath → P.length+1≤p) :
    ¬TooLong G z (Fintype.card V-h-1) (p+1) := by
  apply not_tooLong_of_path_bounds
  · intro a b P hp
    have := gap P hp
    omega
  · intro a b P hp
    exact Nat.lt_succ_of_le (longest P hp)

/-- A finite decision-tree certificate rules out all intermediate graphs.
The two child intervals in split contain the actual graph according as
the tested edge is present or absent. -/
inductive Rejection (z : V) (full afterDelete k : ℕ) (required : V→ℕ) :
    SimpleGraph V → SimpleGraph V → Prop where
  | path {L U} (long : TooLong L z full afterDelete) : Rejection z full afterDelete k required L U
  | degree {L U} (v : V) (small : U.degree v<required v) : Rejection z full afterDelete k required L U
  | cut {L U} (v : V) (apart : ¬(U.induce {u | u≠v}).Connected) :
      Rejection z full afterDelete k required L U
  | even {L U} (v : V) (excess : k<(forcedTwo L U v).card) : Rejection z full afterDelete k required L U
  | forbid {L U} (a b : V) (blocked : TooLong (L⊔edge a b) z full afterDelete)
      (next : Rejection z full afterDelete k required L (U\edge a b)) :
      Rejection z full afterDelete k required L U
  | force {L U} (a b : V) (possible : U.Adj a b) (tight : U.degree a=required a)
      (next : Rejection z full afterDelete k required (L⊔edge a b) U) :
      Rejection z full afterDelete k required L U
  | split {L U} (a b : V)
      (withEdge : Rejection z full afterDelete k required (L⊔edge a b) U)
      (withoutEdge : Rejection z full afterDelete k required L (U\edge a b)) :
      Rejection z full afterDelete k required L U

/-- A certificate is sound for the actual graph, including when a partial
interval has many unspecified edges. -/
theorem Rejection.sound {G L U : SimpleGraph V} {z : V} {f d k : ℕ} {required : V→ℕ}
    (tree : Rejection z f d k required L U) (actual : Feasible G z f d k required) :
    L≤G → G≤U → False := by
  induction tree with
  | path long =>
    intro lower _
    exact actual.short (long.mono lower)
  | degree v small =>
    intro _ upper
    exact (Nat.not_lt_of_ge ((actual.degrees v).trans (degree_le_of_le upper))) small
  | cut v apart =>
    intro _ upper
    exact apart (connected_induce_of_le upper _ (actual.connected v))
  | even v excess =>
    intro lower upper
    exact (Nat.not_lt_of_ge (forcedTwo_card_le lower upper v _ (actual.even v))) excess
  | forbid a b blocked next ih =>
    intro lower upper
    exact ih lower (forbid_edge_of_tooLong lower upper actual.short blocked)
  | force a b possible tight next ih =>
    intro lower upper
    exact ih (force_edge_at_saturated lower upper (actual.degrees a) tight possible) upper
  | split a b withEdge withoutEdge yes no =>
    intro lower upper
    by_cases actualEdge : G.Adj a b
    · exact yes (sup_le lower ((edge_le_iff (G:=G) (v:=a) (w:=b)).mpr (Or.inr actualEdge))) upper
    · exact no lower (omit_edge upper actualEdge)

end Graph189Completion

#print axioms Graph189Completion.checker_path_bounds
#print axioms Graph189Completion.Rejection.sound
