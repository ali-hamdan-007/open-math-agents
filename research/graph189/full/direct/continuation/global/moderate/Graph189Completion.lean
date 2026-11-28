import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance

namespace Graph189Completion
open SimpleGraph Finset
open scoped Classical
variable {V : Type*}

/-- The target is a number of vertices, as in the finite completion checker. -/
def HasPath (G : SimpleGraph V) (target : ℕ) : Prop :=
  ∃ a b, ∃ P : G.Walk a b, P.IsPath ∧ target≤P.support.length

theorem HasPath.mono {L G : SimpleGraph V} {t : ℕ} (h : HasPath L t) (inc : L≤G) :
    HasPath G t := by
  obtain ⟨a,b,P,hp,hlen⟩ := h
  exact ⟨a,b,P.mapLe inc,hp.mapLe inc,by simpa only [Walk.support_mapLe_eq_support] using hlen⟩

private theorem walk_of_chain {G : SimpleGraph V} (a : V) (l : List V)
    (chain : (a::l).IsChain G.Adj) : ∃ b, ∃ P : G.Walk a b, P.support=a::l := by
  induction l generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons v l ih =>
    obtain ⟨edge,tail⟩ := List.isChain_cons_cons.mp chain
    obtain ⟨b,P,hs⟩ := ih v tail
    exact ⟨b,.cons edge P,by simp only [Walk.support_cons,hs]⟩

/-- A plain list of distinct vertices and consecutive mandatory edges is
a checkable certificate for a lower-graph path. -/
theorem hasPath_of_list {G : SimpleGraph V} {a : V} {l : List V} {t : ℕ}
    (chain : (a::l).IsChain G.Adj) (unique : (a::l).Nodup) (length : t≤(a::l).length) :
    HasPath G t := by
  obtain ⟨b,P,hs⟩ := walk_of_chain a l chain
  exact ⟨a,b,P,Walk.IsPath.mk' (hs ▸ unique),hs ▸ length⟩

theorem hasPath_induce_of_list {G : SimpleGraph V} {a : V} {l : List V} {t : ℕ}
    {S : Set V} (inside : ∀ v∈a::l, v∈S) (chain : (a::l).IsChain G.Adj)
    (unique : (a::l).Nodup) (length : t≤(a::l).length) : HasPath (G.induce S) t := by
  obtain ⟨b,P,hs⟩ := walk_of_chain a l chain
  have inP : ∀ v∈P.support, v∈S := hs ▸ inside
  have hp := Walk.IsPath.mk' (p:=P) (hs ▸ unique)
  let Q := P.induce S inP
  have back : Q.map (Embedding.induce S).toHom=P := Walk.map_induce P inP
  exact ⟨_,_,Q,(back ▸ hp).of_map,by simp only [Q,Walk.support_induce,List.length_attachWith,hs]; exact length⟩

def TooLong (G : SimpleGraph V) (z : V) (full afterDelete : ℕ) : Prop :=
  HasPath G full ∨ HasPath (G.induce {u | u≠z}) afterDelete

theorem TooLong.mono {L G : SimpleGraph V} {z : V} {f d : ℕ}
    (h : TooLong L z f d) (inc : L≤G) : TooLong G z f d := by
  rcases h with h|h
  · exact Or.inl (h.mono inc)
  · exact Or.inr (h.mono (fun _ _ e => inc e))

theorem not_tooLong_of_path_bounds {G : SimpleGraph V} {z : V} {f d : ℕ}
    (whole : ∀ {a b} (P : G.Walk a b), P.IsPath → P.length+1<f)
    (deleted : ∀ {a b} (P : (G.induce {u | u≠z}).Walk a b), P.IsPath → P.length+1<d) :
    ¬TooLong G z f d := by
  rintro (⟨a,b,P,hp,sz⟩|⟨a,b,P,hp,sz⟩)
  · rw [Walk.length_support] at sz
    exact (Nat.not_lt_of_ge sz) (whole P hp)
  · rw [Walk.length_support] at sz
    exact (Nat.not_lt_of_ge sz) (deleted P hp)

theorem connected_induce_of_le {G U : SimpleGraph V} (upper : G≤U) (S : Set V)
    (connected : (G.induce S).Connected) : (U.induce S).Connected :=
  Connected.mono (fun _ _ e => upper e) connected

theorem omit_edge {G U : SimpleGraph V} (upper : G≤U) {a b : V}
    (absent : ¬G.Adj a b) : G≤U\edge a b := by
  intro v w hvw
  refine ⟨upper hvw,?_⟩
  intro h
  obtain ⟨e,_⟩ := (edge_adj a b v w).mp h
  rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact absent hvw
  · exact absent hvw.symm

theorem forbid_edge_of_tooLong {L G U : SimpleGraph V} (lower : L≤G) (upper : G≤U)
    {z a b : V} {f d : ℕ} (short : ¬TooLong G z f d)
    (blocked : TooLong (L⊔edge a b) z f d) : G≤U\edge a b := by
  apply omit_edge upper
  intro hab
  exact short (blocked.mono (sup_le lower ((edge_le_iff (G:=G) (v:=a) (w:=b)).mpr (Or.inr hab))))

section Finite
variable [Fintype V] {L G U : SimpleGraph V}

theorem saturated_neighbors (upper : G≤U) (x : V) {required : ℕ}
    (floor : required≤G.degree x) (saturated : U.degree x=required) :
    G.neighborFinset x=U.neighborFinset x := by
  apply eq_of_subset_of_card_le
  · exact fun y h => (U.mem_neighborFinset x y).mpr (upper ((G.mem_neighborFinset x y).mp h))
  · rw [U.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree,saturated]
    exact floor

theorem force_edge_at_saturated (lower : L≤G) (upper : G≤U) {a b : V} {required : ℕ}
    (floor : required≤G.degree a) (saturated : U.degree a=required)
    (possible : U.Adj a b) : L⊔edge a b≤G := by
  apply sup_le lower
  apply (edge_le_iff (G:=G) (v:=a) (w:=b)).mpr
  right
  apply (G.mem_neighborFinset a b).mp
  rw [saturated_neighbors upper a floor saturated]
  exact (U.mem_neighborFinset a b).mpr possible

/-- Lower-graph two-step witnesses whose target edge is absent even in the
upper graph. No connectivity or shortest-path assumption on L is needed. -/
noncomputable def forcedTwo (L U : SimpleGraph V) (x : V) : Finset V :=
  univ.filter (fun y => x≠y ∧ ¬U.Adj x y ∧ ∃ a, L.Adj x a ∧ L.Adj y a)

theorem forcedTwo_dist (lower : L≤G) (upper : G≤U) {x y : V} (hy : y∈forcedTwo L U x) :
    G.dist x y=2 := by
  obtain ⟨ne,missing,a,xa,ya⟩ := (mem_filter.mp hy).2
  have h := SimpleGraph.edist_eq_two_iff.mpr ⟨ne,fun e => missing (upper e),⟨a,lower xa,lower ya⟩⟩
  simp [SimpleGraph.dist,h]

theorem forcedTwo_card_le (lower : L≤G) (upper : G≤U) (x : V) (k : ℕ)
    (cap : G.distEven x≤k+1) : (forcedTwo L U x).card≤k := by
  classical
  have sub : insert x (forcedTwo L U x) ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl|hy
    · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
    · exact mem_filter.mpr ⟨mem_univ _,by simp [forcedTwo_dist lower upper hy]⟩
  have nmem : x∉forcedTwo L U x := fun h => (mem_filter.mp h).2.1 rfl
  have cnt := card_le_card sub
  rw [card_insert_of_notMem nmem] at cnt
  change _≤G.distEven x at cnt
  omega

end Finite
end Graph189Completion

#print axioms Graph189Completion.hasPath_of_list
#print axioms Graph189Completion.hasPath_induce_of_list
#print axioms Graph189Completion.forbid_edge_of_tooLong
#print axioms Graph189Completion.force_edge_at_saturated
#print axioms Graph189Completion.forcedTwo_card_le
