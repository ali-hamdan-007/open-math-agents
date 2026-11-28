import Graph189RootedOneLow
import Graph189ExteriorPopulation
import Graph189LinkedExterior

namespace Graph189UniversalLinked
open SimpleGraph Finset Graph189ExteriorDegreeCycle

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem cost (T : Finset V) (a : {x : V | x∉T}) :
    G.degree a.val ≤ (G.induce {x : V | x∉T}).degree a + T.card := by
  classical
  rw [degree_induce_filter]
  have eq : (G.neighborFinset a.val).filter (fun x => x∈{v : V | v∉T}) = G.neighborFinset a.val \ T := by
    ext; simp
  rw [eq,←G.card_neighborFinset_eq_degree]
  have := card_sdiff_add_card_inter (G.neighborFinset a.val) T
  have := card_le_card (inter_subset_right (s₁:=G.neighborFinset a.val) (s₂:=T))
  omega

/-- Avoid a small prescribed set containing the universal vertex and finish
there by one genuine edge. The resulting path otherwise avoids the set. -/
private theorem reach_hub (c : V) (hub : ∀ a, a≠c → G.Adj a c) (T : Finset V)
    (inT : c∈T) (a : V) (start : a∉T) {d : ℕ}
    (positive : ∀ v, T.card < G.degree v)
    (pair : ∀ i j : V, i≠j → d+T.card ≤ G.degree i ∨ d+T.card ≤ G.degree j) :
    ∃ q : G.Walk a c, q.IsPath ∧ d+2 ≤ q.support.length ∧ ∀ v∈T, v≠c → v∉q.support := by
  classical
  let S := {v : V | v∉T}
  let H := G.induce S
  let a' : S := ⟨a,start⟩
  have has : ∃ b,H.Adj a' b := by
    have t := cost (G:=G) T a'
    have pos := positive a
    change G.degree a ≤ H.degree a' + T.card at t
    have non : (H.neighborFinset a').Nonempty := card_pos.mp (by
      rw [H.card_neighborFinset_eq_degree]; omega)
    obtain ⟨b,mem⟩ := non
    exact ⟨b,(H.mem_neighborFinset _ _).mp mem⟩
  have high (i j : S) (ne : i≠j) : d≤H.degree i ∨ d≤H.degree j := by
    have ci := cost (G:=G) T i
    have cj := cost (G:=G) T j
    change G.degree i.val ≤ H.degree i + T.card at ci
    change G.degree j.val ≤ H.degree j + T.card at cj
    rcases pair i.val j.val (fun eq => ne (Subtype.ext eq)) with h|h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  obtain ⟨b,P,hp,len⟩ := Graph189RootedOneLow.rooted_path a' has high
  let e := Embedding.induce (G:=G) S
  let Q := P.map e.toHom
  have path : Q.IsPath := hp.map e.injective
  have miss (v : V) (hv : v∈T) : v∉Q.support := by
    intro hh
    change v∈(P.map e.toHom).support at hh
    rw [Walk.support_map] at hh
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hh
    exact w.property hv
  have bc : b.val ≠ c := fun eq => b.property (eq ▸ inT)
  let edge : G.Adj (e.toHom b) c := hub b.val bc
  refine ⟨Q.concat edge,path.concat (miss c inT) edge,?_,?_⟩
  · change d+2 ≤ (Q.concat edge).support.length
    rw [Walk.length_support,Walk.length_concat]
    change d+2 ≤ (P.map e.toHom).length+1+1
    rw [Walk.length_map]
    rw [Walk.length_support] at len
    omega
  · intro v hv ne hit
    change v∈(Q.concat edge).support at hit
    rw [Walk.support_concat] at hit
    rcases List.mem_append.mp hit with h|h
    · exact miss v hv h
    · exact ne (by simpa using h)

/-- A universal vertex and one exceptional degree allow long paths between
all prescribed endpoints. The exceptional vertex may itself be prescribed. -/
theorem universal_paths (c : V) (hub : ∀ a, a≠c → G.Adj a c) {l : ℕ}
    (three : 3≤l) (positive : ∀ v, 3≤G.degree v)
    (pair : ∀ a b : V, a≠b → l-1 ≤ G.degree a ∨ l-1 ≤ G.degree b)
    (a b : V) (ne : a≠b) : ∃ q : G.Walk a b, q.IsPath ∧ l≤q.support.length := by
  classical
  have into (u : V) (away : u≠c) : ∃ q : G.Walk u c, q.IsPath ∧ l≤q.support.length := by
    obtain ⟨q,hq,len,_⟩ := reach_hub c hub {c} (by simp) u (by simpa using away) (d:=l-2)
      (by intro v; have := positive v; simp; omega)
      (by intro i j diff; have := pair i j diff; simp only [card_singleton]; omega)
    exact ⟨q,hq,by omega⟩
  by_cases bRoot : b=c
  · subst b; exact into a ne
  by_cases aRoot : a=c
  · subst a
    obtain ⟨q,hq,len⟩ := into b bRoot
    exact ⟨q.reverse,hq.reverse,by simpa using len⟩
  let T : Finset V := {c,b}
  have distinct : c≠b := fun eq => bRoot eq.symm
  have ct : T.card=2 := by simp [T,distinct]
  obtain ⟨q,hq,len,avoid⟩ := reach_hub c hub T (by simp [T]) a (by simp [T,aRoot,ne])
    (d:=l-3) (by intro v; have := positive v; omega)
    (by intro i j diff; have := pair i j diff; omega)
  have cb := (hub b bRoot).symm
  refine ⟨q.concat cb,hq.concat (avoid b (by simp [T]) bRoot) cb,?_⟩
  rw [Walk.length_support,Walk.length_concat]
  rw [Walk.length_support] at len
  omega

theorem linked (c : V) (hub : ∀ a, a≠c → G.Adj a c) {l : ℕ}
    (size : l+1≤Fintype.card V) (three : 3≤l) (positive : ∀ v, 3≤G.degree v)
    (pair : ∀ a b : V, a≠b → l-1 ≤ G.degree a ∨ l-1 ≤ G.degree b) :
    Graph189LinkedExterior.Linked G l := by
  classical
  refine ⟨univ,by simpa using size,?_⟩
  intro a _ b _ ne
  obtain ⟨q,hq,len⟩ := universal_paths c hub three positive pair a b ne
  exact ⟨q,hq,len,fun v _ => mem_univ v⟩

#print axioms universal_paths
#print axioms linked
end Graph189UniversalLinked
