import Graph189ExteriorPopulation
import Graph189ExteriorDegree

open SimpleGraph Finset
namespace Graph189LinkedRoot
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The center and exactly its neighbors exterior to the path vertex set. -/
def window (P : Finset V) (x : V) : Finset V :=
  insert x (H.neighborFinset x \ P)

theorem window_card (P : Finset V) (x : V) :
    (window H P x).card = (H.neighborFinset x \ P).card+1 := by
  apply card_insert_of_notMem
  exact fun h => (H.notMem_neighborFinset_self _) (mem_sdiff.mp h).1

theorem window_outside (P : Finset V) {x : V} (hx : x∉P) {y : V}
    (hy : y∈window H P x) : y∉P := by
  rcases mem_insert.mp hy with rfl|hy
  · exact hx
  · exact (mem_sdiff.mp hy).2

theorem window_adj (P : Finset V) {x y : V} (hy : y∈window H P x) (ne : y≠x) :
    H.Adj x y :=
  (H.mem_neighborFinset x y).mp (mem_sdiff.mp (mem_insert.mp hy |>.resolve_left ne)).1

private theorem center_degree (P : Finset V) (x : V) :
    (H.induce (window H P x : Set V)).degree ⟨x,mem_insert_self _ _⟩ =
      (H.neighborFinset x \ P).card := by
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  congr 1
  ext z
  simp only [window,Finset.mem_filter,Finset.mem_coe,mem_insert,mem_sdiff]
  constructor
  · rintro ⟨hz,rfl|h⟩
    · exact ((H.notMem_neighborFinset_self _) hz).elim
    · exact h
  · exact fun h => ⟨h.1,Or.inr h⟩

/-- At a vertex adjacent to the center, the center itself and all common
exterior neighbors contribute separate neighbors in the induced window. -/
private theorem adjacent_degree (P : Finset V) (x : V) (y : window H P x)
    (ne : y.val≠x) :
    1+((H.neighborFinset y.val \ P) ∩ H.neighborFinset x).card ≤
      (H.induce (window H P x : Set V)).degree y := by
  let C := (H.neighborFinset y.val \ P) ∩ H.neighborFinset x
  have no : x∉C := fun h => (H.notMem_neighborFinset_self _) (mem_inter.mp h).2
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  have inc : insert x C ⊆ (H.neighborFinset y.val).filter (fun v => v ∈ (window H P x : Set V)) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_filter.mpr ⟨(H.mem_neighborFinset _ _).mpr
          (window_adj H P y.property ne).symm,mem_insert_self _ _⟩
    · obtain ⟨h1,h2⟩ := mem_inter.mp hv
      exact mem_filter.mpr ⟨(mem_sdiff.mp h1).1,mem_insert_of_mem (mem_sdiff.mpr ⟨h2,(mem_sdiff.mp h1).2⟩)⟩
  have bound := card_le_card inc
  rw [card_insert_of_notMem no] at bound
  simpa only [C,Nat.add_comm 1] using bound

/-- The sharp exterior contact inequality yields the degree hypotheses for a
linked set inside a closed exterior neighborhood, with one possible exception. -/
theorem window_degrees {a b : V} (p : H.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : H.Walk u v, r.IsPath → r.length≤p.length)
    (x : V) (outside : x∉p.support) (high : V→Prop) (hx : high x)
    {k δ l : ℕ} (hd : ∀ v, high v → k≤H.degree v+1) (md : ∀ v, δ≤H.degree v+1)
    (cap : (univ.filter (fun z => H.dist x z=2)).card≤k)
    (three : 3≤l) (size : l≤(H.neighborFinset x \ p.support.toFinset).card)
    (highRoom : l-1+(H.neighborFinset x \ p.support.toFinset).card+2≤k)
    (lowRoom : 3+(H.neighborFinset x \ p.support.toFinset).card+2≤δ) :
    ∀ y : window H p.support.toFinset x,
      3≤(H.induce (window H p.support.toFinset x : Set V)).degree y ∧
      (high y.val → l-1≤(H.induce (window H p.support.toFinset x : Set V)).degree y) := by
  intro y
  by_cases eq : y.val=x
  · have same : y=(⟨x,mem_insert_self _ _⟩ : window H p.support.toFinset x) := Subtype.ext eq
    rw [same,center_degree]
    exact ⟨three.trans size,fun _ => by omega⟩
  have adj := window_adj H p.support.toFinset y.property eq
  have out := window_outside H p.support.toFinset (fun h => outside (List.mem_toFinset.mp h)) y.property
  have contact := Graph189ExteriorGap.exterior_contact_degree p hp longest outside
    (fun h => out (List.mem_toFinset.mpr h)) adj cap
  have split := card_sdiff_add_card_inter (H.neighborFinset x) p.support.toFinset
  rw [H.card_neighborFinset_eq_degree] at split
  have inside := adjacent_degree H p.support.toFinset x y eq
  have center := hd x hx
  have base := md y.val
  exact ⟨by omega,fun h => by have := hd y.val h; omega⟩

#print axioms window_degrees
end Graph189LinkedRoot
