import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

open SimpleGraph Finset
namespace Graph189LinkedExterior

/-- A set containing at least l+1 vertices with internally routed paths of
at least l vertices between any two prescribed distinct members. -/
def Linked {W : Type*} (H : SimpleGraph W) (l : Nat) : Prop :=
  ∃ D : Finset W, l+1≤D.card ∧ ∀ u∈D, ∀ v∈D, u≠v →
    ∃ p : H.Walk u v, p.IsPath ∧ l≤p.support.length ∧ ∀ b∈p.support,b∈D

theorem map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    (injective : Function.Injective f) {l : Nat} (linked : Linked G l) : Linked H l := by
  classical
  obtain ⟨D,size,paths⟩ := linked
  let e : V ↪ W := ⟨f,injective⟩
  refine ⟨D.map e,by simpa using size,?_⟩
  intro u hu v hv ne
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hu
  obtain ⟨y,hy,rfl⟩ := mem_map.mp hv
  obtain ⟨q,hq,len,within⟩ := paths x hx y hy (fun same => ne (congrArg e same))
  refine ⟨q.map f,hq.map injective,?_,?_⟩
  · simpa only [Walk.support_map,List.length_map] using len
  · intro b hb
    rw [Walk.support_map] at hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact mem_map.mpr ⟨a,within a ha,rfl⟩

#print axioms map
end Graph189LinkedExterior
