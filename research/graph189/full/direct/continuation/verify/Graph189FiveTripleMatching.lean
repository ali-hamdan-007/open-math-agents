import Graph189ThreeSelectedPorts
import Graph189ProtectedExteriorDegree

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveTripleMatching
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}

/-- A fixed contact of the first row extends to a matching of all three
rows if each of the other two has at least three choices. -/
theorem forced (p : G.Walk u v) (W : Finset V) (three : W.card=3)
    (x : W) (i : Fin p.support.length) (edge : G.Adj p.support[i.val] x.val)
    (rows : ∀ y : W, y≠x → 3≤((univ : Finset (Fin p.support.length)).filter
      (fun j => G.Adj p.support[j.val] y.val)).card) :
    ∃ M : Finset (Fin p.support.length), M.card=3 ∧ i∈M ∧ ∃ f : M ↪ W,
      ∀ j : M, G.Adj p.support[j.val.val] (f j).val := by
  classical
  let N (y : W) : Finset (Fin p.support.length) := if y=x then {i} else
    univ.filter (fun j => G.Adj p.support[j.val] y.val)
  have hall (T : Finset W) : T.card≤(T.biUnion N).card := by
    by_cases h : ∃ y∈T, y≠x
    · obtain ⟨y,hy,ne⟩ := h
      have card := T.card_le_univ
      rw [Fintype.card_coe,three] at card
      have le : N y ⊆ T.biUnion N := fun z mem => mem_biUnion.mpr ⟨y,hy,mem⟩
      have sz := card_le_card le
      rw [show N y=univ.filter (fun j : Fin p.support.length => G.Adj p.support[j.val] y.val) by
        simp [N,ne]] at sz
      exact card.trans ((rows y ne).trans sz)
    · by_cases empty : T=∅
      · simp [empty]
      obtain ⟨y,hy⟩ := nonempty_iff_ne_empty.mpr empty
      have mem : y=x := by_contra (fun ne => h ⟨y,hy,ne⟩)
      have eq : T={x} := by
        apply eq_singleton_iff_unique_mem.mpr
        exact ⟨mem ▸ hy,fun z hz => by_contra (fun ne => h ⟨z,hz,ne⟩)⟩
      simp [eq,N]
  obtain ⟨g,inj,allowed⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  let M := (univ : Finset W).image g
  let emb : W → M := fun y => ⟨g y,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective emb := by
    constructor
    · intro a b h; exact inj (congrArg Subtype.val h)
    · intro j
      obtain ⟨a,_,eq⟩ := mem_image.mp j.property
      exact ⟨a,Subtype.ext eq⟩
  let e := Equiv.ofBijective emb bij
  have gx : g x=i := by simpa [N] using allowed x
  have size : M.card=W.card := by simpa using Fintype.card_congr e.symm
  refine ⟨M,size.trans three,gx ▸ mem_image_of_mem g (mem_univ x),e.symm.toEmbedding,?_⟩
  intro j
  let a := e.symm j
  have val : g a=j.val := congrArg Subtype.val (e.apply_symm_apply j)
  change G.Adj (p.support.get j.val) a.val
  rw [←val]
  by_cases same : a=x
  · simpa only [same,gx,List.get_eq_getElem] using edge
  · exact (mem_filter.mp (by simpa [N,same] using allowed a :
      g a ∈ univ.filter (fun l : Fin p.support.length => G.Adj p.support[l.val] a.val))).2

/-- The positions of a matched triple on a thirteen-vertex protected path
are determined by the position of its protected vertex. -/
def marks (t : ℕ) : Finset ℕ :=
  if t=0 then {1,5,9} else if t=4 then {3,5,9} else if t=8 then {3,7,9} else {3,7,11}

theorem layout {a b c t L : ℕ} (size : L≤13) (interior : 0<a ∧ c+1<L)
    (spacing : a+2≤b ∧ b+2≤c) (pos : t<L)
    (pre : a≤t → 3≤a) (post : t≤c → c+4≤L)
    (first : b≤t ∨ t≤a → a+4≤b) (second : c≤t ∨ t≤b → b+4≤c) :
    L=13 ∧ (t=0 ∨ t=4 ∨ t=8 ∨ t=12) ∧ ({a,b,c} : Finset ℕ)=marks t := by
  have patterns : (t=0 ∧ a=1 ∧ b=5 ∧ c=9) ∨ (t=4 ∧ a=3 ∧ b=5 ∧ c=9) ∨
      (t=8 ∧ a=3 ∧ b=7 ∧ c=9) ∨ (t=12 ∧ a=3 ∧ b=7 ∧ c=11) := by omega
  rcases patterns with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩ <;>
    exact ⟨by omega,by decide,by decide⟩

end Graph189FiveTripleMatching
