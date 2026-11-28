import Graph189ThreeRegularMinimum
import Graph189ContactIntervals
import Graph189HighExteriorDegree
import Graph189MidpointExchange
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open SimpleGraph Finset
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Connected parts of the omitted set. Empty labels are allowed. Maximizing
over such partitions gives the same optimum as using connected components. -/
structure Partition (G : SimpleGraph V) (U : Finset V) (F : V → Finset V) : Prop where
  cover : ∀v,v∈U ↔ ∃i,v∈F i
  separate : ∀i j,i≠j → Disjoint (F i) (F j)
  connected : ∀i,(G.induce (F i:Set V)).Preconnected

def score (F : V → Finset V) : ℕ := ∑i,(F i).card^2

private theorem singleton_parts (G : SimpleGraph V) (U : Finset V) :
    Partition G U (fun i => if i∈U then {i} else ∅) := by
  classical
  constructor
  · intro v
    constructor
    · intro hv
      exact ⟨v,by simp [hv]⟩
    rintro ⟨i,hi⟩
    split_ifs at hi with h
    · simpa [(mem_singleton.mp hi)] using h
    simp at hi
  · intro i j ne
    split_ifs <;> simp_all
  · intro i a b
    have ha := a.property
    have hb := b.property
    have eq : a=b := by
      apply Subtype.ext
      split_ifs at ha hb with h <;> simp_all
    subst b
    exact Reachable.refl _

variable [Nonempty V]

theorem exists_optimal (G : SimpleGraph V) :
    ∃a b,∃p : G.Walk a b,∃F : V→Finset V,p.IsPath ∧
    (∀{u v},∀q : G.Walk u v,q.IsPath → q.length≤p.length) ∧
    Partition G p.support.toFinsetᶜ F ∧
    ∀{u v},∀q : G.Walk u v,q.IsPath → q.length=p.length →
      ∀K : V→Finset V,Partition G q.support.toFinsetᶜ K → score K≤score F := by
  classical
  obtain ⟨a,b,p,hp,longest⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) (Classical.arbitrary V)
  let good := (univ : Finset (V→Finset V)).filter (fun F =>
    ∃u v,∃q : G.Walk u v,q.IsPath ∧ q.length=p.length ∧ Partition G q.support.toFinsetᶜ F)
  have non : good.Nonempty := ⟨_,mem_filter.mpr ⟨mem_univ _,a,b,p,hp,rfl,singleton_parts G _⟩⟩
  obtain ⟨F,fg,maximal⟩ := good.exists_max_image score non
  obtain ⟨u,v,q,hq,len,part⟩ := (mem_filter.mp fg).2
  refine ⟨u,v,q,F,hq,fun r hr => (longest r hr).trans_eq len.symm,part,?_⟩
  intro a' b' r hr same K data
  exact maximal K (mem_filter.mpr ⟨mem_univ _,a',b',r,hr,same.trans len,data⟩)

omit [Nonempty V] in
private theorem insert_connected {U : Finset V} {x y : V}
    (conn : (G.induce (U:Set V)).Preconnected) (hy : y∈U) (edge : G.Adj x y) :
    (G.induce (insert x U:Set V)).Preconnected := by
  classical
  let T : Set V := insert x U
  let base : T := ⟨y,Set.mem_insert_of_mem _ hy⟩
  have toBase (a : T) : (G.induce T).Reachable a base := by
    rcases (Set.mem_insert_iff.mp a.property) with head|inside
    · exact (show (G.induce T).Adj a base by change G.Adj a.val y; rwa [head]).reachable
    · exact (conn ⟨a,inside⟩ ⟨y,hy⟩).map (G.induceHomOfLE (show (U:Set V)⊆T from Set.subset_insert _ _)).toHom
  intro a b
  exact (toBase a).trans (toBase b).symm

omit [Nonempty V] in
theorem exchange {F : V→Finset V} {U : Finset V} (part : Partition G U F)
    {i j x y z : V} (diff : i≠j) (xi : x∈F i) (outside : y∉U) (zj : z∈F j) (edge : G.Adj y z)
    (noncut : (G.induce ((F i).erase x:Set V)).Preconnected) (order : (F i).card≤(F j).card) :
    ∃K : V→Finset V,Partition G (insert y (U.erase x)) K ∧ score F<score K := by
  classical
  let K (l : V) := if l=i then (F i).erase x else if l=j then insert y (F j) else F l
  have old {v l : V} (h : v∈F l) : v∈U := (part.cover v).mpr ⟨l,h⟩
  have yoff (l : V) : y∉F l := fun h => outside (old h)
  have unique {l l' v : V} (h : v∈F l) (h' : v∈F l') : l=l' := by
    by_contra ne
    exact disjoint_left.mp (part.separate l l' ne) h h'
  have km (l v : V) : v∈K l ↔ (v≠x ∧ v∈F l) ∨ (l=j ∧ v=y) := by
    by_cases li : l=i
    · subst l; simp [K,diff]
    by_cases lj : l=j
    · subst l
      have no : x∉F j := fun h => diff (unique xi h)
      simp [K,li]
      grind
    have no : x∉F l := fun h => li (unique h xi)
    simp [K,li,lj]
    grind
  refine ⟨K,⟨?_,?_,?_⟩,?_⟩
  · intro v
    simp only [mem_insert,mem_erase,km,part.cover]
    grind
  · intro l l' ne
    apply Finset.disjoint_left.mpr
    intro v h h'
    rcases (km l v).mp h with ⟨_,h⟩|⟨lj,vy⟩ <;> rcases (km l' v).mp h' with ⟨_,h'⟩|⟨lj',vy'⟩
    · exact ne (unique h h')
    · exact outside (vy' ▸ old h)
    · exact outside (vy ▸ old h')
    · exact ne (lj.trans lj'.symm)
  · intro l
    by_cases li : l=i
    · rw [show K l = (F i).erase x by simp [K,li]]
      exact noncut
    by_cases lj : l=j
    · rw [show K l = insert y (F j) by simp [K,lj,diff.symm],coe_insert]
      exact insert_connected (part.connected j) zj edge
    rw [show K l = F l by simp [K,li,lj]]
    exact part.connected l
  · let S := (univ.erase i).erase j
    have jin : j∈univ.erase i := mem_erase.mpr ⟨diff.symm,mem_univ _⟩
    have sums (T : V→Finset V) : (∑l∈S,(T l).card^2)+(T j).card^2+(T i).card^2=score T := by
      rw [show (∑l∈S,(T l).card^2)+(T j).card^2=∑l∈univ.erase i,(T l).card^2 from
        sum_erase_add _ (fun l => (T l).card^2) jin]
      exact sum_erase_add _ (fun l => (T l).card^2) (mem_univ _)
    have remain : (∑l∈S,(K l).card^2)=∑l∈S,(F l).card^2 := by
      apply sum_congr rfl
      intro l hl
      simp [K,(mem_erase.mp (mem_erase.mp hl).2).1,(mem_erase.mp hl).1]
    have iCard : (K i).card+1=(F i).card := by simpa [K] using card_erase_add_one xi
    have jCard : (K j).card=(F j).card+1 := by simp [K,diff.symm,yoff j]
    rw [←sums K,←sums F,remain,jCard,←iCard]
    rw [←iCard] at order
    nlinarith

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.exists_optimal
#print axioms Graph189OptimalExterior.exchange
