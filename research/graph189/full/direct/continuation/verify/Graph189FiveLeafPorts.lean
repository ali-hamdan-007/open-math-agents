import Mathlib.Data.Finset.Sort
import Graph189TwoMarkShift
import Graph189HighMinimumGap

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189FiveLeafPorts

/-- A row containing four marks exhausts the five-witness bound, so all
successive gaps in every ordered quadruple are exactly two. -/
theorem marks_exact {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (outside : x∉p.support) (quota : (univ.filter (fun z => G.dist x z=2)).card ≤ 5)
    {i j l r : ℕ} (hi : i∈contactPositions p x) (hj : j∈contactPositions p x) (hl : l∈contactPositions p x)
    (hr : r∈contactPositions p x) (ij : i<j) (jl : j<l) (lr : l<r) : i+2=j ∧ j+2=l ∧ l+2=r := by
  classical
  have apart {m n : ℕ} (hm : m∈contactPositions p x) (hn : n∈contactPositions p x) (lt : m<n) : m+2 ≤ n := by
    obtain ⟨mv,me⟩ := (mem_contactPositions p x m).mp hm
    obtain ⟨nv,ne⟩ := (mem_contactPositions p x n).mp hn
    exact omitted_contact_spacing p hp longest outside ⟨m,mv⟩ ⟨n,nv⟩ lt
      (by simpa [get_at] using me) (by simpa [get_at] using ne)
  have first := apart hi hj ij
  have second := apart hj hl jl
  have third := apart hl hr lr
  obtain ⟨ip,ib,im,ia⟩ := shifted_contact p hp longest outside hi
  obtain ⟨jp,jb,jm,ja⟩ := shifted_contact p hp longest outside hj
  obtain ⟨lp,lb,lm,la⟩ := shifted_contact p hp longest outside hl
  obtain ⟨rp,rb,rm,ra⟩ := shifted_contact p hp longest outside hr
  let A : Finset ℕ := {i-1,i+1,j+1,l+1,r+1}
  have acard : A.card=5 := by
    dsimp [A]
    rw [card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_insert,mem_singleton]; omega),
      card_insert_of_notMem (by simp only [mem_singleton]; omega),card_singleton]
  have full (s : ℕ) (inPath : s < p.support.length) (two : G.dist x (p.getVert s)=2) : s∈A := by
    by_contra missing
    let S := insert s A
    have good (t : ℕ) (ht : t∈S) : t < p.support.length ∧ G.dist x (p.getVert t)=2 := by
      simp only [S,A,mem_insert,mem_singleton] at ht
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> first | assumption | omega
    have inj : Set.InjOn p.getVert (S : Set ℕ) := by
      intro m hm n hn eq
      have := (good m hm).1
      have := (good n hn).1
      have := p.length_support
      exact hp.getVert_injOn (by change m ≤ p.length; omega) (by change n ≤ p.length; omega) eq
    have sub : S.image p.getVert ⊆ univ.filter (fun z => G.dist x z=2) := by
      intro z hz
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨mem_univ _,(good t ht).2⟩
    have c := (card_le_card sub).trans quota
    rw [card_image_of_injOn inj,show S=insert s A from rfl,card_insert_of_notMem missing,acard] at c
    omega
  have m := full (j-1) (by omega) jm
  have n := full (l-1) (by omega) lm
  have o := full (r-1) (by omega) rm
  simp only [A,mem_insert,mem_singleton] at m n o
  omega

theorem four_marks {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v x : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length)
    (outside : x∉p.support) (quota : (univ.filter (fun z => G.dist x z=2)).card ≤ 5)
    (many : 4 ≤ (contactPositions p x).card) :
    ∃ i, i∈contactPositions p x ∧ i+2∈contactPositions p x ∧ i+4∈contactPositions p x ∧ i+6∈contactPositions p x := by
  let N := contactPositions p x
  let A := N.orderEmbOfCardLe many
  have hit (i : Fin 4) : A i∈N := N.orderEmbOfCardLe_mem many i
  obtain ⟨l,m,r⟩ := marks_exact p hp longest outside quota (hit 0) (hit 1) (hit 2) (hit 3)
    (A.strictMono (by decide)) (A.strictMono (by decide)) (A.strictMono (by decide))
  refine ⟨A 0,hit 0,?_,?_,?_⟩
  · rw [l]; exact hit 1
  · rw [show A 0+4=A 2 by omega]; exact hit 2
  · rw [show A 0+6=A 3 by omega]; exact hit 3

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem port_window (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (off : List.Disjoint q.support p.support)
    {s : ℕ} (mark : s ∈ contactPositions p x) :
    q.support.length ≤ s ∧ s+1+q.support.length ≤ p.support.length := by
  obtain ⟨sr,adj⟩ := (mem_contactPositions p x s).mp mark
  have link : G.Adj p.support[s] x := by rwa [get_at p sr]
  have rev : List.Disjoint q.reverse.support p.support := by simpa [Walk.support_reverse] using off
  have front := prefix_of_detour p hp longest ⟨s,sr⟩ q.reverse hq.reverse rev link.symm
  have back := suffix_of_detour p hp longest ⟨s,sr⟩ q hq off link
  simp only [Walk.support_reverse,List.length_reverse] at front
  exact ⟨front,back⟩

/-- Any high omission has at least one exterior neighbor: otherwise the
strict single-mark shift already exceeds its whole distance-two budget. -/
theorem has_neighbor (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {x : V} (off : x∉p.support) (high : 5 ≤ G.degree x)
    (quota : (univ.filter (fun w => G.dist x w=2)).card ≤ 5) :
    ∃ w, G.Adj x w ∧ w∉p.support := by
  classical
  by_contra! allOn
  have covered : G.neighborFinset x ⊆ p.support.toFinset :=
    fun w hw => List.mem_toFinset.mpr (allOn w ((G.mem_neighborFinset _ _).mp hw))
  have count := contact_card_neighbors p hp x
  rw [inter_eq_left.mpr covered,G.card_neighborFinset_eq_degree] at count
  have shell := single_positions_lt_path_shell p hp maximal off (card_pos.mp (by omega : 0 < (contactPositions p x).card))
  have sub : p.support.toFinset.filter (fun w => G.dist x w=2) ⊆ univ.filter (fun w => G.dist x w=2) :=
    fun w h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
  have := (card_le_card sub).trans quota
  omega

/-- An exchange at any midpoint between two high marks makes that midpoint
adjacent to the one other omission. -/
theorem charged_midpoint (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {x z : V} (off : x∉p.support) (zo : z∉p.support)
    (only : ∀ v, v∉p.support → v=x ∨ v=z) (high : ∀ v, v≠z → 5 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ 5)
    {i : ℕ} (first : i∈contactPositions p x) (last : i+2∈contactPositions p x) :
    G.Adj z (p.getVert (i+1)) := by
  classical
  obtain ⟨_,ad⟩ := (mem_contactPositions p x i).mp first
  obtain ⟨ir,bd⟩ := (mem_contactPositions p x (i+2)).mp last
  obtain ⟨u,v,q,hq,len,supp⟩ := swap_contact_midpoint p hp off i ir ad bd
  let t := p.getVert (i+1)
  have tx : t≠x := fun e => off (e ▸ p.getVert_mem_support _)
  have tz : t≠z := fun e => zo (e ▸ p.getVert_mem_support _)
  have missing : t∉q.support := by
    intro mem
    have on := List.mem_toFinset.mpr mem
    rw [supp] at on
    exact (mem_insert.mp on).elim tx (fun h => (mem_erase.mp h).1 rfl)
  obtain ⟨w,edge,absent⟩ := has_neighbor q hq (fun r hr => len ▸ maximal r hr) missing (high t tz) (quota t)
  have wo : w∉p.support := by
    intro on
    apply absent
    apply List.mem_toFinset.mp
    rw [supp]
    exact mem_insert_of_mem (mem_erase.mpr ⟨edge.ne.symm,List.mem_toFinset.mpr on⟩)
  rcases only w wo with wx|wz
  · apply False.elim
    apply absent
    apply List.mem_toFinset.mp
    rw [supp,wx]
    exact mem_insert_self _ _
  · exact wz ▸ edge.symm

#print axioms four_marks
#print axioms charged_midpoint
end Graph189FiveLeafPorts
