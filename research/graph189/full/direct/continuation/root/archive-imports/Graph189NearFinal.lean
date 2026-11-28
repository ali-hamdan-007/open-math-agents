import Graph189ConeNontrivial
import Graph189ExteriorMatching
import Graph189HallDeficiency
import Graph189HighMinimumGap
import Graph189LayerCutoff
import Graph189MatchedOrder
import Graph189PrescribedBatch
import Graph189RootedOmission
import Graph189RootedSplice
import Graph189SmallMinimumOrder
import Graph189StructuralConclusion
import Graph189TwoTightGaps
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Finset.Sort







namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap Graph189ExteriorDegreeCycle Graph189LayerCover
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The entire exterior of every longest path through the least-degree vertex
is Hamilton-connected if its deletion is traceable and twice its degree fits the quota. -/
theorem hamilton_connected_rooted_exterior (connected : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z)
    (half : 2*G.degree z≤G.secondSmallestDegree) (cap : ∀ a, G.distEven a≤G.secondSmallestDegree+1)
    {u v : {b : V | b≠z}} (r : (G.induce {b : V | b≠z}).Walk u v) (hr : r.IsHamiltonian)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (on : z∈q.support)
    (longest : ∀ {c d}, ∀ p : G.Walk c d, p.IsPath → z∈p.support → p.length≤q.length) :
    let U := univ \ q.support.toFinset
    U.card ≤ G.secondSmallestDegree+1-G.degree z ∧
    ∀ a b : U, a≠b → ∃ p : (G.induce (U : Set V)).Walk a b, p.IsHamiltonian := by
  classical
  intro U
  let k := G.secondSmallestDegree
  let d := G.degree z
  have equal : U.card+q.support.length=Fintype.card V := by
    have h := card_sdiff_add_card_inter (univ : Finset V) q.support.toFinset
    rwa [univ_inter,List.toFinset_card_of_nodup hq.support_nodup,card_univ] at h
  have miss {i j} (p : G.Walk i j) (hp : p.IsPath) (hz : z∈p.support) :
       p.support.length+U.card≤Fintype.card V := by
    have h := longest p hp hz
    have p1 := p.length_support
    have q1 := q.length_support
    omega
  have lower := order_of_rooted_gap z (by omega) miss r hr
  have upper := Graph189LayerCutoff.order_of_small_degree G connected z G.secondSmallestDegree cap (by omega)
  change (d+1)*(U.card+1)≤Fintype.card V at lower
  change Fintype.card V≤1+d+k+d*(k+1-d) at upper
  change 2*d≤k at half
  change 3≤d at three
  have small : U.card≤k+1-d := by
    by_contra! large
    have lim : k+1-d+2≤U.card+1 := by omega
    have count := (Nat.mul_le_mul_left (d+1) lim).trans lower
    have eq : k+1-d+d=k+1 := by omega
    nlinarith
  refine ⟨small,?_⟩
  intro a b ne
  let H := G.induce (U : Set V)
  have high (i : U) : k/2≤H.degree i := by
    have out : i.val∉q.support := fun h => (mem_sdiff.mp i.property).2 (List.mem_toFinset.mpr h)
    have h := rooted_half_exterior z least q hq on longest out (by omega) cap
    have same : ((G.neighborFinset i.val).filter (fun w => w∈(U : Set V)))=G.neighborFinset i.val \ q.support.toFinset := by
      ext w
      simp [U]
    change _ ≤ (G.induce (U : Set V)).degree i
    rwa [degree_induce_filter,same]
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (le_top : H≤⊤) _ (Graph189TerminalLeafClosure.complete_prescribed a b ne)
  intro i j _ _
  have hi := high i
  have hj := high j
  have size : Fintype.card (U : Set V) = U.card := Fintype.card_coe U
  omega

/-- Nontraceability and a Hamiltonian minimum deletion force the low-degree
alternative and thereby give the same Hamilton-connected exterior without a degree-ratio premise. -/
theorem near_spanning_rooted_exterior (connected : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z) (k5 : 5≤G.secondSmallestDegree)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (cap : ∀ a, G.distEven a≤G.secondSmallestDegree+1)
    {u v : {b : V | b≠z}} (r : (G.induce {b : V | b≠z}).Walk u v) (hr : r.IsHamiltonian)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (on : z∈q.support)
    (longest : ∀ {c d}, ∀ p : G.Walk c d, p.IsPath → z∈p.support → p.length≤q.length) :
    let U := univ \ q.support.toFinset
    2*G.degree z≤G.secondSmallestDegree ∧ U.card ≤ G.secondSmallestDegree+1-G.degree z ∧
    ∀ a b : U, a≠b → ∃ p : (G.induce (U : Set V)).Walk a b, p.IsHamiltonian := by
  classical
  have half : 2*G.degree z ≤ G.secondSmallestDegree := by
    by_contra! bad
    have high (u : V) : G.secondSmallestDegree<2*G.degree u := by
      have := G.minDegree_le_degree u
      omega
    have impossible := deletion_gap z r hr.isPath (high_min_all_paths_gap notTrace k5 cap high)
    simp [hr.mem_support] at impossible
  exact ⟨half,hamilton_connected_rooted_exterior connected z least three half cap r hr q hq on longest⟩

#print axioms near_spanning_rooted_exterior
#print axioms hamilton_connected_rooted_exterior
end Graph189RootedSplice




namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}

private theorem kept_gap (p : G.Walk x y) (hp : p.IsPath) {root : V}
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B) (kept : root∈A ∨ root∈B)
    (q : G.Walk a b) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  obtain ⟨u,v,r,hr,rs⟩ := splice_path p hp A J B split q hq dis left right
  have still : root∈r.support := by
    rw [rs]
    simp only [List.mem_append]
    tauto
  have bound := longest r hr still
  have rl := r.length_support
  have pl := p.length_support
  rw [rs] at rl
  rw [split] at pl
  simp only [List.length_append] at rl pl
  omega

private theorem in_take (L : List V) (r j : ℕ) (hr : r<L.length) (before : r<j) :
    L[r] ∈ L.take j :=
  List.mem_take_iff_getElem.mpr ⟨r,by omega,rfl⟩

private theorem in_drop (L : List V) (r j : ℕ) (hr : r<L.length) (after : j≤r) :
    L[r] ∈ L.drop j := by
  refine List.mem_drop_iff_getElem.mpr ⟨r-j,by omega,?_⟩
  simp [Nat.add_sub_of_le after]

private theorem kept_prefix (p : G.Walk x y) (hp : p.IsPath)
    (root : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[root.val]∈r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (side : i.val≤root.val) (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := kept_gap p hp longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (Or.inr (in_drop _ _ _ root.isLt side)) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega

/-- An exterior detour starting at the last specified mark replaces the following suffix. -/
private theorem kept_suffix (p : G.Walk x y) (hp : p.IsPath)
    (root : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[root.val]∈r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (side : root.val≤ i.val) (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := kept_gap p hp longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (Or.inl (in_take _ _ _ root.isLt (by omega))) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega

/-- Every pair of distinct marked positions bounds a gap able to absorb a disjoint detour. -/
private theorem kept_interval (p : G.Walk x y) (hp : p.IsPath)
    (root : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[root.val]∈r.support → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i<j) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (side : root.val≤ i.val ∨ j.val≤root.val) (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := kept_gap p hp longest _ _ _ split
    (side.elim (fun h => Or.inl (in_take _ _ _ root.isLt (by omega))) (fun h => Or.inr (in_drop _ _ _ root.isLt h))) q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega


/-- Mark blocks of length m+1 extend away from the root. Distinct marks on
the same side have disjoint blocks, and the two sides never overlap. -/
private theorem pack_marks (A : Finset ℕ) (r n m : ℕ)
    (inRange : ∀ i∈A, i<n) (before : ∀ i∈A, i≤r → m≤ i)
    (after : ∀ i∈A, r < i → i+m<n)
    (apart : ∀ i∈A, ∀ j∈A, i<j → (j≤r ∨ r≤ i) → i+m<j) :
    A.card*(m+1)≤n := by
  let position (q : A × Fin (m+1)) := if q.1.val ≤ r then q.1.val-q.2.val else q.1.val+q.2.val
  have bound (q : A × Fin (m+1)) : position q < n := by
    have iq := inRange q.1 q.1.property
    have qt := q.2.isLt
    dsimp [position]
    split <;> rename_i side
    · omega
    · have last := after q.1 q.1.property (by omega)
      omega
  let f (q : A × Fin (m+1)) : Fin n := ⟨position q,bound q⟩
  have inj : Function.Injective f := by
    rintro ⟨⟨i,hi⟩,⟨a,ha⟩⟩ ⟨⟨j,hj⟩,⟨b,hb⟩⟩ eq
    have same := congrArg Fin.val eq
    change (if i≤r then i-a else i+a)=(if j≤r then j-b else j+b) at same
    have earlier (x y : ℕ) (hx : x∈A) (hy : y∈A) (lt : x<y) : (y≤r ∨ r≤x) → x+m<y :=
      apart x hx y hy lt
    by_cases l : i≤r <;> by_cases rr : j≤r <;> simp [l,rr] at same
    · have il := before i hi l
      have jl := before j hj rr
      have eqi : i=j := by
        rcases lt_trichotomy i j with h|h|h
        · have := earlier i j hi hj h (Or.inl rr); omega
        · exact h
        · have := earlier j i hj hi h (Or.inl l); omega
      have eqt : a=b := by omega
      subst j; subst b; rfl
    · omega
    · omega
    · have eqi : i=j := by
        rcases lt_trichotomy i j with h|h|h
        · have := earlier i j hi hj h (Or.inr (by omega)); omega
        · exact h
        · have := earlier j i hj hi h (Or.inr (by omega)); omega
      have eqt : a=b := by omega
      subst j; subst b; rfl
  simpa [Fintype.card_prod] using Fintype.card_le_of_injective f inj

/-- A matching into a Hamilton-connected exterior yields m+1 distinct path
positions per matched mark, even when the longest path must contain a prescribed root. -/
theorem rooted_mark_order (p : G.Walk x y) (hp : p.IsPath) {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    (A : Finset ℕ) (port : A → V) (inside : ∀ i : A, i.val<p.support.length)
    (attach : ∀ i : A, G.Adj (p.getVert i.val) (port i)) (m : ℕ)
    (routes : ∀ i j : A, i≠j → ExteriorRoute p (port i) (port j) m)
    (left : ∀ i : A, ∃ a, ExteriorRoute p a (port i) m)
    (right : ∀ i : A, ∃ b, ExteriorRoute p (port i) b m) :
    A.card*(m+1)≤p.support.length := by
  obtain ⟨r,valid,eq⟩ := List.mem_iff_getElem.mp on
  let R : Fin p.support.length := ⟨r,valid⟩
  have max {u v} (q : G.Walk u v) (hq : q.IsPath) (hr : p.support[R.val]∈q.support) :
      q.length≤p.length := longest q hq (eq ▸ hr)
  apply pack_marks A r _ _ (fun i hi => inside ⟨i,hi⟩)
  · intro i hi lr
    obtain ⟨a,q,hq,hd,sz⟩ := left ⟨i,hi⟩
    have h := kept_prefix p hp R max ⟨i,inside ⟨i,hi⟩⟩ q hq hd lr
      (by simpa [get_at] using (attach ⟨i,hi⟩).symm)
    exact sz.trans h
  · intro i hi lr
    obtain ⟨b,q,hq,hd,sz⟩ := right ⟨i,hi⟩
    have h := kept_suffix p hp R max ⟨i,inside ⟨i,hi⟩⟩ q hq hd (by exact lr.le)
      (by simpa [get_at] using attach ⟨i,hi⟩)
    change i+1+q.support.length≤p.support.length at h
    omega
  · intro i hi j hj lt side
    have neq : (⟨i,hi⟩ : A) ≠ ⟨j,hj⟩ := fun h => lt.ne (congrArg Subtype.val h)
    obtain ⟨q,hq,hd,sz⟩ := routes _ _ neq
    have h := kept_interval p hp R max ⟨i,inside ⟨i,hi⟩⟩ ⟨j,inside ⟨j,hj⟩⟩ lt q hq hd side.symm
      (by simpa [get_at] using attach ⟨i,hi⟩) (by simpa [get_at] using (attach ⟨j,hj⟩).symm)
    change i+1+q.support.length ≤ j at h
    omega

#print axioms rooted_mark_order
end Graph189RootedSplice






open SimpleGraph Finset
namespace Graph189RootedSplice
open Graph189ExteriorGap Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] [DecidableRel G.Adj] in
theorem rooted_matching_order {x y : V} (q : G.Walk x y) (hq : q.IsPath) {z : V} (on : z∈q.support)
    (longest : ∀ {c d}, ∀ p : G.Walk c d, p.IsPath → z∈p.support → p.length≤q.length)
    (U : Finset V) (out : ∀ w∈U, w∉q.support) (many : 1<U.card)
    (HC : ∀ i j : U, i≠j → ∃ p : (G.induce (U : Set V)).Walk i j, p.IsHamiltonian)
    (A : Finset U) (f : A ↪ ℕ) (good : ∀ i, f i∈contactPositions q i.val.val) :
    U.card+A.card*(U.card+1)≤Fintype.card V := by
  classical
  let M := (univ : Finset A).map f
  have cnt : M.card=A.card := by simp [M]
  have repr (i : M) : ∃ w : A, f w=i.val := by
    obtain ⟨a,_,h⟩ := mem_map.mp i.property
    exact ⟨a,h⟩
  let w (i : M) := (repr i).choose
  have identify (i : M) : f (w i)=i.val := (repr i).choose_spec
  have edge (i : M) : i.val<q.support.length ∧ G.Adj (q.getVert i.val) (w i).val.val := by
    have pos := (mem_contactPositions q (w i).val.val _).mp (good (w i))
    rwa [identify] at pos
  have route (i j : U) (ne : i≠j) : ExteriorRoute q i.val j.val U.card := by
    obtain ⟨p,hp⟩ := HC i j ne
    exact route_of_induced_hamilton q U out hp
  have another (i : U) : ∃ j : U, j≠i := by
    obtain ⟨s,hs,t,ht,ne⟩ := one_lt_card.mp many
    by_cases eq : s=i.val
    · exact ⟨⟨t,ht⟩,fun h => ne (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨s,hs⟩,fun h => eq (congrArg Subtype.val h)⟩
  have packed := rooted_mark_order q hq on longest M (fun i => (w i).val.val) (fun i => (edge i).1)
    (fun i => (edge i).2) U.card (fun i j ne => route _ _ (by
      intro same
      have ww : w i=w j := Subtype.ext same
      exact ne (Subtype.ext ((identify i).symm.trans ((congrArg f ww).trans (identify j))))))
    (fun i => by obtain ⟨j,ne⟩ := another (w i).val; exact ⟨j.val,route _ _ ne⟩)
    (fun i => by obtain ⟨j,ne⟩ := another (w i).val; exact ⟨j.val,route _ _ ne.symm⟩)
  rw [cnt] at packed
  have all := card_outside_add_path q hq U out
  omega

/-- For the complement of a path through the minimum vertex, every exterior
vertex needs at least k+1−m real contact positions. -/
theorem exterior_contact_minimum {x y : V} (q : G.Walk x y) (hq : q.IsPath) {z : V} (on : z∈q.support)
    (least : G.degree z=G.minDegree) :
    let U := univ \ q.support.toFinset
    ∀ w : U, G.secondSmallestDegree+1-U.card ≤ (contactPositions q w.val).card := by
  intro U w
  let k := G.secondSmallestDegree
  let m := U.card
  have out (w : V) (hw : w∈U) : w∉q.support := fun h => (mem_sdiff.mp hw).2 (List.mem_toFinset.mpr h)
  have wz : w.val≠z := fun h => out _ w.property (h ▸ on)
  have degree : k≤G.degree w.val := by
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) w.val z wz with h|h
    · exact h
    · rw [least] at h
      exact h.trans (G.minDegree_le_degree _)
  have size := card_le_card (show G.neighborFinset w.val \ q.support.toFinset ⊆ U.erase w.val from by
    intro y hy
    have h := mem_sdiff.mp hy
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp h.1).ne.symm,mem_sdiff.mpr ⟨mem_univ _,h.2⟩⟩)
  have cut := card_erase_add_one w.property
  have part := card_sdiff_add_card_inter (G.neighborFinset w.val) q.support.toFinset
  rw [G.card_neighborFinset_eq_degree] at part
  rw [contact_card_neighbors q hq w.val]
  change (U.erase w.val).card+1=m at cut
  change k+1-m ≤ _
  by_cases pos : m≤k+1 <;> omega

/-- A Hamiltonian minimum deletion yields the full lambda-order bound at every
lambda through k+1−m for every rooted-longest path of exterior order m. -/
theorem rooted_matching_cone_order (connected : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z) (k5 : 5≤G.secondSmallestDegree)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (cap : ∀ a, G.distEven a≤G.secondSmallestDegree+1)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b) (hr : r.IsHamiltonian)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (on : z∈q.support)
    (longest : ∀ {c d}, ∀ p : G.Walk c d, p.IsPath → z∈p.support → p.length≤q.length) :
    let U := univ \ q.support.toFinset
    let u := G.secondSmallestDegree+1-U.card
    G.degree z≤u ∧ u≤U.card ∧
    ∀ l, l≤u → (l+1)*(G.secondSmallestDegree-l+2)-1≤Fintype.card V := by
  classical
  intro U u
  obtain ⟨half,small,HC⟩ := near_spanning_rooted_exterior connected z least three k5 notTrace cap r hr q hq on longest
  change U.card ≤ G.secondSmallestDegree+1-G.degree z at small
  change ∀ i j : U, i≠j → ∃ p : (G.induce (U : Set V)).Walk i j, p.IsHamiltonian at HC
  let k := G.secondSmallestDegree
  let m := U.card
  have num : m+u=k+1 := by change m+(k+1-m)=k+1; change m≤k+1-G.degree z at small; omega
  have equal : m+q.support.length=Fintype.card V := by
    have h := card_sdiff_add_card_inter (univ : Finset V) q.support.toFinset
    rwa [univ_inter,List.toFinset_card_of_nodup hq.support_nodup,card_univ] at h
  have skip := rooted_omission z least notTrace (by omega) cap q hq on
  change q.support.length+k/2+1≤Fintype.card V at skip
  change m≤k+1-G.degree z at small
  have many : 1<U.card := by change 1<m; change 5≤k at k5; omega
  have um : u≤m := by omega
  refine ⟨by omega,um,?_⟩
  intro l le
  obtain ⟨A,_,size⟩ := exists_subset_card_eq (s:=(univ : Finset U)) (show u≤(univ : Finset U).card by simpa using um)
  have high := exterior_contact_minimum q hq on least
  obtain ⟨f,good⟩ := hall_on_dense_vertices (fun w : U => contactPositions q w.val) u A size (fun w _ => high w)
  have packed := rooted_matching_order q hq on longest U (fun w hw h => (mem_sdiff.mp hw).2
    (List.mem_toFinset.mpr h)) many HC A f good
  rw [size] at packed
  change m+u*(m+1)≤Fintype.card V at packed
  obtain ⟨d,du⟩ := Nat.exists_eq_add_of_le le
  obtain ⟨e,em⟩ := Nat.exists_eq_add_of_le (le.trans um)
  have eq : k-l+2=l+d+e+1 := by omega
  change (l+1)*(k-l+2)-1≤Fintype.card V
  rw [eq]
  rw [du,em] at packed
  have h : (l+1)*(l+d+e+1)≤Fintype.card V+1 := by nlinarith [Nat.zero_le (d*e)]
  omega

omit [Nontrivial V] [DecidableEq V] in
theorem exists_longest_containing (G : SimpleGraph V) (root : V) :
    ∃ x y, ∃ q : G.Walk x y, q.IsPath ∧ root∈q.support ∧
      ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → root∈r.support → r.length≤q.length := by
  classical
  let Good (m : ℕ) := ∃ a b, ∃ q : G.Walk a b, q.IsPath ∧ root∈q.support ∧ q.length=m
  have base : Good 0 := ⟨root,root,.nil,by simp,by simp,rfl⟩
  obtain ⟨u,v,q,hq,kept,len⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨u,v,q,hq,kept,?_⟩
  intro a b r hr inside
  rw [len]
  have h := r.length_support
  have bound := hr.support_nodup.length_le_card
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨a,b,r,hr,inside,rfl⟩)

#print axioms rooted_matching_cone_order
end Graph189RootedSplice



open SimpleGraph Finset
namespace Graph189RootedSplice
open Graph189ExteriorGap Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem forced_uniform {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (links : L → Finset R) (u : ℕ) (many : u < Fintype.card L) (high : ∀ a, u≤(links a).card)
    (no : ∀ A : Finset L, ∀ f : A ↪ R, (∀ i, f i∈links i.val) → A.card≤u) :
    ∃ T : Finset R, T.card=u ∧ ∀ a, links a=T := by
  classical
  let T := univ.biUnion links
  have sub (a : L) : links a⊆T := fun _ h => mem_biUnion.mpr ⟨a,mem_univ _,h⟩
  obtain ⟨x⟩ : Nonempty L := Fintype.card_pos_iff.mp (by omega)
  have lb := (high x).trans (card_le_card (sub x))
  have upper : T.card≤u := by
    by_contra! big
    have hall (S : Finset L) : S.card ≤ (S.biUnion links).card + (Fintype.card L-(u+1)) := by
      by_cases emp : S=∅
      · simp [emp]
      by_cases all : S=univ
      · simpa [all,T] using (show Fintype.card L≤T.card+(Fintype.card L-(u+1)) by omega)
      obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr emp
      have d := (high a).trans (card_le_card (show links a⊆S.biUnion links from
        fun _ h => mem_biUnion.mpr ⟨a,ha,h⟩))
      have small : S.card < Fintype.card L := by
        simpa using card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,all⟩)
      omega
    obtain ⟨A,sz,f,h⟩ := hall_at_least links (u+1) many hall
    have := no A f h
    omega
  exact ⟨T,by omega,fun a => eq_of_subset_of_card_le (sub a) (upper.trans (high a))⟩

/-- In a near-spanning counterexample with m exterior vertices, m>k+1-m
forces all exterior vertices to be adjacent to the same k+1-m path positions.
This covers every even k and all except the smallest possible m when k is odd. -/
theorem common_marks_of_large_exterior (connected : G.Connected) (z : V)
    (least : G.degree z=G.minDegree) (three : 3≤G.degree z) (k5 : 5≤G.secondSmallestDegree)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (cap : ∀ a, G.distEven a≤G.secondSmallestDegree+1)
    {a b : {w : V | w≠z}} (r : (G.induce {w : V | w≠z}).Walk a b) (hr : r.IsHamiltonian)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (on : z∈q.support)
    (longest : ∀ {c d}, ∀ p : G.Walk c d, p.IsPath → z∈p.support → p.length≤q.length) :
    let U := univ \ q.support.toFinset
    let u := G.secondSmallestDegree+1-U.card
    u<U.card → ∃ T : Finset ℕ, T.card=u ∧ ∀ w : U, contactPositions q w.val=T := by
  classical
  intro U u large
  obtain ⟨half,small,HC⟩ := near_spanning_rooted_exterior connected z least three k5 notTrace cap r hr q hq on longest
  change U.card ≤ G.secondSmallestDegree+1-G.degree z at small
  change ∀ i j : U, i≠j → ∃ p : (G.induce (U : Set V)).Walk i j, p.IsHamiltonian at HC
  let m := U.card
  let k := G.secondSmallestDegree
  let d := G.degree z
  have num : m+u=k+1 := by change m+(k+1-m)=k+1; change m≤k+1-d at small; omega
  have equal : m+q.support.length=Fintype.card V := by
    have h := card_sdiff_add_card_inter (univ : Finset V) q.support.toFinset
    rwa [univ_inter,List.toFinset_card_of_nodup hq.support_nodup,card_univ] at h
  have skip := rooted_omission z least notTrace (by omega) cap q hq on
  change q.support.length+k/2+1≤Fintype.card V at skip
  change 2*d≤k at half
  change m≤k+1-d at small
  change 3≤d at three
  have du : d≤u := by omega
  have dm : d<m := by omega
  have bound := Graph189LayerCutoff.order_of_small_degree G connected z k cap (by omega)
  change Fintype.card V≤1+d+k+d*(k+1-d) at bound
  have upp : Fintype.card V ≤ m+u+d+m*u := by
    have prod : d*(k+1-d)≤m*u := by
      obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le dm.le
      obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le du
      have eq : k+1-d=d+a+b := by omega
      rw [ha,hb,eq]
      nlinarith [Nat.zero_le (a*b)]
    omega
  have high (w : U) : u≤(contactPositions q w.val).card := exterior_contact_minimum q hq on least w
  apply forced_uniform (fun w : U => contactPositions q w.val) u (by simpa using large) high
  intro A f good
  have many : 1<U.card := by change 1<m; omega
  have packed := rooted_matching_order q hq on longest U (fun w hw h => (mem_sdiff.mp hw).2
    (List.mem_toFinset.mpr h)) many HC A f good
  change m+A.card*(m+1)≤Fintype.card V at packed
  by_contra! big
  have psize := Nat.mul_le_mul_right (m+1) (show u+1≤A.card by omega)
  nlinarith only [packed,equal,upp,dm,psize]

omit [Nontrivial V] in
/-- If all high exterior vertices realize exactly the minimum number of path
contacts, they are pairwise adjacent in the original graph. -/
theorem clique_of_exact_contacts {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (U : Finset V) (complete : ∀ a, a∈U ↔ a∉p.support) {k u : ℕ}
    (balance : U.card+u=k+1) (degree : ∀ a∈U, k≤G.degree a)
    (exactContacts : ∀ a∈U, (contactPositions p a).card=u) :
    ∀ a∈U, ∀ b∈U, a≠b → G.Adj a b := by
  intro a ha b hb ne
  let D := G.neighborFinset a \ p.support.toFinset
  have sub : D⊆U.erase a := by
    intro x hx
    obtain ⟨adj,off⟩ := mem_sdiff.mp hx
    exact mem_erase.mpr ⟨((G.mem_neighborFinset a x).mp adj).ne.symm,
      (complete x).mpr (fun h => off (List.mem_toFinset.mpr h))⟩
  have split := card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  rw [←contact_card_neighbors p hp a,exactContacts a ha,G.card_neighborFinset_eq_degree] at split
  have one := card_erase_add_one ha
  have high := degree a ha
  change D.card+u=G.degree a at split
  have eq := eq_of_subset_of_card_le sub (by omega)
  have inside := mem_erase.mpr ⟨ne.symm,hb⟩
  rw [←eq] at inside
  exact (G.mem_neighborFinset a b).mp (mem_sdiff.mp inside).1

#print axioms clique_of_exact_contacts
#print axioms common_marks_of_large_exterior
end Graph189RootedSplice




namespace Graph189RootedSplice
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem connectivity_le_degree (v : V) : G.vertexConnectivity≤G.degree v := by
  classical
  let N := G.neighborFinset v
  let U := (N : Set V)ᶜ
  have hn := Fintype.one_lt_card (α:=V)
  unfold vertexConnectivity
  rw [if_neg (by omega : ¬Fintype.card V≤1)]
  apply Nat.sInf_le
  refine ⟨N,G.card_neighborFinset_eq_degree _,?_⟩
  by_cases eq : N.card=Fintype.card V-1
  · exact Or.inr eq
  left
  have count : Fintype.card U=Fintype.card V-N.card := by
    change Fintype.card {z : V // ¬z∈N}=Fintype.card V-N.card
    rw [Fintype.card_subtype_compl (fun z : V => z∈N), Fintype.card_coe]
  have bound := G.degree_lt_card_verts v
  have card : N.card=G.degree v := G.card_neighborFinset_eq_degree _
  have : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have off : v∈U := fun e => G.irrefl ((G.mem_neighborFinset _ _).mp e)
  intro con
  obtain ⟨b,edge⟩ := con.preconnected.exists_adj_of_nontrivial (⟨v,off⟩ : U)
  exact b.property ((G.mem_neighborFinset _ _).mpr edge)

/-- A traceable minimum deletion gives the full order inequality at every
parameter up to the connectivity when the connectivity is at least three, with no connectivity ratio required. -/
theorem order_of_hamiltonian_deletion_up_to_connectivity (hc : G.Connected)
    (z : V) (least : G.degree z = G.minDegree) (three : 3 ≤ G.vertexConnectivity)
    (k5 : 5 ≤ G.secondSmallestDegree) (cap : ∀ w, G.distEven w ≤ G.secondSmallestDegree+1)
    (fail : ¬ ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian)
    {u v : {w : V | w≠z}} (p : (G.induce {w : V | w≠z}).Walk u v) (hp : p.IsHamiltonian)
    (l : ℕ) (hl : l ≤ G.vertexConnectivity) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V := by
  obtain ⟨a,b,q,hq,on,maximal⟩ := exists_longest_containing G z
  have sd : G.vertexConnectivity ≤ G.degree z := connectivity_le_degree z
  obtain ⟨du,_,bound⟩ := rooted_matching_cone_order hc z least (three.trans sd) k5 fail cap p hp q hq on maximal
  exact bound l (hl.trans (sd.trans du))

#print axioms order_of_hamiltonian_deletion_up_to_connectivity

/-- Under the exact qualifying graph hypotheses in the structural range, any
nontraceable Hamiltonian-minimum-deletion example has minimum degree precisely
its connectivity s. The exterior of every longest path through that vertex is a
(k+1−s)-clique, completely adjacent to exactly s path positions. -/
theorem exact_near_counterexample (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree)
    (z : V) (least : G.degree z=G.minDegree)
    (fail : ¬ ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian)
    {u v : {b : V | b≠z}} (p : (G.induce {b : V | b≠z}).Walk u v) (hp : p.IsHamiltonian)
    {x y : V} (q : G.Walk x y) (hq : q.IsPath) (on : z∈q.support)
    (longest : ∀ {c d}, ∀ r : G.Walk c d, r.IsPath → z∈r.support → r.length≤q.length) :
    let U := univ \ q.support.toFinset
    G.degree z=G.vertexConnectivity ∧ U.card=G.secondSmallestDegree+1-G.vertexConnectivity ∧
    (∃ T : Finset ℕ, T.card=G.vertexConnectivity ∧ ∀ i : U, Graph189ExteriorGap.contactPositions q i.val=T) ∧
    ∀ a∈U, ∀ b∈U, a≠b → G.Adj a b := by
  classical
  intro U
  let k := G.secondSmallestDegree
  let s := G.vertexConnectivity
  let u := k+1-U.card
  let n := Fintype.card V
  have point (a : V) : G.distEven a≤G.secondSmallestDegree+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ a))).trans cap
    omega
  have sd : s≤G.degree z := connectivity_le_degree z
  change 5≤s at hs
  change 26≤k at hk
  have three : 3≤G.degree z := by omega
  obtain ⟨su,um,order⟩ := rooted_matching_cone_order hc z least three (by exact (by omega : 5≤k)) fail point p hp q hq on longest
  change G.degree z≤u at su
  change u≤U.card at um
  change ∀ l, l≤u → (l+1)*(k-l+2)-1≤n at order
  have sr : 3*s<k := ratio
  have signed (l : ℕ) (room : l≤k) (le : l≤u) : ((l:ℤ)+1)*((k:ℤ)-l+2)-1≤n := by
    have lower := order l le
    have bound : (l+1)*(k-l+2)≤n+1 := by omega
    have cast : ((l:ℤ)+1)*((↑(k-l) : ℤ)+2)≤(n:ℤ)+1 := by exact_mod_cast bound
    rw [Nat.cast_sub room] at cast
    omega
  have exactU : u=s := by
    by_contra neq
    have base := signed s (by omega) (by omega)
    have lift := signed (s+1) (by omega) (by omega)
    push_cast at lift
    apply fail
    apply Graph189StructuralConclusion.traceable_of_structural_lower_bounds hc cap deletion hs hk ratio
    · exact base
    · intro _ _ _
      let d : ℤ := Graph189EffectiveDeficit.effectiveDeficit G
      change ((s:ℤ)+2)*((k:ℤ)-d-s+1)-1≤(n:ℤ)
      have loss : 0≤((s:ℤ)+2)*d := mul_nonneg (by positivity) (Int.natCast_nonneg _)
      linarith only [lift,loss]
  have dEq : G.degree z=s := by omega
  have mEq : U.card=k+1-s := by
    change k+1-U.card=s at exactU
    omega
  have many : u<U.card := by omega
  obtain ⟨T,size,same⟩ := common_marks_of_large_exterior hc z least three (by exact (by omega : 5≤k)) fail point p hp q hq on longest many
  refine ⟨dEq,mEq,⟨T,size.trans exactU,same⟩,?_⟩
  apply clique_of_exact_contacts q hq U (fun a => by simp [U]) (k:=k) (u:=u) (by omega) _ _
  · intro a ha
    have az : a≠z := fun h => (mem_sdiff.mp ha).2 (List.mem_toFinset.mpr (h ▸ on))
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a z az with h|h
    · exact h
    · rw [least] at h
      exact h.trans (G.minDegree_le_degree _)
  · intro a ha
    rw [same ⟨a,ha⟩]
    exact size

#print axioms connectivity_le_degree
#print axioms exact_near_counterexample
end Graph189RootedSplice



namespace Graph189RootedSplice
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- One entire gap in a path between consecutive marks, allowing either outer
tail. Its bounding marks survive replacement and one touches its interior. -/
structure TightGap (p : G.Walk x y) (z : V) (m : ℕ) where
  left : List V
  block : List V
  right : List V
  split : p.support = left ++ block ++ right
  size : block.length = m
  before : ∀ t∈left.getLast?, G.Adj t z
  after : ∀ t∈right.head?, G.Adj z t
  unmarked : ∀ t∈block, ¬G.Adj z t
  boundary : ∃ b, b∈left++right ∧ G.Adj z b ∧ ∃ t∈block, G.Adj b t

end Graph189RootedSplice




namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

def pathSegment (p : G.Walk x y) (lo hi : ℕ) : List V := (p.support.drop lo).take (hi-lo)

private theorem segment_split (p : G.Walk x y) (lo hi : ℕ) (ordered : lo≤hi) :
    p.support = p.support.take lo ++ pathSegment p lo hi ++ p.support.drop hi := by
  rw [pathSegment,←List.take_add,Nat.add_sub_of_le ordered,List.take_append_drop]

theorem segment_size (p : G.Walk x y) {lo hi : ℕ} (endBound : hi≤p.support.length) :
    (pathSegment p lo hi).length=hi-lo := by
  simp only [pathSegment,List.length_take,List.length_drop]
  exact Nat.min_eq_left (Nat.sub_le_sub_right endBound lo)

theorem segment_member (p : G.Walk x y) {lo hi : ℕ} (endBound : hi≤p.support.length) (w : V) :
    w∈pathSegment p lo hi ↔ ∃ j, lo≤j ∧ j<hi ∧ p.getVert j=w := by
  constructor
  · intro member
    obtain ⟨r,hr,eq⟩ := List.mem_take_iff_getElem.mp member
    have range : r < (p.support.drop lo).length := by omega
    have bound : lo+r<p.support.length := by simp only [List.length_drop] at range; omega
    rw [List.getElem_drop] at eq
    exact ⟨lo+r,by omega,by omega,(get_at p bound).symm.trans eq⟩
  · rintro ⟨j,l,r,rfl⟩
    apply List.mem_take_iff_getElem.mpr
    refine ⟨j-lo,?_,?_⟩
    · simp only [List.length_drop]
      omega
    · rw [List.getElem_drop]
      simpa [Nat.add_sub_of_le l] using get_at p (r.trans_le endBound)

theorem disjoint_segments (p : G.Walk x y) (hp : p.IsPath) {l₁ h₁ l₂ h₂ : ℕ}
    (end₁ : h₁≤p.support.length) (end₂ : h₂≤p.support.length) (separate : h₁≤l₂) :
    List.Disjoint (pathSegment p l₁ h₁) (pathSegment p l₂ h₂) := by
  apply List.disjoint_left.mpr
  intro w a b
  obtain ⟨i,li,hi,fi⟩ := (segment_member p end₁ w).mp a
  obtain ⟨j,lj,hj,fj⟩ := (segment_member p end₂ w).mp b
  have eq := hp.getVert_injOn (show i∈{i | i ≤ p.length} by
    change i≤p.length; have := p.length_support; omega) (show j∈{i | i ≤ p.length} by
    change j≤p.length; have := p.length_support; omega) (fi.trans fj.symm)
  omega

theorem coordinate_neighbors (p : G.Walk x y) (z : V) (lo hi : ℕ)
    (ordered : lo≤hi) (bound : hi≤p.support.length)
    (before : 0<lo → G.Adj (p.getVert (lo-1)) z)
    (after : hi<p.support.length → G.Adj z (p.getVert hi)) :
    (∀ w∈(p.support.take lo).getLast?, G.Adj w z) ∧ (∀ w∈(p.support.drop hi).head?, G.Adj z w) := by
  let A := p.support.take lo
  let B := p.support.drop hi
  have lc (h : 0<lo) : A.getLast?=some (p.getVert (lo-1)) := by
    let i := lo-1
    have eq : lo=i+1 := by dsimp [i]; omega
    have range := bound
    have valid : i<p.support.length := by omega
    change (p.support.take lo).getLast?=some (p.getVert i)
    rw [eq,List.take_succ_eq_append_getElem valid,List.getLast?_concat,get_at p valid]
  have rc (h : hi<p.support.length) : B.head? = some (p.getVert hi) := by
    simp [B,List.head?_drop,List.getElem?_eq_getElem h,get_at]
  have left (w : V) (hw : w∈A.getLast?) : G.Adj w z := by
    by_cases h : 0<lo
    · rw [lc h] at hw
      have eq : p.getVert (lo-1)=w := by simpa using hw
      exact eq ▸ before h
    · have small : lo=0 := by omega
      simp [A,small] at hw
  have right (w : V) (hw : w∈B.head?) : G.Adj z w := by
    by_cases h : hi<p.support.length
    · rw [rc h] at hw
      have eq : p.getVert hi=w := by simpa using hw
      exact eq ▸ after h
    · have last : hi=p.support.length := by omega
      simp [B,last] at hw
  exact ⟨left,right⟩

/-- The two cut positions specify an actual z-gap when both possible bounding
marks touch z and all vertices at intermediate indices are unmarked. -/
theorem gap_from_coordinates (p : G.Walk x y) (z : V) {lo hi : ℕ}
    (pos : lo<hi) (bound : hi≤p.support.length)
    (before : 0<lo → G.Adj (p.getVert (lo-1)) z)
    (after : hi<p.support.length → G.Adj z (p.getVert hi))
    (nontrivial : 0<lo ∨ hi<p.support.length)
    (free : ∀ j, lo≤j → j<hi → ¬G.Adj z (p.getVert j)) :
    ∃ g : TightGap p z (hi-lo), g.block=pathSegment p lo hi := by
  let A := p.support.take lo
  let J := pathSegment p lo hi
  let B := p.support.drop hi
  obtain ⟨left,right⟩ := coordinate_neighbors p z lo hi pos.le bound before after
  refine ⟨⟨A,J,B,segment_split p lo hi pos.le,segment_size p bound,left,right,?_,?_⟩,rfl⟩
  · intro w hw
    obtain ⟨j,jl,jr,rfl⟩ := (segment_member p bound w).mp hw
    exact free j jl jr
  · rcases nontrivial with head|tail
    · have i : lo-1 < p.support.length := by omega
      have mark : p.getVert (lo-1)∈A := by
        rw [←get_at p i]
        exact inTake p.support (lo-1) lo i (by omega)
      refine ⟨_,List.mem_append_left _ mark,(before head).symm,p.getVert lo,
        (segment_member p bound _).mpr ⟨lo,le_rfl,pos,rfl⟩,?_⟩
      have adj := p.adj_getVert_succ (i:=lo-1) (by have := p.length_support; omega)
      rwa [show lo-1+1=lo by omega] at adj
    · have mark : p.getVert hi∈B := by
        apply List.mem_drop_iff_getElem.mpr
        exact ⟨0,by omega,by simpa using get_at p tail⟩
      refine ⟨_,List.mem_append_right _ mark,after tail,p.getVert (hi-1),
        (segment_member p bound _).mpr ⟨hi-1,by omega,by omega,rfl⟩,?_⟩
      have adj := p.adj_getVert_succ (i:=hi-1) (by have := p.length_support; omega)
      rw [show hi-1+1=hi by omega] at adj
      exact adj.symm
where
  inTake (L : List V) (i j : ℕ) (hi : i<L.length) (small : i<j) : L[i]∈L.take j :=
    List.mem_take_iff_getElem.mpr ⟨i,by omega,rfl⟩

/-- Even a possibly empty contact-free interval can be used to insert z, so
its actual length is at least the known rooted omission. -/
theorem coordinate_gap_lower [Fintype V] (p : G.Walk x y) (hp : p.IsPath) (z : V)
    (off : z∉p.support) (near : p.support.length+1=Fintype.card V) (m lo hi : ℕ)
    (ordered : lo≤hi) (bound : hi≤p.support.length)
    (left : ∀ t∈(p.support.take lo).getLast?, G.Adj t z)
    (right : ∀ t∈(p.support.drop hi).head?, G.Adj z t)
    (max : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → z∈q.support → q.support.length+m≤Fintype.card V) :
    m≤hi-lo := by
  obtain ⟨u,v,r,hr,rs⟩ := splice_path p hp _ _ _ (segment_split p lo hi ordered)
    (Walk.nil : G.Walk z z) (by simp) (by simpa [List.disjoint_left] using off) left right
  have h := max r hr (by simp [rs])
  have old := near
  rw [segment_split p lo hi ordered] at old
  rw [rs] at h
  simp only [List.length_append,Walk.support_nil,List.length_singleton] at old h
  rw [segment_size p bound] at old
  omega

#print axioms gap_from_coordinates
#print axioms coordinate_gap_lower
end Graph189RootedSplice





namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {x y : V}

/-- Extract two disjoint actual tight gaps from the ordered neighbors of the
missing vertex on a spanning path of its deletion. -/
theorem two_tight_contact_gaps (p : G.Walk x y) (hp : p.IsPath) (z : V) (off : z∉p.support)
    (near : p.support.length+1=Fintype.card V) (m : ℕ) (positive : 1≤m)
    (marksPositive : 1≤(contactPositions p z).card)
    (upper : Fintype.card V ≤ ((contactPositions p z).card+1)*m+2*(contactPositions p z).card)
    (max : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → z∈q.support → q.support.length+m≤Fintype.card V) :
    ∃ A B : TightGap p z m, List.Disjoint A.block B.block := by
  classical
  let A := contactPositions p z
  let d := A.card
  let L := p.support.length
  let mark : Fin d ↪o ℕ := A.orderEmbOfFin rfl
  have real (i : Fin d) : mark i<L ∧ G.Adj (p.getVert (mark i)) z :=
    (mem_contactPositions p z _).mp (A.orderEmbOfFin_mem rfl i)
  let f : ℕ → ℕ
    | 0 => 0
    | j+1 => if h : j<d then mark ⟨j,h⟩+1 else L+1
  let hi (i : Fin (d+1)) := if h : i.val<d then mark ⟨i.val,h⟩ else L
  have successor (i : Fin (d+1)) : f (i.val+1)=hi i+1 := by
    by_cases h : i.val<d <;> simp [f,hi,h]
  have endBound (i : Fin (d+1)) : hi i≤L := by
    dsimp [hi]
    split <;> rename_i h
    · exact (real ⟨i.val,h⟩).1.le
    · rfl
  have loBound (i : Fin (d+1)) : f i.val≤hi i := by
    rcases i with ⟨i,ir⟩
    cases i with
    | zero => simp [f]
    | succ j =>
      have jd : j<d := by omega
      change f (j+1) ≤ if t : j+1<d then mark ⟨j+1,t⟩ else L
      simp only [f,dif_pos jd]
      split <;> rename_i h
      · exact mark.strictMono (show (⟨j,jd⟩ : Fin d) < ⟨j+1,h⟩ by exact Nat.lt_succ_self j)
      · exact (real ⟨j,jd⟩).1
  have before (i : Fin (d+1)) (positive : 0<f i.val) : G.Adj (p.getVert (f i.val-1)) z := by
    rcases i with ⟨i,ir⟩
    cases i with
    | zero => simp [f] at positive
    | succ j =>
      have jd : j<d := by omega
      simpa [f,jd] using (real ⟨j,jd⟩).2
  have after (i : Fin (d+1)) (below : hi i<L) : G.Adj z (p.getVert (hi i)) := by
    by_cases h : i.val<d
    · simpa [hi,h] using (real ⟨i.val,h⟩).2.symm
    · simp [hi,h] at below
  have oneBound (i : Fin (d+1)) : 0<f i.val ∨ hi i<L := by
    rcases i with ⟨i,ir⟩
    cases i with
    | zero =>
      have h : 0<d := marksPositive
      exact Or.inr (by simpa [hi,h] using (real ⟨0,h⟩).1)
    | succ j =>
      have jd : j<d := by omega
      exact Or.inl (by simp [f,jd])
  have silent (i : Fin (d+1)) (t : ℕ) (lt : f i.val≤t) (tr : t<hi i) : ¬G.Adj z (p.getVert t) := by
    intro edge
    have trange : t<p.support.length := tr.trans_le (endBound i)
    have tin : t∈A := (mem_contactPositions p z t).mpr ⟨trange,edge.symm⟩
    let iso := A.orderIsoOfFin (show A.card=d from rfl)
    let pos : Fin d := iso.symm ⟨t,tin⟩
    have value : mark pos=t := congrArg Subtype.val (iso.apply_symm_apply ⟨t,tin⟩)
    by_cases less : pos.val < i.val
    · rcases i with ⟨iv,ir⟩
      cases iv with
      | zero => exact (Nat.not_lt_zero _ less).elim
      | succ j =>
        have jd : j<d := by omega
        have le : pos≤(⟨j,jd⟩ : Fin d) := by change pos.val≤j; exact Nat.le_of_lt_succ less
        have bound := mark.monotone le
        change f (j+1)≤t at lt
        rw [show f (j+1)=mark ⟨j,jd⟩+1 by simp [f,jd]] at lt
        omega
    · have iRange : i.val<d := by have := pos.isLt; omega
      have le : (⟨i.val,iRange⟩ : Fin d) ≤ pos := by change i.val≤pos.val; omega
      have mono := mark.monotone le
      rw [show hi i=mark ⟨i.val,iRange⟩ by simp [hi,iRange]] at tr
      omega
  have lower (i : Fin (d+1)) : m≤hi i-f i.val := by
    obtain ⟨left,right⟩ := coordinate_neighbors p z (f i.val) (hi i) (loBound i) (endBound i) (before i) (after i)
    exact coordinate_gap_lower p hp z off near m _ _ (loBound i) (endBound i) left right max
  have lengths (i : Fin (d+1)) : m≤ f (i.val+1)-f i.val-1 := by
    have bound := lower i
    have lo := loBound i
    rw [successor]
    omega
  have ending : f (d+1)≤(d+1)*m+2*d := by
    have last : f (d+1) = L+1 := by simp only [f,lt_self_iff_false,dif_neg,not_false_eq_true]
    rw [last]
    change p.support.length+1 ≤ (d+1)*m+2*d
    rw [near]
    exact upper
  obtain ⟨i,j,lt,gi,gj⟩ := two_tight_gaps f positive lengths ending
  have witness (i : Fin (d+1)) (tight : f (i.val+1)-f i.val-1=m) :
      ∃ g : TightGap p z m, g.block=pathSegment p (f i.val) (hi i) := by
    rw [successor] at tight
    have order := loBound i
    have eq : hi i-f i.val=m := by omega
    obtain ⟨g,hg⟩ := gap_from_coordinates p z (by omega : f i.val<hi i) (endBound i)
      (before i) (after i) (oneBound i) (silent i)
    exact eq ▸ ⟨g,hg⟩
  obtain ⟨g,hg⟩ := witness i gi
  obtain ⟨h,hh⟩ := witness j gj
  refine ⟨g,h,?_⟩
  rw [hg,hh]
  apply disjoint_segments p hp (endBound i) (endBound j)
  have ij : i.val<j.val := lt
  rcases j with ⟨j,jr⟩
  cases j with
  | zero => exact (Nat.not_lt_zero _ ij).elim
  | succ b =>
    have br : b<d := by omega
    have ir : i.val<d := by omega
    have le := mark.monotone (show (⟨i.val,ir⟩ : Fin d)≤⟨b,br⟩ from Nat.le_of_lt_succ ij)
    change hi i≤f (b+1)
    simp [hi,f,ir,br]
    omega

#print axioms two_tight_contact_gaps
end Graph189RootedSplice




namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

omit [DecidableEq V] in
/-- A tight gap that becomes a uniform exterior after splicing consists of
genuine two-distance witnesses of the omitted vertex of the original path. -/
private theorem tight_gap_two (p : G.Walk x y) (hp : p.IsPath) (z : V) (outside : z∉p.support)
    (near : p.support.length+1=Fintype.card V) (m : ℕ) (gap : TightGap p z m)
    (uniform : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z∈r.support → r.support.length+m=Fintype.card V →
      ∀ a, a∉r.support → ∀ b, b∉r.support → ∀ t∈r.support, G.Adj t a → G.Adj t b) :
    ∀ w∈gap.block, G.dist z w=2 := by
  obtain ⟨u,v,r,hr,supp⟩ := splice_path p hp gap.left gap.block gap.right gap.split
    (Walk.nil : G.Walk z z) (by simp) (by simpa [List.disjoint_left] using outside) gap.before gap.after
  have kept : z∈r.support := by simp [supp]
  have size : r.support.length+m=Fintype.card V := by
    rw [supp]
    rw [gap.split] at near
    have sz := gap.size
    simp only [Walk.support_nil,List.length_singleton,List.length_append] at near ⊢
    omega
  have old := hp.support_nodup
  rw [gap.split] at old outside
  have out (i : V) (hi : i∈gap.block) : i∉r.support := by
    rw [supp]
    simp only [List.mem_append,Walk.support_nil,List.mem_singleton]
    rintro ((h|rfl)|h)
    · exact List.disjoint_left.mp old.of_append_left.disjoint h hi
    · exact outside (List.mem_append_left _ (List.mem_append_right _ hi))
    · exact List.disjoint_left.mp old.disjoint (List.mem_append_right _ hi) h
  obtain ⟨b,hb,zb,t,ht,bt⟩ := gap.boundary
  have inside : b∈r.support := by
    rw [supp]
    simp only [List.mem_append] at hb ⊢
    tauto
  intro w hw
  have different : z≠w := by
    rintro rfl
    exact outside (List.mem_append_left _ (List.mem_append_right _ hw))
  have edge := uniform r hr kept size t (out t ht) w (out w hw) b inside bt
  exact two_step_metric different (gap.unmarked w hw) zb edge.symm

/-- Two distinct tight original gaps force twice their common length into the
actual even-distance allowance of z, allowing an outer gap at either end. -/
theorem two_tight_gaps_force_cap (p : G.Walk x y) (hp : p.IsPath) (z : V) (outside : z∉p.support)
    (near : p.support.length+1=Fintype.card V) {m k : ℕ} (g h : TightGap p z m)
    (disjoint : List.Disjoint g.block h.block) (cap : G.distEven z≤k+1)
    (uniform : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z∈r.support → r.support.length+m=Fintype.card V →
      ∀ a, a∉r.support → ∀ b, b∉r.support → ∀ t∈r.support, G.Adj t a → G.Adj t b) : 2*m≤k := by
  classical
  let S := g.block.toFinset ∪ h.block.toFinset
  have dis : Disjoint g.block.toFinset h.block.toFinset := Finset.disjoint_left.mpr
    (fun i hi hj => List.disjoint_left.mp disjoint (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj))
  have nd (a : TightGap p z m) : a.block.Nodup := by
    have n := hp.support_nodup
    rw [a.split] at n
    exact n.of_append_left.of_append_right
  have size : S.card=2*m := by
    simp only [S,card_union_of_disjoint dis,List.toFinset_card_of_nodup (nd g),
      List.toFinset_card_of_nodup (nd h),g.size,h.size]
    omega
  have two (w : V) (hw : w∈S) : G.dist z w=2 := by
    rcases mem_union.mp hw with a|b
    · exact tight_gap_two p hp z outside near m g uniform w (List.mem_toFinset.mp a)
    · exact tight_gap_two p hp z outside near m h uniform w (List.mem_toFinset.mp b)
  have absent : z∉S := by intro h; have := two z h; simp at this
  have cover : insert z S ⊆ univ.filter (fun w => Even (G.dist z w)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [two w h]; decide⟩
  have count := card_le_card cover
  rw [card_insert_of_notMem absent,size] at count
  change 2*m+1≤G.distEven z at count
  omega

#print axioms two_tight_gaps_force_cap
end Graph189RootedSplice





namespace Graph189RootedSplice
open SimpleGraph Finset Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every graph in the structural range with a Hamiltonian minimum deletion
has an actual Hamiltonian path in the original graph, at unrestricted minimum degree. -/
theorem traceable_of_near_spanning (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree)
    (z : V) (least : G.degree z=G.minDegree)
    {u v : {b : V | b≠z}} (r : (G.induce {b : V | b≠z}).Walk u v) (hr : r.IsHamiltonian) :
    ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  by_contra fail
  let k := G.secondSmallestDegree
  let s := G.vertexConnectivity
  let n := Fintype.card V
  obtain ⟨a,b,q,hq,on,maximal⟩ := exists_longest_containing G z
  let U := univ \ q.support.toFinset
  let m := U.card
  obtain ⟨ds,ms,_,_⟩ := exact_near_counterexample hc cap deletion hs hk ratio z least fail r hr q hq on maximal
  change G.degree z=s at ds
  change m=k+1-s at ms
  have sr : 3*s<k := ratio
  change 5≤s at hs
  have positive : 1≤m := by omega
  have exactSize : m+q.support.length=n := by
    have h := card_sdiff_add_card_inter (univ : Finset V) q.support.toFinset
    rwa [univ_inter,List.toFinset_card_of_nodup hq.support_nodup,card_univ] at h
  have allmax {x y} (t : G.Walk x y) (ht : t.IsPath) (hz : z∈t.support) :
      t.support.length+m≤Fintype.card V := by
    have bound := maximal t ht hz
    have tl := t.length_support
    have ql := q.length_support
    change t.support.length+m≤n
    omega
  have point (w : V) : G.distEven w≤k+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ w))).trans cap
    change G.distEven w≤G.secondSmallestDegree+1
    omega
  have upper := Graph189LayerCutoff.order_of_small_degree G hc z k point (by omega)
  change n≤1+G.degree z+k+G.degree z*(k+1-G.degree z) at upper
  rw [ds,←ms] at upper
  have nBound : n≤(s+1)*m+2*s := by
    have eq : m+s=k+1 := by omega
    nlinarith only [upper,eq]
  let S := {t : V | t≠z}
  let f := (Embedding.induce (G:=G) S).toHom
  let p := r.map f
  have path : p.IsPath := hr.isPath.map Subtype.val_injective
  have supp : p.support=List.map Subtype.val r.support := Walk.support_map f r
  have off : z ∉ p.support := by
    rw [supp]
    intro h
    obtain ⟨v,_,eq⟩ := List.mem_map.mp h
    exact v.property eq
  have inside (v : V) (ne : v≠z) : v∈p.support := by
    rw [supp]
    exact List.mem_map.mpr ⟨⟨v,ne⟩,hr.mem_support _,rfl⟩
  have cover : insert z p.support.toFinset=univ := by
    ext w
    simp only [mem_insert,List.mem_toFinset,mem_univ,iff_true]
    exact (em (w=z)).imp_right (inside w)
  have near : p.support.length+1=Fintype.card V := by
    have sz := congrArg Finset.card cover
    rwa [card_insert_of_notMem (fun h => off (List.mem_toFinset.mp h)),List.toFinset_card_of_nodup path.support_nodup,card_univ] at sz
  have marks : (contactPositions p z).card=s := by
    have sub : G.neighborFinset z⊆p.support.toFinset := fun w hw =>
      List.mem_toFinset.mpr (inside w ((G.mem_neighborFinset _ _).mp hw).ne.symm)
    rw [contact_card_neighbors p path z,inter_eq_left.mpr sub,G.card_neighborFinset_eq_degree,ds]
  obtain ⟨g,h,dis⟩ := two_tight_contact_gaps p path z off near m positive (by omega)
    (by rw [marks]; exact nBound) allmax
  have even := two_tight_gaps_force_cap p path z off near g h dis (point z) (by
    intro i j t ht member total
    have len : t.length=q.length := by
      have tl := t.length_support
      have ql := q.length_support
      change t.support.length+m=n at total
      omega
    have maximal' {i j} (w : G.Walk i j) (hw : w.IsPath) (hz : z∈w.support) : w.length≤t.length := by
      rw [len]
      exact maximal w hw hz
    obtain ⟨_,_,⟨T,_,same⟩,_⟩ := exact_near_counterexample hc cap deletion hs hk ratio z least fail r hr t ht member maximal'
    intro i outside j absent b hb edge
    obtain ⟨v,valid,eq⟩ := List.mem_iff_getElem.mp hb
    have hit : t.getVert v=b := (get_at t valid).symm.trans eq
    have wi : i∈univ \ t.support.toFinset := mem_sdiff.mpr ⟨mem_univ _,fun h => outside (List.mem_toFinset.mp h)⟩
    have wj : j∈univ \ t.support.toFinset := mem_sdiff.mpr ⟨mem_univ _,fun h => absent (List.mem_toFinset.mp h)⟩
    have ci : v∈contactPositions t i := (mem_contactPositions t i v).mpr ⟨valid,hit ▸ edge⟩
    have ciEq := same ⟨i,wi⟩
    have cjEq := same ⟨j,wj⟩
    change contactPositions t i=T at ciEq
    change contactPositions t j=T at cjEq
    rw [ciEq,←cjEq] at ci
    have cj := ((mem_contactPositions t j v).mp ci).2
    rwa [hit] at cj)
  omega

/-- The connectivity bound itself supplies connectedness of every singleton deletion. -/
theorem traceable_of_near_in_structural_range (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (hs : 5≤G.vertexConnectivity) (hk : 26≤G.secondSmallestDegree)
    (ratio : 3*G.vertexConnectivity<G.secondSmallestDegree)
    (z : V) (least : G.degree z=G.minDegree)
    {u v : {b : V | b≠z}} (r : (G.induce {b : V | b≠z}).Walk u v) (hr : r.IsHamiltonian) :
    ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  have deletion (w : V) : (G.induce {v : V | v≠w}).Connected := by
    have equal : {v : V | v∉({w} : Finset V)} = {v : V | v≠w} := by
      ext v
      simp only [Set.mem_ofPred_eq,Finset.mem_singleton]
    rw [←equal]
    exact Graph189CutSides.connected_after_smaller_deletion (G:=G) ({w} : Finset V)
      (by simp; omega : ({w} : Finset V).card<G.vertexConnectivity)
  exact traceable_of_near_spanning hc cap deletion hs hk ratio z least r hr

#print axioms traceable_of_near_in_structural_range
#print axioms traceable_of_near_spanning
end Graph189RootedSplice

