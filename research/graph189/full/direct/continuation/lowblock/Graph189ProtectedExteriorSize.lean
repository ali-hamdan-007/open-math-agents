import Graph189ProtectedIntervals
import Graph189VertexMatching

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}

/-- The number omitted by a longest path through z is no larger than
any interval that can be replaced by z on a path covering G−z. -/
private theorem singleton_gap (p : G.Walk x y) (hp : p.IsPath) {z : V}
    (outside : z ∉ p.support) {m : ℕ}
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length+m ≤ p.support.length+1)
    (A J B : List V) (split : p.support=A++J++B)
    (left : ∀ v∈A.getLast?, G.Adj v z) (right : ∀ v∈B.head?, G.Adj z v) :
    m ≤ J.length := by
  let q : G.Walk z z := Walk.nil
  have dis : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  obtain ⟨a,b,r,hr,rs⟩ := splice_support p hp A J B split q (by simp [q]) dis left right
  have count := maximal r hr (by simp [rs,q])
  rw [rs,split] at count
  simp only [q,Walk.support_nil,List.length_append,List.length_singleton] at count
  omega

/-- An exterior detour ending at the first specified mark replaces the preceding prefix. -/
private theorem first_tail (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i : Fin p.support.length)
    (contact : G.Adj z p.support[i.val]) : m ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := singleton_gap p hp outside maximal [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega

/-- An exterior detour starting at the last specified mark replaces the following suffix. -/
private theorem last_tail (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i : Fin p.support.length)
    (contact : G.Adj p.support[i.val] z) : i.val + 1 + m ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := singleton_gap p hp outside maximal (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega

/-- Every pair of distinct marked positions bounds a gap able to absorb a disjoint detour. -/
private theorem inner_gap (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i j : Fin p.support.length) (hij : i<j)
    (left : G.Adj p.support[i.val] z) (right : G.Adj z p.support[j.val]) :
    i.val+1+m ≤ j.val := by
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
  have bound := singleton_gap p hp outside maximal _ _ _ split (by
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

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- The neighbor positions of z on a path covering its deletion give
one more disjoint gap than there are neighbors. Each gap bounds the
size of the omitted set of a longest path through z. -/
theorem protected_exterior_size_upper (p : G.Walk x y) (hp : p.IsPath) {z : V}
    (outside : z ∉ p.support) (all : ∀ v, v ≠ z → v ∈ p.support)
    (pos : 0 < G.degree z) {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length) :
    1+G.degree z+(G.degree z+1)*(Q.support.toFinsetᶜ : Finset V).card ≤ Fintype.card V := by
  classical
  let m := (Q.support.toFinsetᶜ : Finset V).card
  have size : p.support.length+1=Fintype.card V := by
    have h : insert z p.support.toFinset=univ := by
      ext v
      by_cases e : v=z
      · simp [e]
      · simp [all v e]
    have eq := congrArg Finset.card h
    rwa [card_insert_of_notMem (by simpa using outside),
      List.toFinset_card_of_nodup hp.support_nodup,card_univ] at eq
  have mx {u v} (r : G.Walk u v) (hr : r.IsPath) (contains : z∈r.support) :
      r.support.length + m ≤ p.support.length+1 := by
    have bound := maximal r hr contains
    have total := card_add_card_compl Q.support.toFinset
    rw [List.toFinset_card_of_nodup hQ.support_nodup] at total
    change Q.support.length+m=Fintype.card V at total
    have := Q.length_support
    have := r.length_support
    omega
  let N := G.neighborFinset z
  have onPath (v : V) (hv : v∈N) : v∈p.support :=
    all v ((G.mem_neighborFinset _ _).mp hv).ne.symm
  obtain ⟨marks,e,values⟩ := vertex_positions_equiv p N onPath
  have card : marks.card = G.degree z := by
    have eq : marks.card = N.card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr e
    exact eq.trans (G.card_neighborFinset_eq_degree z)
  let j := marks.card-1
  have hj : marks.card = j+1 := by dsimp [j]; omega
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  have adj (i : Fin (j+1)) : G.Adj z p.support[(M i).val] := by
    change G.Adj z p.support[(iso i).val.val]
    rw [values (iso i)]
    exact (G.mem_neighborFinset _ _).mp (e (iso i)).property
  have fst := first_tail p hp outside mx (M 0) (adj _)
  have lst := last_tail p hp outside mx (M (Fin.last j)) (adj _).symm
  have spread (i : Fin j) : (M i.castSucc).val+1+m ≤ (M i.succ).val :=
    inner_gap p hp outside mx (M i.castSucc) (M i.succ) (M.strictMono i.castSucc_lt_succ)
      (adj _).symm (adj _)
  have lower (i : Fin (j+1)) : (i.val+1)*m+i.val ≤ (M i).val := by
    induction i using Fin.induction with
    | zero => simpa using fst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_castSucc,Fin.val_succ,Nat.succ_mul] at ih step ⊢
      omega
  have final := lower (Fin.last j)
  simp only [Fin.val_last] at final
  change 1+G.degree z+(G.degree z+1)*m ≤ _
  rw [←card,hj]
  rw [Nat.succ_mul]
  omega

omit [DecidableRel G.Adj] [DecidableEq V] in
/-- There is a longest path among all paths containing z, with an actual
path position realizing the protected vertex. -/
theorem exists_longest_through (G : SimpleGraph V) (z : V) :
    ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ ∃ t : Fin Q.support.length,
      Q.support[t.val] = z ∧
        ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length := by
  classical
  let Good (n : ℕ) := ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ z ∈ Q.support ∧ Q.length=n
  have base : Good 0 := ⟨z,z,.nil,by simp,by simp,rfl⟩
  obtain ⟨a,b,Q,hQ,mem,sz⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  refine ⟨a,b,Q,hQ,⟨i,hi⟩,eq,?_⟩
  intro u v r hr member
  rw [sz]
  have len := r.length_support
  have bound := hr.support_nodup.length_le_card
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,member,rfl⟩)

/-- The upper size bound stated directly for a Hamilton path in G−z. -/
theorem protected_size_of_traceable_deletion (z : V) (pos : 0 < G.degree z)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length) :
    1+G.degree z+(G.degree z+1)*(Q.support.toFinsetᶜ : Finset V).card ≤ Fintype.card V := by
  let e := Embedding.induce (G:=G) {v : V | v ≠ z}
  apply protected_exterior_size_upper (p.map e.toHom) (hp.isPath.map e.injective) _ _ pos Q hQ maximal
  · rw [Walk.support_map]
    intro h
    obtain ⟨v,_,eq⟩ := List.mem_map.mp h
    exact v.property eq
  · intro v ne
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨v,ne⟩,hp.mem_support _,rfl⟩

/-- If the claimed base order fails, the entire protected-path exterior
contains at most k−s vertices. -/
theorem protected_size_under_base_failure (z : V) (pos : 0 < G.degree z)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length)
    {s k : ℕ} (sk : s ≤ k) (sd : s ≤ G.degree z)
    (failure : Fintype.card V+1 < (s+1)*(k-s+2)) :
    (Q.support.toFinsetᶜ : Finset V).card+s ≤ k := by
  let m := (Q.support.toFinsetᶜ : Finset V).card
  have lower := protected_size_of_traceable_deletion z pos p hp Q hQ maximal
  change 1+G.degree z+(G.degree z+1)*m ≤ _ at lower
  change m+s ≤ k
  by_contra! small
  have cmp := Nat.mul_le_mul (Nat.add_le_add_right sd 1)
    (show k-s+2 ≤ m+1 by omega)
  rw [show (G.degree z+1)*(m+1) = (G.degree z+1)*m+(G.degree z+1) from Nat.mul_succ _ _] at cmp
  omega

end Graph189ExteriorGap

#print axioms Graph189ExteriorGap.protected_exterior_size_upper
#print axioms Graph189ExteriorGap.exists_longest_through
#print axioms Graph189ExteriorGap.protected_size_of_traceable_deletion

#print axioms Graph189ExteriorGap.protected_size_under_base_failure
