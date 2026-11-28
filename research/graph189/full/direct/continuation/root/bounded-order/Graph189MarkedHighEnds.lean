import Graph189FanCycle
import Graph189ParentFocused
import Graph189ConnectedMarkedRoute

open SimpleGraph Finset
namespace Graph189MarkedHighEnds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Keep the exceptional vertex in the side. Rotating a longest path gives
two high ends. At small orders the one-exception Hamilton cycle opens at any
mark. Otherwise the two-end pivot argument loses at most one vertex. -/
theorem marked_with_bonus (hc : G.Connected) (z : V) {d : ℕ} (low : 2≤G.degree z)
    (high : ∀v,v≠z → d≤G.degree v) (P : Finset V) (marks : P.Nonempty)
    (bonus : ℕ) (one : bonus≤1) (strong : ∀v,v≠z → v∉P → d+bonus≤G.degree v)
    (room : ∀a b : V,a≠z → b≠z → a∉P → b∉P → Fintype.card V<G.degree a+G.degree b+P.card) :
    ∃x∈P, ∃y, ∃r : G.Walk x y,r.IsPath ∧ Fintype.card V≤r.support.length+(min (Fintype.card V-2*d) (max 1 (Fintype.card V-(2*d+bonus)))) := by
  classical
  obtain ⟨u,um⟩ := marks
  by_cases small : Fintype.card V≤2*d
  · obtain ⟨a,C,hC⟩ := Graph189FanCycle.small_cycle z low hc.preconnected (fun v ne => by have := high v ne; omega)
    let Q := C.rotate u (hC.mem_support u)
    have hQ : Q.IsHamiltonianCycle := hC.rotate (hC.mem_support u)
    have len := Q.length_dropLast_add_one hQ.isCycle.not_nil
    have eq := hQ.length_eq
    exact ⟨u,um,_,Q.dropLast,hQ.isCycle.isPath_dropLast,by rw [Walk.length_support]; omega⟩
  obtain ⟨L,nd,chain,three,first,last,maximal⟩ := Graph189FanCycle.longest_high_ends z low
  have ne : L≠[] := by rintro rfl; simp at three
  let p := Walk.ofSupport L ne chain
  have ps : p.support=L := Walk.support_ofSupport ne chain
  have hp : p.IsPath := Walk.IsPath.mk' (by rwa [ps])
  have start := high (L.head ne) (fun eq => first ((List.head?_eq_some_head ne).trans (congrArg some eq)))
  have finish := high (L.getLast ne) (fun eq => last ((List.getLast?_eq_some_getLast ne).trans (congrArg some eq)))
  have longest {a b : V} (r : G.Walk a b) (hr : r.IsPath) : r.length≤p.length := by
    have cmp := maximal r.support hr.support_nodup r.isChain_adj_support
    have left := p.length_support
    rw [ps] at left
    have right := r.length_support
    omega
  let allowable := min (Fintype.card V-2*d) (max 1 (Fintype.card V-(2*d+bonus)))
  change ∃x∈P, ∃y, ∃r : G.Walk x y,r.IsPath ∧ Fintype.card V≤r.support.length+allowable
  have span (short : L.length<Fintype.card V) := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.lemma4 hc L ne nd chain maximal short (by omega)).2.2.1
  let loss := Fintype.card V-(2*d+1)
  have near : Fintype.card V≤p.support.length+loss := by
    rw [ps]
    dsimp [loss]
    by_cases all : L.length<Fintype.card V
    · have sum := span all
      omega
    omega
  have best : loss≤allowable := by dsimp [loss,allowable]; omega
  by_cases headMark : L.head ne∈P
  · exact ⟨_,headMark,_,p,hp,by omega⟩
  by_cases tailMark : L.getLast ne∈P
  · exact ⟨_,tailMark,_,p.reverse,hp.reverse,by simpa using (show Fintype.card V≤p.support.length+allowable by omega)⟩
  have near' : Fintype.card V≤p.support.length+(allowable-1) := by
    rw [ps]
    by_cases full : L.length<Fintype.card V
    · have sa := strong _ (fun eq => first ((List.head?_eq_some_head ne).trans (congrArg some eq))) headMark
      have sb := strong _ (fun eq => last ((List.getLast?_eq_some_getLast ne).trans (congrArg some eq))) tailMark
      have deg := span full
      dsimp [allowable]; omega
    omega
  have bound := Graph189MarkedRotation.from_longest_with p hp longest P near'  (room _ _
    (fun eq => first ((List.head?_eq_some_head ne).trans (congrArg some eq)))
    (fun eq => last ((List.getLast?_eq_some_getLast ne).trans (congrArg some eq))) headMark tailMark) (fun r hr close enough => by
      obtain ⟨v,t,ht,len⟩ := Graph189MarkedCycleEntry.enter hc u r hr close
      exact ⟨u,um,v,t,ht,by omega⟩)
  have cost : allowable-1+1=allowable := by dsimp [allowable]; omega
  rwa [cost] at bound

theorem marked_using_unmarked (hc : G.Connected) (z : V) {d : ℕ} (low : 2≤G.degree z)
    (high : ∀v,v≠z → d≤G.degree v) (P : Finset V) (marks : P.Nonempty)
    (room : ∀a b : V,a≠z → b≠z → a∉P → b∉P → Fintype.card V<G.degree a+G.degree b+P.card) :
    ∃x∈P, ∃y, ∃r : G.Walk x y,r.IsPath ∧ Fintype.card V≤r.support.length+(Fintype.card V-2*d) := by
  simpa only [Nat.add_zero,Nat.min_eq_left (le_max_right 1 _)] using
    marked_with_bonus hc z low high P marks 0 (by decide)
      (fun v ne _ => by simpa using high v ne) room

theorem marked (hc : G.Connected) (z : V) {d : ℕ} (low : 2≤G.degree z)
    (high : ∀v,v≠z → d≤G.degree v) (P : Finset V) (marks : P.Nonempty)
    (room : Fintype.card V<2*d+P.card) :
    ∃x∈P, ∃y, ∃r : G.Walk x y,r.IsPath ∧ Fintype.card V≤r.support.length+(Fintype.card V-2*d) := by
  apply marked_using_unmarked hc z low high P marks
  intro a b ha hb _ _
  have := high a ha
  have := high b hb
  omega

end Graph189MarkedHighEnds
#print axioms Graph189MarkedHighEnds.marked
#print axioms Graph189MarkedHighEnds.marked_using_unmarked
#print axioms Graph189MarkedHighEnds.marked_with_bonus
