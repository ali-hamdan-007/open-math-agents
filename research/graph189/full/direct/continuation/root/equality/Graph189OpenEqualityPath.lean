import Graph189BondyEqualityCensus

open SimpleGraph Finset Graph189UniversalCycle OMA.BondyK
namespace Graph189BondyEquality
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At a vertex of the stipulated minimum ambient degree, equality of its
completion degree makes every incident completion edge genuine. -/
theorem genuine_edges (w v : V) {d : ℕ} (lower : d≤G.degree v)
    (tight : (completeAt G w).degree v=d) :
    ∀ x : V, (completeAt G w).Adj v x → G.Adj v x := by
  classical
  let K := completeAt G w
  have inc : G.neighborFinset v⊆K.neighborFinset v := by
    intro a ha
    exact (K.mem_neighborFinset _ _).mpr (Or.inl ((G.mem_neighborFinset _ _).mp ha))
  have eq := eq_of_subset_of_card_le inc (by
    rw [G.card_neighborFinset_eq_degree,K.card_neighborFinset_eq_degree]
    exact tight.le.trans lower)
  intro x adj
  apply (G.mem_neighborFinset _ _).mp
  rw [eq]
  exact (K.mem_neighborFinset _ _).mpr adj

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem chain_of_all_edges {X : List V} (nd : X.Nodup)
    (all : ∀ x∈X, ∀ y∈X, x≠y → G.Adj x y) : X.IsChain G.Adj := by
  induction X with
  | nil => simp
  | cons x X ih =>
    cases X with
    | nil => simp
    | cons y Y =>
      have n := List.nodup_cons.mp nd
      apply List.IsChain.cons_cons
      · exact all x (by simp) y (by simp) (fun eq => n.1 (by simp [eq]))
      · exact ih n.2 (fun a ha b hb => all a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem original_chain {c : ℕ} {f : ℕ→V} (t : ℕ)
    (edges : ∀ (i : ℕ) (_ : t ≤ i) (_ : i + 1 < t + c), G.Adj (f i) (f (i + 1))) :
    (up f t c).IsChain G.Adj := by
  have build (b n : ℕ) (lo : t≤b) (hi : b+n≤t+c) : (up f b n).IsChain G.Adj := by
    induction n generalizing b with
    | zero => simp [up]
    | succ n ih =>
      cases n with
      | zero => simp [up]
      | succ n =>
        have tail := ih (b+1) (by omega) (by omega)
        simp only [up,List.range'_succ,List.map_cons] at tail ⊢
        exact List.IsChain.cons_cons (edges b lo (by omega)) tail
  exact build t c le_rfl le_rfl

/-- Opening a saturated longest completion cycle at its universal anchor,
after the cyclic gap comparison has established the census. -/
theorem traceable_of_equality_census [Nontrivial V]
    (w : V) {c k d : ℕ} {f : ℕ→V} {H : Finset V} {s : ℕ→ℕ}
    (cycle : Cy (completeAt G w) c f) (data : Layout (completeAt G w) c k d f H s)
    (offDegree : ∀ v : V, v≠w → d≤G.degree v) (kd : k≤d)
    (room : d+2≤Fintype.card V) (census : c+H.card=Fintype.card V) :
    ∃ x y, ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  let K := completeAt G w
  let A := (range k).image (fun i => f (s i))
  have sc : A.card=k := data.anchor_count
  have size := data.size
  have dis : Disjoint H A := by
    apply Finset.disjoint_left.mpr
    intro v hv av
    obtain ⟨i,_,eq⟩ := mem_image.mp av
    exact data.outside v hv (s i) eq
  have exact_degree (v : V) (hv : v∈H) : K.degree v=d := by
    have neighbors := data.neighbors v hv
    change K.neighborFinset v=H.erase v ∪A at neighbors
    rw [←K.card_neighborFinset_eq_degree,neighbors,card_union_of_disjoint (dis.mono_left (erase_subset _ _)),
      card_erase_of_mem hv,sc]
    have positive := card_pos.mpr ⟨v,hv⟩
    omega
  have outside : w∉H := by
    intro inH
    have dw := exact_degree w inH
    change (completeAt G w).degree w=d at dw
    rw [completeAt_degree_self] at dw
    omega
  have real (v : V) (h : v∈H) := genuine_edges w v (offDegree v (fun eq => outside (eq ▸ h)))
    (exact_degree v h)
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<H.card by omega)
  have wa : w∈A := by
    have vw : K.Adj v w := Or.inr ⟨Or.inr rfl,fun eq => outside (eq ▸ hv)⟩
    have n := (K.mem_neighborFinset _ _).mpr vw
    rw [data.neighbors v hv] at n
    exact (mem_union.mp n).resolve_left (fun h => outside (mem_erase.mp h).2)
  obtain ⟨j,hj,head⟩ := mem_image.mp wa
  have jlt := mem_range.mp hj
  let t := s j
  have first : f t=w := head
  have cc := cycle.three
  have next : f (t+1)≠w := by
    rw [← first]
    exact cycle.ne_of_window (b:=t) (by omega) (by omega) (by omega) (by omega) (by omega)
  have firstEdge : G.Adj (f t) (f (t+1)) :=
    (genuine_edges w (f (t+1)) (offDegree _ next) (data.successors j jlt) _ (cycle.adj t).symm).symm
  have chain := original_chain (G:=G) (f:=f) (c:=c) t (by
    intro i lo hi
    by_cases eq : i=t
    · simpa [eq] using firstEdge
    rcases cycle.adj i with adj|⟨on,_⟩
    · exact adj
    rcases on with h|h
    · exact (cycle.ne_of_window (b:=t) lo (by omega) (by omega) (by omega) eq (h.trans first.symm)).elim
    · exact (cycle.ne_of_window (b:=t) (by omega) hi (by omega) (by omega) (by omega) (h.trans first.symm)).elim)
  let T := up f t c
  let F := H.toList
  have fx : F.Nodup := H.nodup_toList
  have tx : T.Nodup := nodup_up cycle le_rfl
  have mark : T.head?=some w := by
    obtain ⟨b,eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c≠0)
    simp only [T,eq,up_head,first]
  have inF (x : V) : x∈F ↔ x∈H := mem_toList
  have disjoint : List.Disjoint F T := by
    rw [List.disjoint_left]
    intro x xf xt
    obtain ⟨i,_,_,hi⟩ := mem_up.mp xt
    exact data.outside x ((inF _).mp xf) i hi
  have combo : (F++T).IsChain G.Adj := by
    apply List.isChain_append.mpr
    refine ⟨chain_of_all_edges fx ?_,chain,?_⟩
    · intro x hx y hy ne
      have h := (inF _).mp hx
      apply real x h
      apply (K.mem_neighborFinset _ _).mp
      rw [data.neighbors x h]
      exact mem_union_left _ (mem_erase.mpr ⟨ne.symm,(inF _).mp hy⟩)
    · intro x hx y hy
      have h : x∈H := (inF _).mp (List.mem_of_getLast? hx)
      have wy : w=y := by simpa [mark] using hy
      subst y
      apply real x h
      exact Or.inr ⟨Or.inr rfl,fun eq => outside (eq ▸ h)⟩
  have nd : (F++T).Nodup := List.nodup_append.mpr ⟨fx,tx,by rintro a ha b hb rfl; exact List.disjoint_left.mp disjoint ha hb⟩
  have len : (F++T).length=Fintype.card V := by simpa [F,T,up,Nat.add_comm] using census
  generalize e : F++T=L at combo nd len
  cases L with
  | nil =>
    simp only [List.length_nil] at len
    have pos : 0<Fintype.card V := Fintype.card_pos
    omega
  | cons u l =>
    obtain ⟨y,p,supp,_⟩ := walk_of_chain l u combo
    have hp : p.IsPath := Walk.IsPath.mk' (by rw [supp];exact nd)
    have span : p.support.toFinset=univ := eq_of_subset_of_card_le (subset_univ _) (by
      rw [card_univ,supp,List.toFinset_card_of_nodup nd]; exact len.ge)
    refine ⟨u,y,p,hp.isHamiltonian_of_mem ?_⟩
    intro x
    apply List.mem_toFinset.mp
    rw [span]
    exact mem_univ _

#print axioms traceable_of_equality_census
end Graph189BondyEquality
