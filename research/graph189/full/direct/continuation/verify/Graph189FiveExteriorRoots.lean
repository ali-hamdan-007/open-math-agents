import Graph189FourRoutes

open Finset SimpleGraph
namespace Graph189FiveExteriorRoots
variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Every initial edge in a graph of minimum degree three starts a four-vertex path. -/
theorem extend_edge (degrees : ∀ w, 3 ≤ H.degree w) {u a : W} (ua : H.Adj u a) :
    ∃ b c, H.Adj a b ∧ H.Adj b c ∧ u≠b ∧ u≠c ∧ a≠c := by
  classical
  obtain ⟨b,hb,bu⟩ := exists_mem_ne (show 1 < (H.neighborFinset a).card by
    rw [H.card_neighborFinset_eq_degree]; have := degrees a; omega) u
  have ab := (H.mem_neighborFinset _ _).mp hb
  obtain ⟨c,hc⟩ := exists_mem_notMem_of_card_lt_card (s:={u,a}) (t:=H.neighborFinset b) (by
    rw [card_pair ua.ne,H.card_neighborFinset_eq_degree]
    exact degrees b)
  exact ⟨b,c,ab,(H.mem_neighborFinset _ _).mp hc.1,bu.symm,fun e => hc.2 (by simp [e]),fun e => hc.2 (by simp [e])⟩

omit [DecidableEq W] in
theorem four_from (degrees : ∀ w, 3 ≤ H.degree w) (u : W) :
    ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 4 ≤ q.support.length := by
  classical
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (H.neighborFinset u).card by
    rw [H.card_neighborFinset_eq_degree]; have := degrees u; omega)
  have ua := (H.mem_neighborFinset _ _).mp ha
  obtain ⟨b,c,ab,bc,ub,uc,ac⟩ := extend_edge H degrees ua
  let q : H.Walk u c := .cons ua (.cons ab (.cons bc .nil))
  exact ⟨c,q,Walk.IsPath.mk' (by simp [q,ua.ne,ab.ne,bc.ne,ub,uc,ac]),by simp [q]⟩

private theorem last_neighbors (degrees : ∀ w, 3 ≤ H.degree w) {u a b c : W}
    (short : ¬ ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 5 ≤ q.support.length)
    (ua : H.Adj u a) (ab : H.Adj a b) (bc : H.Adj b c) (ub : u≠b) (uc : u≠c) (ac : a≠c) :
    H.neighborFinset c={u,a,b} := by
  classical
  apply eq_of_subset_of_card_le
  · intro w hw
    by_contra skip
    have cw := (H.mem_neighborFinset _ _).mp hw
    have wu : w≠u := fun e => skip (by simp [e])
    have wa : w≠a := fun e => skip (by simp [e])
    have wb : w≠b := fun e => skip (by simp [e])
    let q : H.Walk u w := .cons ua (.cons ab (.cons bc (.cons cw .nil)))
    exact short ⟨w,q,Walk.IsPath.mk' (by simp [q,ua.ne,ab.ne,bc.ne,cw.ne,ub,uc,ac,wu.symm,wa.symm,wb.symm]),by simp [q]⟩
  · simpa [ua.ne,ub,ab.ne] using degrees c

/-- If a root fails to start five vertices, every initial edge at the root
belongs to a tetrahedron whose three other vertices are saturated. -/
private theorem tetrahedron (degrees : ∀ w, 3 ≤ H.degree w) {u a : W}
    (short : ¬ ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 5 ≤ q.support.length) (ua : H.Adj u a) :
    ∃ b c, u≠b ∧ u≠c ∧ a≠b ∧ a≠c ∧ b≠c ∧ H.Adj u b ∧ H.Adj u c ∧
      H.neighborFinset a={u,b,c} ∧ H.neighborFinset b={u,a,c} ∧ H.neighborFinset c={u,a,b} := by
  classical
  obtain ⟨b,c,ab,bc,ub,uc,ac⟩ := extend_edge H degrees ua
  have Nc := last_neighbors H degrees short ua ab bc ub uc ac
  have ucE : H.Adj u c := ((H.mem_neighborFinset _ _).mp (by rw [Nc]; simp)).symm
  have acE : H.Adj a c := ((H.mem_neighborFinset _ _).mp (by rw [Nc]; simp)).symm
  have Nb := last_neighbors H degrees short ua acE bc.symm uc ub ab.ne
  have ubE : H.Adj u b := ((H.mem_neighborFinset _ _).mp (by rw [Nb]; simp)).symm
  have Na := last_neighbors H degrees short ubE bc acE.symm uc ua.ne ab.ne.symm
  exact ⟨b,c,ub,uc,ab.ne,ac,bc.ne,ubE,ucE,Na,Nb,Nc⟩

/-- A root failing the five-vertex condition is universal, all other
vertices have degree three, and a non-tetrahedral component then has at
least seven vertices. -/
theorem deficient (connected : H.Connected) (degrees : ∀ w, 3 ≤ H.degree w) (u : W)
    (short : ¬ ∃ v, ∃ q : H.Walk u v, q.IsPath ∧ 5 ≤ q.support.length) :
    (∀ v, v≠u → H.Adj u v ∧ H.degree v=3) ∧ (Fintype.card W=4 ∨ 7 ≤ Fintype.card W) := by
  classical
  let T := insert u (H.neighborFinset u)
  have closed (v : W) (hv : v∈T) (w : W) (edge : H.Adj v w) : w∈T := by
    rcases mem_insert.mp hv with rfl|near
    · exact mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr edge)
    have uv := (H.mem_neighborFinset _ _).mp near
    obtain ⟨b,c,_,_,_,_,_,ub,uc,Nv,_,_⟩ := tetrahedron H degrees short uv
    have hit := (H.mem_neighborFinset _ _).mpr edge
    rw [Nv] at hit
    simp only [mem_insert,mem_singleton] at hit
    rcases hit with rfl|rfl|rfl
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr ub)
    · exact mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr uc)
  have universal (v : W) (vu : v≠u) : H.Adj u v := by
    have inside : v∈T := by
      by_contra missing
      obtain ⟨w⟩ := connected u v
      obtain ⟨e,_,ein,eout⟩ := w.exists_boundary_dart (T : Set W) (mem_insert_self _ _) missing
      exact eout (closed _ ein _ e.adj)
    exact (H.mem_neighborFinset _ _).mp ((mem_insert.mp inside).resolve_left vu)
  have deg (v : W) (vu : v≠u) : H.degree v=3 := by
    have edge := universal v vu
    obtain ⟨b,c,ub,uc,_,_,bc,_,_,Nv,_,_⟩ := tetrahedron H degrees short edge
    rw [←H.card_neighborFinset_eq_degree,Nv]
    simp [ub,uc,bc]
  refine ⟨fun v h => ⟨universal v h,deg v h⟩,?_⟩
  by_cases four : Fintype.card W=4
  · exact Or.inl four
  apply Or.inr
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (H.neighborFinset u).card by
    rw [H.card_neighborFinset_eq_degree]; have := degrees u; omega)
  have ua := (H.mem_neighborFinset _ _).mp ha
  obtain ⟨b,c,ub,uc,ab,ac,bc,_,_,Na,Nb,Nc⟩ := tetrahedron H degrees short ua
  let B : Finset W := {u,a,b,c}
  have size : B.card=4 := by simp [B,ua.ne,ub,uc,ab,ac,bc]
  have lb := B.card_le_univ
  obtain ⟨x,hx⟩ := exists_mem_notMem_of_card_lt_card (s:=B) (t:=univ) (by rw [card_univ]; omega)
  have bound (t : W) (Hxt : H.Adj x t) (ht : t∈B) : t=u := by
    have no : x≠u ∧ x≠a ∧ x≠b ∧ x≠c := by simpa [B] using hx.2
    have hit := (H.mem_neighborFinset _ _).mpr Hxt.symm
    simp only [B,mem_insert,mem_singleton] at ht
    rcases ht with rfl|rfl|rfl|rfl
    · rfl
    all_goals simp_all
  have inc : insert x (H.neighborFinset x \ {u}) ⊆ Bᶜ := by
    intro t ht
    apply mem_compl.mpr
    rcases mem_insert.mp ht with rfl|inN
    · exact hx.2
    · intro tB
      obtain ⟨ed,tu⟩ := mem_sdiff.mp inN
      exact tu (mem_singleton.mpr (bound t ((H.mem_neighborFinset _ _).mp ed) tB))
  have cBound := card_le_card inc
  rw [card_insert_of_notMem (by simp),card_compl,size] at cBound
  have rem := card_sdiff_add_card_inter (H.neighborFinset x) ({u} : Finset W)
  have cap := card_le_card (inter_subset_right (s₁:=H.neighborFinset x) (s₂:={u}))
  rw [card_singleton] at cap
  rw [H.card_neighborFinset_eq_degree] at rem
  have := degrees x
  omega

#print axioms deficient
end Graph189FiveExteriorRoots
