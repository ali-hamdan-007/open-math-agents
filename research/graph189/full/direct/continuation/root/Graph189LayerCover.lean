import Graph189SeparatorCover
import Mathlib.Data.Finset.Powerset
open SimpleGraph Finset
namespace Graph189LayerCover
variable {V : Type*} [Fintype V]
noncomputable def layer (G : SimpleGraph V) (z : V) (n : ℕ) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist z v = n)
@[simp] theorem in_layer {G : SimpleGraph V} {z y : V} {n : ℕ} :
    y ∈ layer G z n ↔ G.dist z y = n := by classical simp [layer]
-- The private-cover and two-edge witnesses adapt the research fork's Graph189ThirdLayer.
private theorem minimal_cover (A B : Finset V) (R : V → V → Prop)
    (hc : ∀ b ∈ B, ∃ a ∈ A, R a b) :
    ∃ T ⊆ A, (∀ b ∈ B, ∃ a ∈ T, R a b) ∧
      ∀ a ∈ T, ∃ b ∈ B, R a b ∧ ∀ a' ∈ T, a' ≠ a → ¬ R a' b := by
  classical
  let covers (S : Finset V) := ∀ b ∈ B, ∃ a ∈ S, R a b
  let family := A.powerset.filter covers
  have ha : A ∈ family := mem_filter.mpr ⟨mem_powerset.mpr (fun _ h => h), hc⟩
  obtain ⟨T,hT,hmin⟩ := family.exists_min_image Finset.card ⟨A,ha⟩
  obtain ⟨hsub,hcovers⟩ := mem_filter.mp hT
  have hsub' := mem_powerset.mp hsub
  refine ⟨T,hsub',hcovers,?_⟩
  intro a haT
  have missing : ¬ covers (T.erase a) := by
    intro h
    have hs : T.erase a ∈ family := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset a T).trans hsub'),h⟩
    exact (not_le_of_gt (card_erase_lt_of_mem haT)) (hmin _ hs)
  change ¬ (∀ b ∈ B, ∃ a' ∈ T.erase a, R a' b) at missing
  push Not at missing
  obtain ⟨b,hb,hprivate⟩ := missing
  obtain ⟨x,hx,hxb⟩ := hcovers b hb
  have hxa : x = a := by
    by_contra h
    exact hprivate x (mem_erase.mpr ⟨h,hx⟩) hxb
  exact ⟨b,hb,hxa ▸ hxb,fun a' ha' hdiff => hprivate a' (mem_erase.mpr ⟨hdiff,ha'⟩)⟩

omit [Fintype V] in
private theorem predecessor {G : SimpleGraph V} {z y : V} {d : ℕ}
    (h : G.dist z y = d+1) : ∃ p, G.dist z p = d ∧ G.Adj p y := by
  have hr : G.dist y z = d+1 := by rwa [dist_comm]
  have hpos : G.Reachable y z := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hpos.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at h
  | cons hy tail =>
    rename_i p
    have hlen' : tail.length = d := by rw [Walk.length_cons,hr] at hlen; omega
    have hle : G.dist z p ≤ d := by rw [dist_comm]; exact hlen' ▸ G.dist_le tail
    have ht := hy.diff_dist_adj (u := z)
    exact ⟨p,by omega,hy.symm⟩

omit [Fintype V] in
private theorem dist_two {G : SimpleGraph V} {x y q : V}
    (hne : x ≠ y) (hna : ¬G.Adj x y) (h1 : G.Adj x q) (h2 : G.Adj q y) :
    G.dist x y = 2 := by
  let w : G.Walk x y := .cons h1 (.cons h2 .nil)
  have hlo := w.reachable.one_lt_dist_of_ne_of_not_adj hne hna
  have hhi : G.dist x y ≤ 2 := G.dist_le w
  omega


omit [Fintype V] in
private theorem second_step {G : SimpleGraph V} (hc : G.Connected) (z y : V)
    (h : 2 ≤ G.dist z y) : ∃ b, G.dist z b = 2 ∧ G.dist z y = 2 + G.dist b y := by
  generalize hd : G.dist z y = d at h ⊢
  induction d using Nat.strong_induction_on generalizing y with
  | h d ih =>
    by_cases e : d=2
    · exact ⟨y,hd.trans e,by simp [e]⟩
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
      obtain ⟨p,hp,hpy⟩ := predecessor hd
      obtain ⟨b,hb,split⟩ := ih m (by omega) p hp (by omega)
      have up := hc.dist_triangle (u:=b) (v:=p) (w:=y)
      rw [dist_eq_one_iff_adj.mpr hpy] at up
      have low := hc.dist_triangle (u:=z) (v:=b) (w:=y)
      exact ⟨b,hb,by omega⟩

/-- An arbitrary supplied cover of the distance-two layer gives a root-specific
order estimate. The root can have any eccentricity. -/
theorem order_of_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ layer G z 2, ∃ a ∈ R, G.Adj a b) :
    ∃ t ≤ R.card, t ≤ k+1 ∧ Fintype.card V ≤ 1+G.degree z+k+t*(k+1-t) := by
  classical
  obtain ⟨T,hTR,hTc,hTp⟩ := minimal_cover R (layer G z 2) G.Adj covers
  let port (a : V) : V := if h : a ∈ T then (hTp a h).choose else z
  have hp (a : V) (h : a ∈ T) : G.dist z (port a) = 2 ∧ G.Adj a (port a) ∧
      ∀ a' ∈ T, a' ≠ a → ¬ G.Adj a' (port a) := by
    simpa [port,h] using (hTp a h).choose_spec
  have hA (a : V) (h : a ∈ T) : G.dist z a = 1 := dist_eq_one_iff_adj.mpr (arms a (hTR h))
  let evenSet (a : V) := (univ.filter (fun v => Even (G.dist a v))).erase a
  have quota (a : V) : (evenSet a).card ≤ k := by
    have self : a ∈ univ.filter (fun v => Even (G.dist a v)) := by simp
    have bound := cap a
    change (univ.filter (fun v => Even (G.dist a v))).card ≤ k+1 at bound
    unfold evenSet
    rw [card_erase_of_mem self]
    omega
  have evenMem {a v : V} (n : a ≠ v) (ev : Even (G.dist a v)) : v ∈ evenSet a :=
    mem_erase.mpr ⟨Ne.symm n, mem_filter.mpr ⟨mem_univ _,ev⟩⟩
  let F := univ.filter (fun v => 3 ≤ G.dist z v ∧ ¬ Even (G.dist z v))
  let W (a : V) := F.filter (fun c => c ∈ evenSet a)
  have cov : F ⊆ T.biUnion W := by
    intro c hcF
    obtain ⟨far,odd⟩ := (mem_filter.mp hcF).2
    obtain ⟨b,hb,hsplit⟩ := second_step hc z c (by omega)
    obtain ⟨a,ha,hab⟩ := hTc b (in_layer.mpr hb)
    have upper := hc.dist_triangle (u:=a) (v:=b) (w:=c)
    rw [dist_eq_one_iff_adj.mpr hab] at upper
    have lower := hc.dist_triangle (u:=z) (v:=a) (w:=c)
    have unit := hA a ha
    have distinct : a ≠ c := by rintro rfl; omega
    have even : Even (G.dist a c) := by rw [Nat.even_iff] at odd ⊢; omega
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hcF,evenMem distinct even⟩⟩
  have row (a : V) (ha : a ∈ T) : (W a).card + T.card ≤ k+1 := by
    let f (j : V) := if G.Adj a j then port j else j
    have hzj (j : V) (hj : j ∈ T) : G.dist z (f j) ≤ 2 := by
      by_cases h : G.Adj a j <;> simp [f,h,(hp j hj).1,hA j hj]
    have finj : Set.InjOn f ↑(T.erase a) := by
      intro j hj l hl hEq
      obtain ⟨_,hjT⟩ := mem_erase.mp hj
      obtain ⟨_,hlT⟩ := mem_erase.mp hl
      by_cases hjA : G.Adj a j <;> by_cases hlA : G.Adj a l <;> simp [f,hjA,hlA] at hEq
      · by_contra hne
        exact (hp l hlT).2.2 j hjT hne (hEq ▸ (hp j hjT).2.1)
      · have h1 := (hp j hjT).1; have h2 := hA l hlT; rw [hEq] at h1; omega
      · have h1 := (hp l hlT).1; have h2 := hA j hjT; rw [hEq] at h2; omega
      · exact hEq
    let E := (T.erase a).image f
    have heq : E.card = (T.erase a).card := card_image_of_injOn finj
    have hdis : Disjoint (W a) E := by
      apply Finset.disjoint_left.mpr
      intro x hx hw
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
      have h1 := (mem_filter.mp (mem_filter.mp hx).1).2.1
      have h2 := hzj j (mem_erase.mp hj).2
      omega
    have incl : W a ∪ E ⊆ evenSet a := by
      intro x hx
      rcases mem_union.mp hx with hw|he
      · exact (mem_filter.mp hw).2
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp he
        obtain ⟨hne,hj⟩ := mem_erase.mp hj
        suffices hd : G.dist a (f j) = 2 by
          apply evenMem _ (by simp [hd])
          intro eq
          rw [← eq, dist_self] at hd
          omega
        by_cases haj : G.Adj a j
        · simp only [f,if_pos haj]
          have hza := hA a ha
          have hzj' := (hp j hj).1
          apply dist_two _ ((hp j hj).2.2 a ha hne.symm) haj (hp j hj).2.1
          rintro heq'; rw [heq'] at hza; omega
        · simp only [f,if_neg haj]
          exact dist_two hne.symm haj (dist_eq_one_iff_adj.mp (hA a ha)).symm
            (dist_eq_one_iff_adj.mp (hA j hj))
    have hcount := (card_le_card incl).trans (quota a)
    rw [card_union_of_disjoint hdis,heq] at hcount
    have he := card_erase_add_one ha
    omega
  have hsize : T.card ≤ k+1 := by
    rcases T.eq_empty_or_nonempty with he|⟨a,ha⟩
    · simp [he]
    · have := row a ha; omega
  have farCount : F.card ≤ T.card*(k+1-T.card) := by
    calc F.card ≤ (T.biUnion W).card := card_le_card cov
         _ ≤ ∑ a ∈ T, (W a).card := card_biUnion_le
         _ ≤ ∑ _ ∈ T, (k+1-T.card) := sum_le_sum (fun a ha => by have := row a ha; omega)
         _ = T.card*(k+1-T.card) := by simp
  have all : (univ : Finset V) ⊆ (({z} ∪ G.neighborFinset z) ∪ evenSet z) ∪ F := by
    intro v hv
    by_cases same : v = z
    · subst v; simp
    by_cases adj : G.Adj z v
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ ((G.mem_neighborFinset z v).mpr adj)))
    by_cases e : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_right _ (evenMem (Ne.symm same) e))
    have pos := (hc z v).one_lt_dist_of_ne_of_not_adj (Ne.symm same) adj
    exact mem_union_right _ (mem_filter.mpr ⟨hv,by rw [Nat.even_iff] at e; omega, e⟩)
  have one := card_union_le ({z} : Finset V) (G.neighborFinset z)
  have two := card_union_le ({z} ∪ G.neighborFinset z) (evenSet z)
  have three := card_union_le (({z} ∪ G.neighborFinset z) ∪ evenSet z) F
  have hcard := card_le_card all
  rw [card_univ] at hcard
  simp only [card_singleton,G.card_neighborFinset_eq_degree] at one
  exact ⟨T.card,card_le_card hTR,hsize,by have h := quota z; omega⟩
#print axioms order_of_cover
end Graph189LayerCover

