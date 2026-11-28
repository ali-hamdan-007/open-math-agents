import Graph189MinimumCutOrder
import Graph189LayerCutoff
import Graph189CutPopulationOrder

namespace Graph189GraphPopulation
open SimpleGraph Finset Graph189CutSides
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem minimum_sides (room : G.vertexConnectivity < Fintype.card V-1) :
    ∃ A B S : Finset V, S.card=G.vertexConnectivity ∧ CutSides G A B S := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card=j ∧
    (¬(G.induce ((S : Set V)ᶜ)).Connected ∨ S.card=Fintype.card V-1)}
  have hn := Fintype.one_lt_card (α:=V)
  have eq : G.vertexConnectivity=sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬ Fintype.card V≤1)]
  let v : V := Classical.arbitrary V
  have hcard : (univ.erase v).card=Fintype.card V-1 := by rw [card_erase_of_mem (mem_univ v),card_univ]
  have inhabited : M.Nonempty := ⟨_,univ.erase v,hcard,Or.inr hcard⟩
  have chosen : G.vertexConnectivity∈M := by rw [eq]; exact Nat.sInf_mem inhabited
  obtain ⟨S,sz,bad|he⟩ := chosen
  · have survives : ∃ u, u ∉ S := by
      by_contra! h
      have all := Finset.eq_univ_iff_forall.mpr h
      rw [all,card_univ] at sz
      omega
    obtain ⟨A,B,sides⟩ := exists_cutSides_of_disconnected S survives bad
    exact ⟨A,B,S,sz,sides⟩
  · omega

private theorem ordered_side {A B S : Finset V} (sides : CutSides G A B S) (hc : G.Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (smallDeletion : ∀ T : Finset V, T.card<S.card → (G.induce {u : V | u∉T}).Connected)
    (highDeg : ∀ v, S.card<G.degree v) (hs : 2≤S.card) (hsk : S.card≤G.secondSmallestDegree)
    (orientation : (A.filter (fun v => G.secondSmallestDegree≤G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree≤G.degree v)).card) :
    let k : ℤ := G.secondSmallestDegree
    let s : ℤ := S.card
    ((Fintype.card V : ℤ)-2*k-1)*(k-s)≤s*k*k := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k≤G.degree v)
  let Y := B.filter (fun v => k≤G.degree v)
  let L := univ.filter (fun v => G.degree v<k)
  have few : L.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    obtain h|h := degree_pair (G:=G) u v ne
    · exact (not_lt_of_ge h) (mem_filter.mp hu).2
    · exact (not_lt_of_ge h) (mem_filter.mp hv).2
  have cover : univ ⊆ ((S∪X)∪Y)∪L := by
    intro v _
    by_cases h : k≤G.degree v
    · rcases sides.cover v with ha|hb|hs'
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨ha,h⟩)))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hb,h⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hs'))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,Nat.lt_of_not_ge h⟩)
  have cnt := card_le_card cover
  rw [card_univ] at cnt
  have h₁ := card_union_le S X
  have h₂ := card_union_le (S∪X) Y
  have h₃ := card_union_le ((S∪X)∪Y) L
  have total : Fintype.card V≤X.card+Y.card+S.card+1 := by omega
  obtain ⟨a,ha,hka⟩ : ∃ a∈A, k≤G.degree a := by
    obtain ⟨a,ha⟩ := sides.left_nonempty
    by_cases h : k≤G.degree a
    · exact ⟨a,ha,h⟩
    have nb : ∃ b∈G.neighborFinset a, b∉S := by
      by_contra! hnb
      have hh := card_le_card (show G.neighborFinset a ⊆ S from fun v hv => hnb v hv)
      rw [G.card_neighborFinset_eq_degree] at hh
      exact (not_le_of_gt (highDeg a)) hh
    obtain ⟨b,hb,hsb⟩ := nb
    have adj := (G.mem_neighborFinset a b).mp hb
    rcases sides.cover b with hA|hB|hS
    · exact ⟨b,hA,(degree_pair (G:=G) a b adj.ne).resolve_left h⟩
    · exact (sides.no_cross a ha b hB adj).elim
    · exact (hsb hS).elim
  have dis : Disjoint (G.neighborFinset a) Y := by
    apply Finset.disjoint_left.mpr
    intro b hab hb
    exact sides.no_cross a ha b (mem_filter.mp hb).1 ((G.mem_neighborFinset a b).mp hab)
  have haY : a∉Y := fun h => Finset.disjoint_left.mp sides.apart ha (mem_filter.mp h).1
  have no : a∉ G.neighborFinset a∪Y := by simp [haY]
  have row := card_le_card (subset_univ (insert a (G.neighborFinset a∪Y)))
  rw [card_insert_of_notMem no,card_union_of_disjoint dis,G.card_neighborFinset_eq_degree,card_univ] at row
  have lower : k≤X.card+S.card := by omega
  have prod := sides.high_product hc smallDeletion cap
  change X.card*Y.card≤X.card*k+S.card*(k*k) at prod
  change X.card≤Y.card at orientation
  have q := Graph189CutPopulationOrder.population_order
    (s:=(S.card:ℚ)) (k:=(k:ℚ)) (n:=(Fintype.card V:ℚ)) (x:=(X.card:ℚ)) (y:=(Y.card:ℚ))
    (by exact_mod_cast hs) (by exact_mod_cast hsk)
    (by
      have hh : (k:ℚ)≤(X.card:ℚ)+S.card := by exact_mod_cast lower
      linarith)
    (by exact_mod_cast orientation) (by exact_mod_cast total)
    (by
      have hh : (X.card:ℚ)*Y.card≤(X.card:ℚ)*k+(S.card:ℚ)*(k*k) := by exact_mod_cast prod
      nlinarith only [hh])
  change ((Fintype.card V:ℤ)-2*(k:ℤ)-1)*((k:ℤ)-S.card)≤(S.card:ℤ)*k*k
  have reflect {a b : ℤ} (h : (a:ℚ)≤(b:ℚ)) : a≤b := by exact_mod_cast h
  apply reflect
  push_cast
  exact q

/-- The finite-domain order upper at the actual vertex connectivity. A root
of degree at most s handles all singleton-side exceptions by its layer count. -/
theorem actual_order_upper (hc : G.Connected) (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (hs : 5≤G.vertexConnectivity) (hk : 3*G.vertexConnectivity<G.secondSmallestDegree)
    (room : G.vertexConnectivity<Fintype.card V-1) :
    let k : ℤ := G.secondSmallestDegree
    let s : ℤ := G.vertexConnectivity
    ((Fintype.card V:ℤ)-2*k-1)*(k-s)≤s*k*k := by
  classical
  let k := G.secondSmallestDegree
  let s := G.vertexConnectivity
  by_cases hz : ∃ z, G.degree z≤s
  · obtain ⟨z,hz⟩ := hz
    have c (a : V) : G.distEven a ≤ k+1 := by simpa only [k,Nat.add_comm 1] using cap a
    have d2 : 2*G.degree z ≤ k+1 := by change 3*s<k at hk; omega
    have row := Graph189LayerCutoff.order_of_small_degree G hc z k c d2
    have prod := Nat.mul_le_mul hz (Nat.sub_le (k+1) (G.degree z))
    have coarse : Fintype.card V≤1+s+k+s*(k+1) := by omega
    change 3*s<k at hk
    have upper : Fintype.card V≤(s+2)*k+1 := by nlinarith only [coarse,hk]
    have uu : (Fintype.card V:ℤ)≤((s:ℤ)+2)*k+1 := by exact_mod_cast upper
    have hh : (Fintype.card V:ℤ)-2*k-1≤(s:ℤ)*k := by nlinarith only [uu]
    have hsk : (s:ℤ)≤k := by exact_mod_cast (show s≤k by omega)
    have m := mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr hsk)
    have p := mul_nonneg (sq_nonneg (s:ℤ)) (show (0:ℤ)≤k by positivity)
    change ((Fintype.card V:ℤ)-2*k-1)*((k:ℤ)-s)≤(s:ℤ)*k*k
    nlinarith only [m,p]
  · push Not at hz
    obtain ⟨A,B,S,sz,sides⟩ := minimum_sides room
    have smaller (T : Finset V) (ht : T.card<S.card) :
        (G.induce {u : V | u∉T}).Connected := connected_after_smaller_deletion T (by omega)
    have high (v : V) : S.card<G.degree v := by simpa only [sz] using hz v
    have h2 : 2≤S.card := by omega
    have hsk : S.card≤G.secondSmallestDegree := by omega
    let H (v : V) := G.secondSmallestDegree≤G.degree v
    rcases le_total (A.filter H).card (B.filter H).card with h|h
    · simpa only [sz] using ordered_side sides hc cap smaller high h2 hsk h
    · simpa only [sz] using ordered_side sides.swap hc cap smaller high h2 hsk h

end Graph189GraphPopulation
#print axioms Graph189GraphPopulation.minimum_sides
#print axioms Graph189GraphPopulation.actual_order_upper
