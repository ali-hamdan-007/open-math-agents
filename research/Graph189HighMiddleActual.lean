import Graph189HighMiddleClosure
import Graph189Order14Relabel
import Graph189DegreeTwoOuter

namespace Graph189HighMiddleActual
open SimpleGraph Graph189DegreeTwoOuter Graph189LowDegreeTwo
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The sufficient closure criterion applied to the adjacent one-miss shape. -/
theorem traceable (h : G.Connected) (hd : G.diam ≤ 3)
    (hn : Fintype.card V = 14) (hs : G.secondSmallestDegree = 5)
    (he : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (z a b : V) (hne : a ≠ b) (hz : G.neighborFinset z = {a,b}) (hab : G.Adj a b)
    (hW : (Finset.univ.filter (fun x => G.dist z x = 2)).card = 5)
    (hma : (Finset.univ.filter (fun x => G.dist z x = 2 ∧ ¬ G.Adj a x)).card = 1)
    (hmb : (Finset.univ.filter (fun x => G.dist z x = 2 ∧ ¬ G.Adj b x)).card = 1)
    (hHigh : 3 ≤ (Finset.univ.filter (fun x => G.dist z x = 2 ∧ 8 ≤ G.degree x)).card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have := h.nonempty
  let W := Finset.univ.filter (fun x => G.dist z x = 2)
  let R := Finset.univ.filter (fun x => G.dist z x = 3)
  let T := W.filter (fun x => 8 ≤ G.degree x)
  let A := W.filter (fun x => ¬ G.Adj a x)
  let B := W.filter (fun x => ¬ G.Adj b x)
  let S := W.filter (fun x => G.Adj a x ∧ G.Adj b x)
  let Fa := R.filter (fun x => G.dist a x = 3)
  let Fb := R.filter (fun x => G.dist b x = 3)
  have hW' : W.card = 5 := hW
  rw [← Finset.filter_filter] at hma hmb hHigh
  have hA : A.card = 1 := hma
  have hB : B.card = 1 := hmb
  have hT : 3 ≤ T.card := hHigh
  have hC := Graph189Order14Relabel.middleCard h z a b hz
  change W.card = A.card+B.card+S.card at hC
  obtain ⟨_,_,_,_,_,_,_,_,hl⟩ := Graph189Order14Relabel.positions h hd hn z a b hne hz
  change 3+A.card+B.card+S.card+R.card = 14 at hl
  have hR : R.card = 6 := by omega
  have az : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hz])
  have bz : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hz])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hz,Finset.card_pair hne]
  have good (x : V) (hx : x ≠ z) : 5 ≤ G.degree x := by
    have hg := Graph189Bipartite.degree_pair (G := G) x z hx
    omega
  have mW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have miss (u : V) (hm : (W.filter (fun x => ¬ G.Adj u x)).card = 1) :
      ∃ p ∈ W, ¬ G.Adj u p ∧ ∀ x ∈ W, G.Adj u x ↔ x ≠ p := by
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hm
    have hp' : p ∈ W.filter (fun x => ¬ G.Adj u x) := by simp [hp]
    obtain ⟨hpW,hno⟩ := Finset.mem_filter.mp hp'
    refine ⟨p,hpW,hno,fun x hx => ?_⟩
    have hmem : x ∈ W.filter (fun x => ¬ G.Adj u x) ↔ ¬ G.Adj u x := by simp [hx]
    rw [hp,Finset.mem_singleton] at hmem
    tauto
  have layer (u v : V) (hu : G.Adj z u) (hv : G.Adj z v) (huv : u ≠ v)
      (huvAdj : G.Adj u v) (hm : (W.filter (fun x => ¬ G.Adj u x)).card = 1) :
      6 ≤ G.degree u ∧ (∀ r ∈ R, ¬ G.Adj u r) ∧
        2 ≤ (R.filter (fun r => G.dist u r = 3)).card ∧
        ∀ r ∈ R.filter (fun r => G.dist u r = 3), (T ∩ G.neighborFinset r).card ≤ 1 := by
    obtain ⟨p,hpW,hup,hm⟩ := miss u hm
    have hno (r : V) (hr : r ∈ R) : ¬ G.Adj u r := by
      intro hur
      have ht := h.dist_triangle (u := z) (v := u) (w := r)
      rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr hur] at ht
      omega
    have hsub : insert z (insert v (W.erase p)) ⊆ G.neighborFinset u := by
      intro x hx
      apply (G.mem_neighborFinset u x).mpr
      rcases Finset.mem_insert.mp hx with e | hx
      · exact e.symm ▸ hu.symm
      · rcases Finset.mem_insert.mp hx with e | hx
        · exact e.symm ▸ huvAdj
        · exact (hm x (Finset.mem_of_mem_erase hx)).mpr (Finset.ne_of_mem_erase hx)
    have hzW : z ∉ W := by simp [W]
    have hvW : v ∉ W := by simp [W,dist_eq_one_iff_adj.mpr hv]
    have h0 : z ∉ insert v (W.erase p) := by
      simp [Finset.mem_insert,G.ne_of_adj hv,Finset.mem_erase,hzW]
    have h1 : v ∉ W.erase p := fun hx => hvW (Finset.mem_of_mem_erase hx)
    have hdeg := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem h0,Finset.card_insert_of_notMem h1,
      Finset.card_erase_of_mem hpW,hW'] at hdeg
    have hpv : G.Adj v p := by
      obtain ⟨w,hw,hwp⟩ := split_two h ((mW p).mp hpW)
      have hw' : w = a ∨ w = b := by simpa [hz] using (G.mem_neighborFinset z w).mpr hw
      have hu' : u = a ∨ u = b := by simpa [hz] using (G.mem_neighborFinset z u).mpr hu
      have hv' : v = a ∨ v = b := by simpa [hz] using (G.mem_neighborFinset z v).mpr hv
      have hwu : w ≠ u := fun eq => hup (eq ▸ hwp)
      have hwv : w = v := by grind
      exact hwv ▸ hwp
    have hpneq : u ≠ p := by
      intro eq
      have hh := (mW p).mp hpW
      rw [← eq,dist_eq_one_iff_adj.mpr hu] at hh
      contradiction
    have hdp : G.dist u p = 2 := two_edges huvAdj hpv hpneq hup
    let D := R.filter (fun r => G.dist u r = 2)
    let F := R.filter (fun r => G.dist u r = 3)
    have hpart : D ∪ F = R := by
      ext r
      simp only [D,F,Finset.mem_union,Finset.mem_filter]
      constructor
      · exact fun hh => hh.elim And.left And.left
      · intro hr
        have hne : u ≠ r := by
          intro eq
          have hh := (mR r).mp hr
          rw [← eq,dist_eq_one_iff_adj.mpr hu] at hh
          contradiction
        have hpos : 0 < G.dist u r := h.pos_dist_of_ne hne
        have hone : G.dist u r ≠ 1 := fun eq => hno r hr (dist_eq_one_iff_adj.mp eq)
        have hle := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := u) (v := r)).trans hd
        have hf : G.dist u r = 2 ∨ G.dist u r = 3 := by omega
        exact hf.imp (fun h => ⟨hr,h⟩) (fun h => ⟨hr,h⟩)
    have hD : D.card ≤ 4 := by
      have hsub : insert p D ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
        intro x hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
        exact (Finset.mem_insert.mp hx).elim (fun eq => eq.symm ▸ hdp) (fun he => (Finset.mem_filter.mp he).2)
      have hpD : p ∉ D := by simp [D,R,(mW p).mp hpW]
      have hh := (Finset.card_le_card hsub).trans (distance_two_cap _ he u)
      rw [Finset.card_insert_of_notMem hpD] at hh
      omega
    have hF : 2 ≤ F.card := by
      have hcard := Finset.card_union_le D F
      rw [hpart,hR] at hcard
      omega
    refine ⟨by exact hdeg,hno,hF,?_⟩
    intro r hr
    obtain ⟨hrR,hur⟩ := Finset.mem_filter.mp hr
    have only := (remote_unique_middle h ((mR r).mp hrR) hur (fun x hx => hm x ((mW x).mpr hx))).2
    have hh : T ∩ G.neighborFinset r ⊆ {p} := by
      intro x hx
      obtain ⟨hxT,hxr⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_singleton.mpr (only x ((mW x).mp (Finset.mem_filter.mp hxT).1)
        ((G.mem_neighborFinset r x).mp hxr).symm)
    exact (Finset.card_le_card hh).trans (by simp)
  obtain ⟨ha,haNo,hFa,hFaN⟩ := layer a b az bz hne hab hA
  obtain ⟨hb,hbNo,hFb,hFbN⟩ := layer b a bz az hne.symm hab.symm hB
  have dt : Disjoint T R := by
    refine Finset.disjoint_left.mpr ?_
    intro x hT hR
    have h2 := (mW x).mp (Finset.mem_filter.mp hT).1
    have h3 := (mR x).mp hR
    omega
  exact Graph189HighMiddleClosure.traceable_of_high_middle hn z a b hne (G.ne_of_adj az.symm)
    (G.ne_of_adj bz.symm) hzd.ge ha hb good T R hT hR dt
    (by simp [T,W]) (by simp [T,W,dist_eq_one_iff_adj.mpr az]) (by simp [T,W,dist_eq_one_iff_adj.mpr bz])
    (by simp [R]) (by simp [R,dist_eq_one_iff_adj.mpr az]) (by simp [R,dist_eq_one_iff_adj.mpr bz])
    (fun _ hx => (Finset.mem_filter.mp hx).2) (fun r hr => ⟨haNo r hr,hbNo r hr⟩)
    Fa Fb (Finset.filter_subset _ _) (Finset.filter_subset _ _) hFa hFb hFaN hFbN

#print axioms traceable
end Graph189HighMiddleActual
