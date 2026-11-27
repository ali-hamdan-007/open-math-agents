import Graph189Order14Relabel
import Graph189DegreeTwoOuter

namespace Graph189TwoTwo
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoOuter
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 600000 in
private theorem impossibleOfLayers (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 5) (z a b : V) (hne : a ≠ b)
    (hZ : G.neighborFinset z = {a,b}) (hab : G.Adj a b)
    (hw : (Finset.univ.filter (fun x => G.dist z x = 2)).card = 5)
    (hr : (Finset.univ.filter (fun x => G.dist z x = 3)).card = 6)
    (hma : (Finset.univ.filter (fun x => G.dist z x = 2 ∧ ¬ G.Adj a x)).card = 2)
    (hmb : (Finset.univ.filter (fun x => G.dist z x = 2 ∧ ¬ G.Adj b x)).card = 2) :
    False := by
  classical
  have := h.nonempty
  let s := G.secondSmallestDegree
  change s = 5 at hs
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  have mW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have az : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have bz : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have cap (u : V) : (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s :=
    distance_two_cap s hσ u
  have ds (x y : V) : G.dist x y ≤ 3 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := x) (v := y)).trans hd
  have anchors {u : V} (hu : G.Adj z u) : u = a ∨ u = b := by
    simpa [hZ] using (G.mem_neighborFinset z u).mpr hu
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hh := ds z x
    have hr : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases hr with h0 | h1 | h2 | h3
    · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
    · have hu := anchors (dist_eq_one_iff_adj.mp h1)
      exact hu.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((mW x).mpr h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((mR x).mpr h3))))
  have reachW {r : V} (hr : r ∈ R) : ∃ w ∈ W, G.Adj w r := by
    obtain ⟨w,hw,hadj⟩ := split_three h ((mR r).mp hr)
    exact ⟨w,(mW w).mpr hw,hadj⟩
  have reachAnchor {w : V} (hw : w ∈ W) : G.Adj a w ∨ G.Adj b w := by
    obtain ⟨u,hu,hadj⟩ := split_two h ((mW w).mp hw)
    rcases anchors hu with e | e
    · exact Or.inl (e ▸ hadj)
    · exact Or.inr (e ▸ hadj)
  have remoteNo {u r : V} (hu : G.Adj z u) (hr : r ∈ R) : ¬ G.Adj u r := by
    intro hadj
    have ht := h.dist_triangle (u := z) (v := u) (w := r)
    rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr hadj] at ht
    omega
  have remoteTwo {u r w : V} (hu : G.Adj z u) (hr : r ∈ R) (huw : G.Adj u w)
      (hwr : G.Adj w r) : G.dist u r = 2 := by
    have hne : u ≠ r := by
      intro e
      have hh := (mR r).mp hr
      rw [← e,dist_eq_one_iff_adj.mpr hu] at hh
      contradiction
    exact two_edges huw hwr hne (remoteNo hu hr)
  let Da := R.filter (fun r => G.dist a r = 2)
  let Db := R.filter (fun r => G.dist b r = 2)
  let Ma := W.filter (fun w => ¬ G.Adj a w)
  let Mb := W.filter (fun w => ¬ G.Adj b w)
  have lim (u v : V) (huv : G.Adj u v) (hu : G.Adj z u)
      (hav : ∀ w ∈ W, G.Adj u w ∨ G.Adj v w) :
      (R.filter (fun r => G.dist u r = 2)).card + (W.filter (fun w => ¬ G.Adj u w)).card ≤ s := by
    let D := R.filter (fun r => G.dist u r = 2)
    let M := W.filter (fun w => ¬ G.Adj u w)
    have hsub : D ∪ M ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_union.mp hx with hd' | hm
      · exact (Finset.mem_filter.mp hd').2
      · obtain ⟨hxW,hn⟩ := Finset.mem_filter.mp hm
        have hne : u ≠ x := by
          intro e
          have hh := (mW x).mp hxW
          rw [← e,dist_eq_one_iff_adj.mpr hu] at hh
          contradiction
        exact two_edges huv ((hav x hxW).resolve_left hn) hne hn
    have hdis : Disjoint D M := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      have hx' := (mR x).mp (Finset.mem_filter.mp hx).1
      have hy' := (mW x).mp (Finset.mem_filter.mp hy).1
      omega
    have hl := (Finset.card_le_card hsub).trans (cap u)
    rw [Finset.card_union_of_disjoint hdis] at hl
    exact hl
  have coverR : Da ∪ Db = R := by
    apply Finset.Subset.antisymm (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    intro r hr
    obtain ⟨w,hw,hwr⟩ := reachW hr
    apply Finset.mem_union.mpr
    exact (reachAnchor hw).imp
      (fun he => Finset.mem_filter.mpr ⟨hr,remoteTwo az hr he hwr⟩)
      (fun he => Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr he hwr⟩)
  have la : Da.card + Ma.card ≤ s := lim a b hab az (fun _ hw => reachAnchor hw)
  have lb : Db.card + Mb.card ≤ s := lim b a hab.symm bz (fun _ hw => (reachAnchor hw).symm)
  have hsum := Finset.card_union_le Da Db
  rw [coverR] at hsum
  rw [← Finset.filter_filter] at hma hmb
  have hma' : Ma.card = 2 := hma
  have hmb' : Mb.card = 2 := hmb
  have hw' : W.card = 5 := hw
  have hr' : R.card = 6 := hr
  have hda : Da.card = 3 := by omega
  have hdb : Db.card = 3 := by omega
  have hDD : Disjoint Da Db := by
    have hh := Finset.card_union_add_card_inter Da Db
    rw [coverR,hr',hda,hdb] at hh
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  have hMM : Disjoint Ma Mb := by
    refine Finset.disjoint_left.mpr ?_
    intro x ha hb
    exact (reachAnchor (Finset.mem_filter.mp ha).1).elim (Finset.mem_filter.mp ha).2
      (Finset.mem_filter.mp hb).2
  have hsubM : Ma ∪ Mb ⊆ W :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  let C := W \ (Ma ∪ Mb)
  have hcc : C.card = 1 := by
    dsimp [C]
    rw [Finset.card_sdiff_of_subset hsubM,Finset.card_union_of_disjoint hMM,hw',hma',hmb']
  obtain ⟨c,hC⟩ := Finset.card_eq_one.mp hcc
  have hc : c ∈ C := by simp [hC]
  have hcW := (Finset.mem_sdiff.mp hc).1
  have hca : G.Adj a c := by
    by_contra he
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcW,he⟩))
  have hcb : G.Adj b c := by
    by_contra he
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcW,he⟩))
  have noC (r : V) (hr : r ∈ R) : ¬ G.Adj c r := by
    intro he
    exact Finset.disjoint_left.mp hDD
      (Finset.mem_filter.mpr ⟨hr,remoteTwo az hr hca he⟩)
      (Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr hcb he⟩)
  have notZ {x : V} (hx : x ∈ W) : x ≠ z := by
    intro he
    have hh := (mW x).mp hx
    simp [he] at hh
  have sep {x r : V} (hx : x ∈ W) (hr : r ∈ R) : x ≠ r := by
    intro he
    have h2 := (mW x).mp hx
    have h3 := (mR r).mp hr
    rw [he] at h2
    omega
  have good (x : V) (hx : x ∈ W) : 5 ≤ G.degree x := by
    have h := Graph189Bipartite.degree_pair (G := G) x z (notZ hx)
    omega
  have budget (u : V) (K : Finset V) (hK : ∀ x ∈ K, G.dist u x = 2) : K.card ≤ 5 := by
    have hsub : K ⊆ Finset.univ.filter (fun x => G.dist u x = 2) :=
      fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hK x hx⟩
    have hle := (Finset.card_le_card hsub).trans (cap u)
    omega
  have missed : ∃ x ∈ W, x ≠ c ∧ ¬ G.Adj c x := by
    by_contra! hn
    have hd := budget c R (by
      intro r hr
      obtain ⟨w,hw,hwr⟩ := reachW hr
      have hwne : w ≠ c := fun e => noC r hr (e ▸ hwr)
      exact two_edges (hn w hw hwne) hwr (sep hcW hr) (noC r hr))
    omega
  obtain ⟨x,hxW,hxc,hcx⟩ := missed
  have hxm : x ∈ Ma ∪ Mb := by
    by_contra he
    have hxC : x ∈ C := Finset.mem_sdiff.mpr ⟨hxW,he⟩
    exact hxc (by simpa [hC] using hxC)
  have cAll (w : V) (hwW : w ∈ W) (hwc : w ≠ c) (hwx : w ≠ x) : G.Adj c w := by
    let F := insert a (insert b ((W.erase c).erase x))
    have hsub : G.neighborFinset c ⊆ F := by
      intro t ht
      have he := (G.mem_neighborFinset c t).mp ht
      rcases all t with ho | ho | ho | hw | hr
      · subst t
        have hh := (mW c).mp hcW
        rw [dist_eq_one_iff_adj.mpr he.symm] at hh
        contradiction
      · exact Finset.mem_insert.mpr (Or.inl ho)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl ho))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun eq => hcx (eq ▸ he),Finset.mem_erase.mpr ⟨(G.ne_of_adj he).symm,hw⟩⟩))
      · exact (noC t hr he).elim
    have h3 : ((W.erase c).erase x).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxc,hxW⟩),
        Finset.card_erase_of_mem hcW,hw']
    have hF : F.card ≤ 5 := by
      have h1 := Finset.card_insert_le a (insert b ((W.erase c).erase x))
      have h2 := Finset.card_insert_le b ((W.erase c).erase x)
      change F.card ≤ _ at h1
      omega
    have hle : 5 ≤ (G.neighborFinset c).card := good c hcW
    have hEq := Finset.eq_of_subset_of_card_le hsub (hF.trans hle)
    exact (G.mem_neighborFinset c w).mp (hEq.symm ▸ Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwx,Finset.mem_erase.mpr ⟨hwc,hwW⟩⟩)))
  let M (u : V) := W.filter (fun w => ¬ G.Adj u w)
  let D (u : V) := R.filter (fun r => G.dist u r = 2)
  have finish (u v : V) (hu : G.Adj z u) (hv : G.Adj z v)
      (orientation : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
      (hxM : x ∈ M v) (hM : (M v).card = 2) (hDv : (D v).card = 3) : False := by
    have dd : Disjoint (D u) (D v) := by
      rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hDD
      · exact hDD.symm
    have unionD : D u ∪ D v = R := by
      rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact coverR
      · rw [Finset.union_comm]; exact coverR
    have getAnchor (w : V) (hw : w ∈ W) : G.Adj u w ∨ G.Adj v w := by
      rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact reachAnchor hw
      · exact (reachAnchor hw).symm
    have hux : G.Adj u x := (getAnchor x hxW).resolve_right (Finset.mem_filter.mp hxM).2
    have hys : 0 < ((M v).erase x).card := by rw [Finset.card_erase_of_mem hxM,hM]; decide
    obtain ⟨y,hy⟩ := Finset.card_pos.mp hys
    have hyx := Finset.ne_of_mem_erase hy
    have ⟨hyW,hyv⟩ := Finset.mem_filter.mp (Finset.mem_of_mem_erase hy)
    have hvc : G.Adj v c := by
      rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hcb
      · exact hca
    have hyc : y ≠ c := fun e => hyv (e.symm ▸ hvc)
    have cy := cAll y hyW hyc hyx
    have yNoV (r : V) (hr : r ∈ D v) : ¬ G.Adj y r := by
      intro he
      have hrR := (Finset.mem_filter.mp hr).1
      have huy := (getAnchor y hyW).resolve_right hyv
      exact Finset.disjoint_left.mp dd (Finset.mem_filter.mpr ⟨hrR,remoteTwo hu hrR huy he⟩) hr
    have cvTwo (r : V) (hr : r ∈ D v) : G.dist c r = 2 := by
      have hrR := (Finset.mem_filter.mp hr).1
      obtain ⟨w,hw,hwr⟩ := reachW hrR
      have hwc : w ≠ c := fun e => noC r hrR (e ▸ hwr)
      have hwx : w ≠ x := by
        intro e
        have hrU : r ∈ D u :=
          Finset.mem_filter.mpr ⟨hrR,remoteTwo hu hrR hux (e ▸ hwr)⟩
        exact Finset.disjoint_left.mp dd hrU hr
      exact two_edges (cAll w hw hwc hwx) hwr (sep hcW hrR) (noC r hrR)
    have hcz : G.dist c z = 2 := by rw [SimpleGraph.dist_comm]; exact (mW c).mp hcW
    have hcu : G.Adj c u := by
      rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hca.symm
      · exact hcb.symm
    have hcx2 := two_edges hcu hux hxc.symm hcx
    let K := insert x (insert z (D v))
    have hzDv : z ∉ D v := by simp [D,R]
    have hxK : x ∉ insert z (D v) := by
      intro he
      rcases Finset.mem_insert.mp he with e | hm
      · exact notZ hxW e
      · exact sep hxW (Finset.mem_filter.mp hm).1 rfl
    have hK : K.card = 5 := by
      dsimp [K]
      rw [Finset.card_insert_of_notMem hxK,Finset.card_insert_of_notMem hzDv,hDv]
    have nearK (r : V) (hr : r ∈ K) : G.dist c r = 2 := by
      rcases Finset.mem_insert.mp hr with e | he
      · exact e.symm ▸ hcx2
      · rcases Finset.mem_insert.mp he with e | he
        · exact e.symm ▸ hcz
        · exact cvTwo r he
    have yNoU (r : V) (hr : r ∈ D u) : ¬ G.Adj y r := by
      intro he
      have hrR := (Finset.mem_filter.mp hr).1
      have hcr := two_edges cy he (sep hcW hrR) (noC r hrR)
      have hrK : r ∉ K := by
        intro hmr
        rcases Finset.mem_insert.mp hmr with e | hmr
        · exact sep hxW hrR e.symm
        · rcases Finset.mem_insert.mp hmr with e | hm
          · have hbad := (mR r).mp hrR
            simp [e] at hbad
          · exact Finset.disjoint_left.mp dd hr hm
      have hh := budget c (insert r K) (by
        intro t ht
        exact (Finset.mem_insert.mp ht).elim (fun e => e.symm ▸ hcr) (nearK t))
      rw [Finset.card_insert_of_notMem hrK,hK] at hh
      omega
    have yNoR (r : V) (hr : r ∈ R) : ¬ G.Adj y r := by
      rw [← unionD] at hr
      exact (Finset.mem_union.mp hr).elim (yNoU r) (yNoV r)
    have hsub : G.neighborFinset y ⊆ insert u (W.erase y) := by
      intro w hw
      have he := (G.mem_neighborFinset y w).mp hw
      have cases : w = z ∨ w = u ∨ w = v ∨ w ∈ W ∨ w ∈ R := by
        rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact all w
        · simpa [or_comm,or_left_comm,or_assoc] using all w
      rcases cases with e | e | e | hwW | hwR
      · subst w
        have hbad := (mW y).mp hyW
        rw [dist_eq_one_iff_adj.mpr he.symm] at hbad
        contradiction
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact (hyv ((e ▸ he).symm)).elim
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨(G.ne_of_adj he).symm,hwW⟩)
      · exact (yNoR w hwR he).elim
    have hle := Finset.card_insert_le u (W.erase y)
    rw [Finset.card_erase_of_mem hyW,hw'] at hle
    have hg : 5 ≤ (G.neighborFinset y).card := good y hyW
    have hEq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hh := budget y R (by
      intro r hr
      obtain ⟨w,hw,hwr⟩ := reachW hr
      have he : w ≠ y := fun e => yNoR r hr (e ▸ hwr)
      have hwy : w ∈ G.neighborFinset y := hEq.symm ▸ Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨he,hw⟩)
      exact two_edges ((G.mem_neighborFinset y w).mp hwy) hwr (sep hyW hr) (yNoR r hr))
    omega
  rcases Finset.mem_union.mp hxm with hxa | hxb
  · exact finish b a bz az (Or.inr ⟨rfl,rfl⟩) hxa hma' hda
  · exact finish a b az bz (Or.inl ⟨rfl,rfl⟩) hxb hmb' hdb

/-- In an order-fourteen graph under the original distance bound, adjacent
anchors cannot each miss two of the five middle-layer vertices. -/
theorem impossible (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 5) (hn : Fintype.card V = 14)
    (z a b : V) (hne : a ≠ b)
    (hZ : G.neighborFinset z = {a,b}) (hab : G.Adj a b)
    (hw : (Finset.univ.filter (fun x => G.dist z x = 2)).card = 5)
    (hma : (Finset.univ.filter (fun x => G.dist z x = 2 ∧ ¬ G.Adj a x)).card = 2)
    (hmb : (Finset.univ.filter (fun x => G.dist z x = 2 ∧ ¬ G.Adj b x)).card = 2) :
    False := by
  classical
  let W := Finset.univ.filter (fun x => G.dist z x = 2)
  let R := Finset.univ.filter (fun x => G.dist z x = 3)
  let A := W.filter (fun x => ¬ G.Adj a x)
  let B := W.filter (fun x => ¬ G.Adj b x)
  let S := W.filter (fun x => G.Adj a x ∧ G.Adj b x)
  have hC := Graph189Order14Relabel.middleCard h z a b hZ
  change W.card = A.card + B.card + S.card at hC
  obtain ⟨_,_,_,_,_,_,_,_,hl⟩ := Graph189Order14Relabel.positions h hd hn z a b hne hZ
  change 3+A.card+B.card+S.card+R.card = 14 at hl
  have hW : W.card = 5 := hw
  have hR : R.card = 6 := by omega
  exact impossibleOfLayers h hd hσ hs z a b hne hZ hab hw hR hma hmb

#print axioms impossible
end Graph189TwoTwo
