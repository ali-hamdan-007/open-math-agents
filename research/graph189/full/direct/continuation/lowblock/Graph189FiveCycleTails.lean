import Graph189FiveCycleSixData

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleTails
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b r : V}

/-- Two different cycle vertices each seeing two path marks can run along
the longer cycle arc to a common anchor and then through two exterior
vertices. The two resulting six-vertex tails and a four-vertex inner
arc force at least eighteen vertices on the longest path. -/
theorem order (p : G.Walk a b) (hp : p.IsPath) (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    {c x y u v : V} (cc : c∈C.support) (uc : u∈C.support) (vc : v∈C.support)
    (un : u≠c) (vn : v≠c) (uv : u≠v) (cx : G.Adj c x) (xy : G.Adj x y)
    (xp : x∉p.support) (yp : y∉p.support) (xc : x∉C.support) (yc : y∉C.support)
    (rowU : 2≤(contactPositions p u).card) (rowV : 2≤(contactPositions p v).card) :
    18≤p.support.length := by
  classical
  obtain ⟨_,_,join⟩ := Graph189TwoExteriorLinks.cycle_routes C hc
  have tail {z : V} (zc : z∈C.support) (ne : z≠c) : ExteriorRoute p z y 6 := by
    obtain ⟨q,hq,len,inc⟩ := join _ (List.mem_toFinset.mpr zc) _ (List.mem_toFinset.mpr cc) ne
    have noX : x∉q.support := fun h => xc (List.mem_toFinset.mp (inc _ h))
    have noY : y∉(q.concat cx).support := by
      rw [Walk.support_concat,List.mem_append]
      exact not_or.mpr ⟨fun h => yc (List.mem_toFinset.mp (inc _ h)),by simpa using xy.ne.symm⟩
    refine ⟨(q.concat cx).concat xy,(hq.concat noX cx).concat noY xy,?_,?_⟩
    · apply List.disjoint_left.mpr
      intro w hw
      simp only [Walk.support_concat,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (h|e)|e
      · exact off _ (List.mem_toFinset.mp (inc _ h))
      · exact e ▸ xp
      · exact e ▸ yp
    · simp only [Walk.support_concat,List.length_append,List.length_cons,List.length_nil] 
      omega
  have middle {s t : V} (sc : s∈C.support) (tc : t∈C.support) (ne : s≠t) : ExteriorRoute p s t 4 := by
    obtain ⟨q,hq,len,inc⟩ := join _ (List.mem_toFinset.mpr sc) _ (List.mem_toFinset.mpr tc) ne
    exact ⟨q,hq,List.disjoint_left.mpr (fun z hz => off z (List.mem_toFinset.mp (inc z hz))),by omega⟩
  obtain ⟨i,im⟩ := card_pos.mp (show 0<(contactPositions p u).card by omega)
  obtain ⟨j,jm,ji⟩ := exists_mem_ne (show 1<(contactPositions p v).card by omega) i
  obtain ⟨ir,ie⟩ := (mem_contactPositions _ _ _).mp im
  obtain ⟨jr,je⟩ := (mem_contactPositions _ _ _).mp jm
  let I : Fin p.support.length := ⟨i,ir⟩
  let J : Fin p.support.length := ⟨j,jr⟩
  have ix : G.Adj p.support[I.val] u := by simpa only [I,get_at] using ie
  have jx : G.Adj p.support[J.val] v := by simpa only [J,get_at] using je
  have apply_three {s t : V} {i j : Fin p.support.length} (before : i<j) (si : G.Adj p.support[i.val] s)
      (tj : G.Adj p.support[j.val] t) (l : ExteriorRoute p s y 6) (r : ExteriorRoute p t y 6)
      (m : ExteriorRoute p s t 4) : 18≤p.support.length := by
    obtain ⟨q,hq,dq,n⟩ := l
    have h := prefix_of_detour p hp mx i q.reverse hq.reverse
      (by rw [Walk.support_reverse]; exact List.disjoint_reverse_left.mpr dq) si.symm
    rw [Walk.support_reverse,List.length_reverse] at h
    obtain ⟨q,hq,dq,n'⟩ := r
    have h' := suffix_of_detour p hp mx j q hq dq tj
    obtain ⟨q,hq,dq,n''⟩ := m
    have h'' := interval_of_detour p hp mx i j before q hq dq si tj.symm
    omega
  rcases lt_or_gt_of_ne (show I≠J from fun e => ji (congrArg Fin.val e).symm) with ij|ji
  · exact apply_three ij ix jx (tail uc un) (tail vc vn) (middle uc vc uv)
  · exact apply_three ji jx ix (tail vc vn) (tail uc un) (middle vc uc uv.symm)

#print axioms order
end Graph189FiveCycleTails
