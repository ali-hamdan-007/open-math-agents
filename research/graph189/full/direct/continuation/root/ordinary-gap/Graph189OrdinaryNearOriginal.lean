import Graph189OrdinaryPathGap
import Graph189OrdinaryTightGap
import Graph189OrdinaryGapDebit

open Finset SimpleGraph Graph189ExteriorGap Graph189RootedSplice
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189OrdinaryPathGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Any contact of an omitted vertex is a contact of each high omitted vertex.
The source of the incidence is allowed to be the unique low vertex. -/
theorem transfer_to_high (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) (k5 : 5 ≤ G.secondSmallestDegree)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (longest : Longest p) (clique : CliqueExterior p)
    (a : V) (ha : a∉p.support) (b : V) (hb : b∉p.support) (bh : G.secondSmallestDegree≤G.degree b)
    (w : V) (hw : w∈p.support) (wa : G.Adj w a) : G.Adj w b := by
  classical
  let E := univ \ p.support.toFinset
  have member (v : V) (hv : v ∉ p.support) : v ∈ E :=
    mem_sdiff.mpr ⟨mem_univ _,fun h => hv (List.mem_toFinset.mp h)⟩
  let first : E := ⟨a,member a ha⟩
  let second : E := ⟨b,member b hb⟩
  obtain ⟨A,_,cover,rows⟩ := ordinary_census hc cap k5 p hp longest clique
  obtain ⟨i,valid,why⟩ := List.mem_iff_getElem.mp hw
  have atPos := (get_at p valid).symm.trans why
  have hit : i ∈ contactPositions p first.val :=
    (mem_contactPositions p _ i).mpr ⟨valid,by simpa [first,atPos] using wa⟩
  have secondHit : i∈contactPositions p second.val := (rows second bh).symm ▸ cover first hit
  have real := (mem_contactPositions p _ i).mp secondHit
  simpa [second,atPos] using real.2

/-- A path omitting at most ceil(k/2)+1 vertices forces traceability whenever
the minimum degree is at least three and the second-smallest degree is at least six. -/
theorem traceable_of_near_unrestricted (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (k6 : 6 ≤ G.secondSmallestDegree) (minimum : 3 ≤ G.minDegree)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (near : Near p) :
    ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  have k5 : 5≤G.secondSmallestDegree := by omega
  by_contra fail
  obtain ⟨a,b,P,hP,longest⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) x
  have longestP : Longest P := fun r hr => longest r hr
  have lengthBound := longest p hp
  have pLen := p.length_support
  have PLen := P.length_support
  have nearP : Near P := by
    change Fintype.card V ≤ p.support.length + (G.secondSmallestDegree + 1) / 2 + 1 at near
    change Fintype.card V ≤ P.support.length + (G.secondSmallestDegree + 1) / 2 + 1
    omega
  have clique {u v : V} (r : G.Walk u v) (hr : r.IsPath) (maximal : Longest r)
      (near : Near r) : CliqueExterior r :=
    near_exterior_clique cap k5 minimum r hr maximal near
      (high_omitted_of_nontraceable hc cap k5 minimum fail r hr maximal)
  have cliqueP := clique P hP longestP nearP
  let E := univ \ P.support.toFinset
  let k := G.secondSmallestDegree
  let u := k/2
  have hk : 6≤k := k6
  have size : E.card=(k+1)/2+1 := cliqueP.1
  have outside (v : V) (hv : v∈E) : v∉P.support := fun h =>
    (mem_sdiff.mp hv).2 (List.mem_toFinset.mpr h)
  let H : Finset E := univ.filter fun z => k≤G.degree z.val
  let L : Finset E := univ.filter fun z => ¬k≤G.degree z.val
  have low : L.card≤1 := card_le_one_iff.mpr (by
    intro v w hv hw
    by_contra diff
    have ne : v.val≠w.val := fun eq => diff (Subtype.ext eq)
    exact (degree_pair (G:=G) _ _ ne).elim (mem_filter.mp hv).2 (mem_filter.mp hw).2)
  have total : H.card+L.card=E.card := by
    have e := card_filter_add_card_filter_not (s:=(univ : Finset E)) (p:=fun v => k≤G.degree v.val)
    rwa [card_univ,Fintype.card_coe] at e
  obtain ⟨first,fH,last,lH,ne⟩ := one_lt_card.mp (show 1<H.card by omega)
  have fh := (mem_filter.mp fH).2
  have lh := (mem_filter.mp lH).2
  have uniform (v : V) (hv : v∈P.support) (adj : G.Adj v first.val) : G.Adj v last.val :=
    transfer_to_high hc cap k5 P hP longestP cliqueP first.val (outside _ first.property)
      last.val (outside _ last.property) lh v hv adj
  have full : G.induce (E : Set V) = ⊤ := by
    ext a b
    change G.Adj a.val b.val ↔ a ≠ b
    constructor
    · exact fun edge same => edge.ne (congrArg Subtype.val same)
    · exact fun different => cliqueP.2 a.val a.property b.val b.property
        (fun same => different (Subtype.ext same))
  have routes (a b : E) (ne : a ≠ b) :
      ∃ q : (G.induce (E : Set V)).Walk a b, q.IsHamiltonian := by
    rw [full]
    exact Graph189TerminalLeafClosure.complete_prescribed a b ne
  obtain ⟨A,cardA,_,rows⟩ := ordinary_census hc cap k5 P hP longestP cliqueP
  have marks := (congrArg Finset.card (rows first fh)).trans cardA
  obtain ⟨lo,hi,width,bound,g,coords⟩ := find_tight_interval P hP longestP E E.card u rfl
    (by dsimp [u]; omega) (by omega) outside first last ne routes uniform marks
    (ordinary_path_room hc cap P hP cliqueP)
  obtain ⟨root,rootBoundary,fromFirst,i,iGap,edge⟩ := g.boundary
  have rootOn : root ∈ P.support := by
    rw [g.split]
    simp only [List.mem_append] at rootBoundary ⊢
    tauto
  have nd := hP.support_nodup
  rw [g.split] at nd
  have rootOutside : root ∉ g.block := by
    intro h
    rcases List.mem_append.mp rootBoundary with l | r
    · exact List.disjoint_left.mp nd.of_append_left.disjoint l h
    · exact List.disjoint_left.mp nd.disjoint (List.mem_append_right _ h) r
  obtain ⟨c,d,Q,hQ,_,lengthQ,omits,stays⟩ := full_exterior_splice P hP root rootOn
    E E.card rfl outside first last ne
    routes uniform g.left g.block g.right g.split rootOutside g.before g.after
  have same : Q.length = P.length := by
    have QLen := Q.length_support
    have size := g.size
    omega
  have longestQ : Longest Q := by
    intro c d r hr
    rw [same]
    exact longestP r hr
  have nearQ : Near Q := by
    have equal : Q.support.length = P.support.length := by
      have QLen := Q.length_support
      omega
    change Fintype.card V ≤ Q.support.length + (G.secondSmallestDegree + 1) / 2 + 1
    rw [equal]
    exact nearP
  have hits (w : V) (hw : w∈g.block) (high : k≤G.degree w) : G.dist first.val w=2 := by
    have on : w∈P.support := by simp [g.split,hw]
    have diff : first.val≠w := fun e => outside _ first.property (by simpa [e] using on)
    have cw := transfer_to_high hc cap k5 Q hQ longestQ (clique Q hQ longestQ nearQ)
      i (omits _ iGap) w (omits _ hw) high root (stays _ rootBoundary) edge
    exact two_step_metric diff (g.unmarked _ hw) fromFirst cw.symm
  have wide (i) (ii : i∈contactPositions P first.val) (j) (jj : j∈contactPositions P first.val)
      (lt : i<j) : i+3≤j := by
    obtain ⟨ir,ic⟩ := (mem_contactPositions P _ _).mp ii
    obtain ⟨jr,jc⟩ := (mem_contactPositions P _ _).mp jj
    have right := uniform (P.getVert j) (P.getVert_mem_support j) jc
    have edge := cliqueP.2 _ first.property _ last.property (fun eq => ne (Subtype.ext eq))
    exact adjacent_omitted_contact_spacing P hP longestP (outside _ first.property)
      (outside _ last.property) edge ⟨i,ir⟩ ⟨j,jr⟩ lt
      (by simpa [get_at] using ic) (by simpa [get_at] using right)
  have quota := second_layer_budget cap first.val
  have debit := tight_gap_debit P hP longestP (outside _ first.property) (by omega : 3≤E.card)
    width bound marks wide g coords hits quota
  change 2*(k/2)+E.card≤k+3 at debit
  omega

#print axioms transfer_to_high
#print axioms traceable_of_near_unrestricted
end Graph189OrdinaryPathGap
