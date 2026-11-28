import Graph189FullExteriorExchange
import Graph189HighMinimumGap
import Graph189OrdinaryContactRows
import Graph189QuadraticOrder
import Graph189OrderBound
import Graph189SingleExteriorShift
import Graph189ThreeRegularMinimum
import Graph189UnrestrictedMinimumDeletion

open Finset SimpleGraph Graph189ExteriorGap Graph189RootedSplice
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

namespace Graph189OrdinaryPathGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def Longest {x y : V} (p : G.Walk x y) : Prop :=
  ∀ {a b : V}, ∀ q : G.Walk a b, q.IsPath → q.length ≤ p.length

def Near {x y : V} (p : G.Walk x y) : Prop :=
  Fintype.card V ≤ p.support.length + (G.secondSmallestDegree + 1) / 2 + 1

def CliqueExterior {x y : V} (p : G.Walk x y) : Prop :=
  let E := univ \ p.support.toFinset
  E.card = (G.secondSmallestDegree + 1) / 2 + 1 ∧
    ∀ a ∈ E, ∀ b ∈ E, a ≠ b → G.Adj a b

private theorem second_layer_budget (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (a : V) : (univ.filter (fun b => G.dist a b = 2)).card ≤ G.secondSmallestDegree := by
  classical
  let T := univ.filter (fun b => G.dist a b = 2)
  have absent : a ∉ T := by simp [T]
  have subset : insert a T ⊆ univ.filter (fun b => Even (G.dist a b)) := by
    intro b hb
    rcases mem_insert.mp hb with rfl | member
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp member).2]; decide⟩
  have count := card_le_card subset
  rw [card_insert_of_notMem absent] at count
  change T.card + 1 ≤ G.distEven a at count
  have bound := cap a
  change T.card ≤ G.secondSmallestDegree
  omega

/-- The strict single-row shift shell excludes an isolated high vertex. The
checked two-row contact degree then excludes a lone low neighbor, since its
original degree is at least three. -/
theorem high_exterior_neighbor [Nontrivial V]
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (k5 : 5 ≤ G.secondSmallestDegree) (minimum : 3 ≤ G.minDegree)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (longest : Longest p)
    {a : V} (outside : a ∉ p.support) (high : G.secondSmallestDegree ≤ G.degree a) :
    ∃ b, b ∉ p.support ∧ G.secondSmallestDegree ≤ G.degree b ∧ G.Adj a b := by
  classical
  by_contra none
  let O := G.neighborFinset a \ p.support.toFinset
  have off {b : V} (hb : b ∈ O) : b ∉ p.support :=
    fun on => (mem_sdiff.mp hb).2 (List.mem_toFinset.mpr on)
  have edge {b : V} (hb : b ∈ O) : G.Adj a b :=
    (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hb).1
  have low {b : V} (hb : b ∈ O) : G.degree b < G.secondSmallestDegree :=
    Nat.lt_of_not_ge (fun h => none ⟨b,off hb,h,edge hb⟩)
  have one : O.card ≤ 1 := card_le_one_iff.mpr (by
    intro b c hb hc
    by_contra ne
    rcases degree_pair (G:=G) b c ne with h | h
    · exact (not_le_of_gt (low hb)) h
    · exact (not_le_of_gt (low hc)) h)
  have split := card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  rw [G.card_neighborFinset_eq_degree, ← contact_card_neighbors p hp a] at split
  change O.card + (contactPositions p a).card = G.degree a at split
  have quota := second_layer_budget cap a
  by_cases empty : O.card = 0
  · have marks : (contactPositions p a).Nonempty := card_pos.mp (by omega)
    have witness := single_positions_lt_path_shell p hp longest outside marks
    have subset : p.support.toFinset.filter (fun b => G.dist a b = 2) ⊆
        univ.filter (fun b => G.dist a b = 2) :=
      filter_subset_filter _ (subset_univ _)
    have bound := (card_le_card subset).trans quota
    omega
  · obtain ⟨b,hb⟩ := card_pos.mp (show 0 < O.card by omega)
    have bound := cross_contact_degree p hp longest outside (off hb) (edge hb) quota
    rw [← contact_card_neighbors p hp a] at bound
    change (contactPositions p a).card + G.degree b ≤ G.secondSmallestDegree + O.card at bound
    have bMinimum := minimum.trans (G.minDegree_le_degree b)
    omega

/-- Within the near-spanning allowance, one high omitted vertex forces the
entire exterior to be a clique of order ceil(k/2)+1. -/
theorem near_exterior_clique [Nontrivial V]
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (k5 : 5 ≤ G.secondSmallestDegree) (minimum : 3 ≤ G.minDegree)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (longest : Longest p) (near : Near p)
    (highOutside : ∃ a, a ∉ p.support ∧ G.secondSmallestDegree ≤ G.degree a) :
    CliqueExterior p := by
  classical
  let E := univ \ p.support.toFinset
  let h := (G.secondSmallestDegree + 1) / 2
  have outside {a : V} (ha : a ∈ E) : a ∉ p.support :=
    fun on => (mem_sdiff.mp ha).2 (List.mem_toFinset.mpr on)
  have internal {a : V} (ha : a ∈ E) (high : G.secondSmallestDegree ≤ G.degree a) :
      h ≤ (G.neighborFinset a \ p.support.toFinset).card := by
    obtain ⟨b,bOutside,bHigh,ab⟩ := high_exterior_neighbor cap k5 minimum p hp longest (outside ha) high
    have bound := half_degree_outside_longest p hp longest (outside ha) bOutside ab
      (second_layer_budget cap a) bHigh
    dsimp [h]
    omega
  have within (a : V) : G.neighborFinset a \ p.support.toFinset ⊆ E.erase a := by
    intro b hb
    obtain ⟨adj,off⟩ := mem_sdiff.mp hb
    have different := ((G.mem_neighborFinset _ _).mp adj).ne.symm
    exact mem_erase.mpr ⟨different,mem_sdiff.mpr ⟨mem_univ _,off⟩⟩
  have total := card_sdiff_add_card_inter (univ : Finset V) p.support.toFinset
  rw [univ_inter,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at total
  change E.card + p.support.length = Fintype.card V at total
  change Fintype.card V ≤ p.support.length + h + 1 at near
  obtain ⟨a,off,high⟩ := highOutside
  have inE : a ∈ E := mem_sdiff.mpr ⟨mem_univ _,fun hit => off (List.mem_toFinset.mp hit)⟩
  have lower := (internal inE high).trans (card_le_card (within a))
  rw [card_erase_of_mem inE] at lower
  have size : E.card = h + 1 := by omega
  change E.card = h + 1 ∧ _
  refine ⟨size,?_⟩
  have fromHigh {a b : V} (ha : a ∈ E) (hb : b ∈ E) (ne : a ≠ b)
      (high : G.secondSmallestDegree ≤ G.degree a) : G.Adj a b := by
    have count := internal ha high
    have saturated := eq_of_subset_of_card_le (within a) (by
      rw [card_erase_of_mem ha,size]
      omega)
    have hit : b ∈ G.neighborFinset a \ p.support.toFinset :=
      saturated.symm ▸ mem_erase.mpr ⟨ne.symm,hb⟩
    exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hit).1
  intro a ha b hb ne
  rcases degree_pair (G:=G) a b ne with high | high
  · exact fromHigh ha hb ne high
  · exact (fromHigh hb ha ne.symm high).symm

/-- With no high omitted vertex, a counterexample would have a Hamiltonian
minimum deletion. The unrestricted minimum-deletion result rules it out. -/
theorem high_omitted_of_nontraceable [Nontrivial V] (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (k5 : 5 ≤ G.secondSmallestDegree) (minimum : 3 ≤ G.minDegree)
    (notTraceable : ¬ ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (longest : Longest p) :
    ∃ a, a ∉ p.support ∧ G.secondSmallestDegree ≤ G.degree a := by
  classical
  by_contra never
  let E := univ \ p.support.toFinset
  have small (a : V) (ha : a ∈ E) : G.degree a < G.secondSmallestDegree :=
    Nat.lt_of_not_ge (fun high => never ⟨a,fun h => (mem_sdiff.mp ha).2 (List.mem_toFinset.mpr h),high⟩)
  have one : E.card ≤ 1 := card_le_one_iff.mpr (by
    intro a b ha hb
    by_contra different
    rcases degree_pair (G:=G) a b different with high | high
    · exact (not_le_of_gt (small a ha)) high
    · exact (not_le_of_gt (small b hb)) high)
  have total := card_sdiff_add_card_inter (univ : Finset V) p.support.toFinset
  rw [univ_inter,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at total
  change E.card + p.support.length = Fintype.card V at total
  have cap' (a : V) : G.distEven a ≤ G.secondSmallestDegree + 1 := by
    simpa only [Nat.add_comm] using cap a
  have minPoint (a : V) : 3 ≤ G.degree a := minimum.trans (G.minDegree_le_degree a)
  obtain ⟨z,low,a,b,P,hP⟩ := Graph189ExteriorDegreeCycle.near_longest_has_hamiltonian_low_deletion
    p hp longest (by omega) notTraceable k5 cap' minPoint
  have least : G.degree z = G.minDegree := by
    obtain ⟨w,hw⟩ := G.exists_minimal_degree_vertex
    by_cases eq : w = z
    · exact (congrArg G.degree eq).symm.trans hw.symm
    have high := (degree_pair (G:=G) w z eq).resolve_right (not_le_of_gt low)
    have minimal := G.minDegree_le_degree z
    omega
  exact notTraceable (traceable_of_hamiltonian_minimum_deletion_unrestricted hc z least
    (minPoint z) k5 cap' P hP)

/-- The omitted clique has Hamiltonian walks between prescribed distinct
endpoints. Its high vertices need at least floor(k/2) path contacts. -/
theorem ordinary_census [Nontrivial V] (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (k5 : 5 ≤ G.secondSmallestDegree)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (longest : Longest p)
    (clique : CliqueExterior p) :
    let E := univ \ p.support.toFinset
    ∃ A : Finset ℕ, A.card = G.secondSmallestDegree / 2 ∧
      (∀ v : E, contactPositions p v.val ⊆ A) ∧
      ∀ v : E, G.secondSmallestDegree ≤ G.degree v.val → contactPositions p v.val = A := by
  classical
  let E := univ \ p.support.toFinset
  let k := G.secondSmallestDegree
  let u := k / 2
  let H : Finset E := univ.filter fun v => k ≤ G.degree v.val
  let L : Finset E := univ.filter fun v => ¬ k ≤ G.degree v.val
  change E.card = (k+1)/2 + 1 ∧ _ at clique
  have size := clique.1
  have outside (a : V) (ha : a ∈ E) : a ∉ p.support :=
    fun on => (mem_sdiff.mp ha).2 (List.mem_toFinset.mpr on)
  have full : G.induce (E : Set V) = ⊤ := by
    ext a b
    change G.Adj a.val b.val ↔ a ≠ b
    constructor
    · exact fun edge same => edge.ne (congrArg Subtype.val same)
    · exact fun different => clique.2 a.val a.property b.val b.property
        (fun same => different (Subtype.ext same))
  have routes (a b : E) (ne : a ≠ b) :
      ∃ q : (G.induce (E : Set V)).Walk a b, q.IsHamiltonian := by
    rw [full]
    exact Graph189TerminalLeafClosure.complete_prescribed a b ne
  have leastTwo : 2 ≤ u := by dsimp [u,k]; omega
  have enoughSpace : u < E.card := by dsimp [u]; omega
  have lowCount : L.card ≤ 1 := card_le_one_iff.mpr (by
    intro a b ha hb
    by_contra different
    have diff : a.val ≠ b.val := fun e => different (Subtype.ext e)
    rcases degree_pair (G:=G) a.val b.val diff with high | high
    · exact (mem_filter.mp ha).2 high
    · exact (mem_filter.mp hb).2 high)
  have sideCount : H.card + L.card = E.card := by
    have eq := card_filter_add_card_filter_not (s:=(univ : Finset E))
      (p:=fun v => k ≤ G.degree v.val)
    rw [card_univ,Fintype.card_coe] at eq
    exact eq
  have many : u ≤ H.card := by dsimp [u]; omega
  have privateOverflow : 3 ≤ u ∨ u < H.card := by
    have hk : 5 ≤ k := k5
    dsimp [u]
    omega
  have rows (a : E) (ha : a ∈ H) : u ≤ (contactPositions p a.val).card := by
    have high := (mem_filter.mp ha).2
    have subset : G.neighborFinset a.val \ p.support.toFinset ⊆ E.erase a.val := by
      intro b hb
      obtain ⟨adj,off⟩ := mem_sdiff.mp hb
      exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp adj).ne.symm,
        mem_sdiff.mpr ⟨mem_univ _,off⟩⟩
    have bound := card_le_card subset
    rw [card_erase_of_mem a.property] at bound
    have split := card_sdiff_add_card_inter (G.neighborFinset a.val) p.support.toFinset
    rw [G.card_neighborFinset_eq_degree,←contact_card_neighbors p hp a.val] at split
    dsimp [u]
    omega
  have allCount := card_sdiff_add_card_inter (univ : Finset V) p.support.toFinset
  rw [univ_inter,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at allCount
  change E.card+p.support.length=Fintype.card V at allCount
  have maximum : (univ.image (distEven G)).max' (by simp) ≤ 1 + k := by
    apply max'_le
    rintro _ hi
    obtain ⟨z,_,rfl⟩ := mem_image.mp hi
    exact cap z
  have upper := Graph189OrderBound.order_le hc maximum
  change Fintype.card V ≤ 1 + G.minDegree + k + (k+1)^2/4 at upper
  obtain ⟨vertex,degree⟩ := Graph189QuadraticOrder.second_attained (G:=G)
  have minBound : G.minDegree ≤ k := (G.minDegree_le_degree vertex).trans_eq degree
  have pathRoom : p.support.length ≤ (u+1)*E.card+2*u := by
    have split := Nat.div_add_mod k 2
    have remain := Nat.mod_lt k (by decide : 0 < 2)
    have factor : k = 2*u + k%2 := by dsimp [u]; omega
    by_cases parity : k%2 = 0
    · have eq : k = 2*u := by omega
      have e : E.card = u+1 := by rw [eq] at size; omega
      have square : (k+1)^2/4 = u*(u+1) := by
        rw [eq,show (2*u+1)^2 = 4*(u*(u+1))+1 by ring]
        omega
      rw [square,eq] at upper
      rw [e] at allCount ⊢
      nlinarith
    · have eq : k = 2*u+1 := by omega
      have e : E.card = u+2 := by rw [eq] at size; omega
      have square : (k+1)^2/4 = (u+1)^2 := by
        rw [eq,show (2*u+1+1)^2 = 4*(u+1)^2 by ring]
        omega
      rw [square,eq] at upper
      rw [e] at allCount ⊢
      nlinarith
  obtain ⟨A,count,cover,uniform⟩ := Graph189ContactGroupCensus.uniform_of_ordinary_census
    p hp longest E outside routes H u leastTwo many enoughSpace privateOverflow rows pathRoom
  refine ⟨A,count,cover,?_⟩
  intro v high
  exact uniform v (mem_filter.mpr ⟨mem_univ _,high⟩)

/-- The ordinary contact census needs uniformity only among high omitted
vertices, since the exceptional low vertex need neither use all marks nor
remain outside after a swap. -/
def UniformHighContacts (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ {x y : V}, ∀ p : G.Walk x y, p.IsPath → Longest p → Near p →
    CliqueExterior p →
    ∀ a, a ∉ p.support → G.secondSmallestDegree ≤ G.degree a →
    ∀ b, b ∉ p.support → G.secondSmallestDegree ≤ G.degree b →
    ∀ w ∈ p.support, G.Adj w a → G.Adj w b

theorem uniform_high_contacts [Nontrivial V] (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (k5 : 5 ≤ G.secondSmallestDegree) : UniformHighContacts G := by
  classical
  intro x y p hp longest _ clique a ha ah b hb bh w hw wa
  let E := univ \ p.support.toFinset
  have member (v : V) (hv : v ∉ p.support) : v ∈ E :=
    mem_sdiff.mpr ⟨mem_univ _,fun h => hv (List.mem_toFinset.mp h)⟩
  let first : E := ⟨a,member a ha⟩
  let second : E := ⟨b,member b hb⟩
  obtain ⟨A,_,_,rows⟩ := ordinary_census hc cap k5 p hp longest clique
  obtain ⟨i,valid,why⟩ := List.mem_iff_getElem.mp hw
  have atPos := (get_at p valid).symm.trans why
  have hit : i ∈ contactPositions p first.val :=
    (mem_contactPositions p _ i).mpr ⟨valid,by simpa [first,atPos] using wa⟩
  rw [rows first ah,← rows second bh] at hit
  have real := (mem_contactPositions p _ i).mp hit
  simpa [second,atPos] using real.2

/-- A full unmarked interval avoiding the low vertex, with the old mark
shifts outside that interval.  The interval will supply the additional
even-distance vertices after swapping in the exterior Hamiltonian path. -/
structure Exchange {x y : V} (p : G.Walk x y) where
  exterior : Finset V
  outside : ∀ v ∈ exterior, v ∉ p.support
  first : exterior
  last : exterior
  distinct : first ≠ last
  firstHigh : G.secondSmallestDegree ≤ G.degree first.val
  lastHigh : G.secondSmallestDegree ≤ G.degree last.val
  routes : ∀ a b : exterior, a ≠ b →
    ∃ q : (G.induce (exterior : Set V)).Walk a b, q.IsHamiltonian
  gap : TightGap p first.val exterior.card
  highGap : ∀ v ∈ gap.block, G.secondSmallestDegree ≤ G.degree v
  shifts : Finset V
  disjointShifts : Disjoint gap.block.toFinset shifts
  evenShifts : ∀ v ∈ shifts, G.dist first.val v = 2
  enough : G.secondSmallestDegree < exterior.card + shifts.card

def HasFullGap (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ {x y : V}, ∀ p : G.Walk x y, p.IsPath → Longest p → Near p →
    CliqueExterior p → Nonempty (Exchange p)

/-- The exact bridge from the matched separator paths to traceability.  The
remaining geometric inputs are the ordinary uniform census and the choice
of one full interval with enough old shifts outside it. -/
theorem traceable_of_near_path [Nontrivial V] (hc : G.Connected) (fullGap : HasFullGap G)
    (k5 : 5 ≤ G.secondSmallestDegree) (minimum : 3 ≤ G.minDegree)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (near : Near p) :
    ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  have uniform : UniformHighContacts G := @uniform_high_contacts _ _ _ _ _ _ hc cap k5
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
  obtain ⟨data⟩ := fullGap P hP longestP nearP cliqueP
  let g := data.gap
  obtain ⟨root,rootBoundary,fromFirst,i,hi,edge⟩ := g.boundary
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
  have old {v : V} (on : v ∈ P.support) (adj : G.Adj v data.first.val) :
      G.Adj v data.last.val :=
    uniform P hP longestP nearP cliqueP
      data.first.val (data.outside _ data.first.property) data.firstHigh
      data.last.val (data.outside _ data.last.property) data.lastHigh v on adj
  obtain ⟨u,v,Q,hQ,_,lengthQ,omits,stays⟩ := full_exterior_splice P hP root rootOn
    data.exterior data.exterior.card rfl data.outside data.first data.last data.distinct
    data.routes (fun _ on adj => old on adj) g.left g.block g.right g.split rootOutside g.before g.after
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
  have hits (w : V) (hw : w ∈ g.block) : G.dist data.first.val w = 2 := by
    have on : w ∈ P.support := by rw [g.split]; simp [hw]
    have diff : data.first.val ≠ w := fun e =>
      data.outside _ data.first.property (by simpa [e] using on)
    have toW := uniform Q hQ longestQ nearQ (clique Q hQ longestQ nearQ)
      i (omits _ hi) (data.highGap _ hi) w (omits _ hw) (data.highGap _ hw)
      root (stays _ rootBoundary) edge
    exact two_step_metric diff (g.unmarked w hw) fromFirst toW.symm
  let W := g.block.toFinset ∪ data.shifts
  have Wcard : W.card = data.exterior.card + data.shifts.card := by
    rw [show W = g.block.toFinset ∪ data.shifts from rfl,card_union_of_disjoint data.disjointShifts,
      List.toFinset_card_of_nodup nd.of_append_left.of_append_right,g.size]
  have even (w : V) (hw : w ∈ W) : G.dist data.first.val w = 2 := by
    rcases mem_union.mp hw with h | h
    · exact hits w (List.mem_toFinset.mp h)
    · exact data.evenShifts w h
  have absent : data.first.val ∉ W := by
    intro h
    have e := even _ h
    simp at e
  have includeEven : insert data.first.val W ⊆ univ.filter (fun w => Even (G.dist data.first.val w)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl | h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [even _ h]; decide⟩
  have count := card_le_card includeEven
  rw [card_insert_of_notMem absent,Wcard] at count
  change data.exterior.card + data.shifts.card + 1 ≤ G.distEven data.first.val at count
  have bound := cap data.first.val
  have more := data.enough
  omega

end Graph189OrdinaryPathGap
