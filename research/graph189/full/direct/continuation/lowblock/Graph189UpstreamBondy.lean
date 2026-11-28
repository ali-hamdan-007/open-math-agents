import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.List.GetD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/- The proof below is the accepted official solution by @koolkao, from
GuillaumeBAUD-coder/open-math-agents PR 7971 at
4ba96e4e630444f2b94fdffc7c26f3e831e11c79. We import its graph definitions
directly and use a local name for the exterior so the file contains no
placeholder-bearing conjecture import. Its mathematical proof is unchanged.
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7971 -/
/-!
Bondy's conjecture for `n ≥ 5k² + 7k` (Ma–Ning–Zhao, arXiv:2606.03696, Theorem 1.1).

Original formal proof; it does not follow the paper's route through average-degree Bondy–Jackson
and Fan's attachment lemmas. Let `C` be a longest cycle, `H` a component of `G - C` holding a path
with `k` vertices, and `Q` a longest path of `H` with `p` vertices. Then `δ ≥ 6k`.

* (L20) For pairwise disjoint pendant paths `R i` off `Q` ending at `u i`,
  `|C| ≥ e(U, C) + |N_C(U)|` (the counting claim (20) of Ma–Ning–Zhao, with their Lemma 3.1).
* Residual lemma: a family `R` chosen lexicographically maximal has
  `Σ d_H(u i) ≤ p·min(p - 1, 2L - 2)` when every cycle of `H` has at most `L` vertices (replaces the
  paper's DFS-tree lemma). With (L20) this rules out `p ≤ 5k + 1`, and `p ≥ 5k + 2` when `H` has
  no cycle with `2k - 2` vertices.
* Linked sets: if `H` has a cycle with at least `2k - 2` (and `k + 1`) vertices, Menger's theorem
  (proved here, Göring's edge-deletion proof) gives `k + 1` disjoint paths to `C`, or `k` paths and
  a separator of size `k`. A shifted-successor degree count (generalising our `k = 3` proof)
  contradicts `(k + 1) δ ≥ n + k (k - 1)` in both cases.
* `k = 1` (Dirac) follows from the same successor counts.
-/


namespace OMA.BondyK

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A sub-list in the middle of a chain is a chain. -/
lemma chain_sub {R : V → V → Prop} {l l₁ : List V} (h : l.IsChain R) (hs : l₁ <:+: l) :
    l₁.IsChain R := by
  obtain ⟨s, t, rfl⟩ := hs
  exact (List.isChain_append.mp (List.isChain_append.mp h).1).2.1

/-- An initial segment of a chain is a chain. -/
lemma chain_pre {R : V → V → Prop} {l l₁ : List V} (h : l.IsChain R) (hs : l₁ <+: l) :
    l₁.IsChain R := by
  obtain ⟨t, rfl⟩ := hs
  exact (List.isChain_append.mp h).1

/-! ## Menger's theorem -/

/-- `l` is a path list from `A` to `B`: nodup, consecutive entries adjacent, head in `A`, last in `B`. -/
def ABP (G : SimpleGraph V) (A B : Finset V) (l : List V) : Prop :=
  l.Nodup ∧ l.IsChain G.Adj ∧ (∃ a ∈ A, l.head? = some a) ∧ (∃ b ∈ B, l.getLast? = some b)

/-! ## Auxiliary notions and list lemmas -/

/-- `S` meets every `A`–`B` path list of `G`. -/
def Sep (G : SimpleGraph V) (A B S : Finset V) : Prop :=
  ∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S

lemma getLast?_app_cons (p q : List V) (y : V) :
    (p ++ y :: q).getLast? = (y :: q).getLast? := by
  rw [List.getLast?_append, List.getLast?_cons]; rfl

/-- Loop erasure: a chain contains a nodup chain with the same ends. -/
lemma erase_loops {R : V → V → Prop} : ∀ l : List V, l.IsChain R →
    ∃ l' : List V, l'.Nodup ∧ l'.IsChain R ∧ l'.head? = l.head? ∧
      l'.getLast? = l.getLast? ∧ ∀ z ∈ l', z ∈ l
  | [], _ => ⟨[], List.nodup_nil, List.isChain_nil, rfl, rfl, fun _ h => h⟩
  | z :: t, h => by
    obtain ⟨t', hnd, hch, hhd, hlast, hsub⟩ := erase_loops t (List.isChain_cons.mp h).2
    by_cases hz : z ∈ t'
    · obtain ⟨u, w, rfl⟩ := List.append_of_mem hz
      have ht : t ≠ [] := by
        rintro rfl; exact absurd (hsub z (by simp)) (by simp)
      obtain ⟨c, hc⟩ : ∃ c, t.getLast? = some c := by
        cases h' : t.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h') ht
        | some c => exact ⟨c, rfl⟩
      refine ⟨z :: w, hnd.sublist (List.sublist_append_right u _), hch.right_of_append, rfl,
        ?_, ?_⟩
      · rw [getLast?_app_cons] at hlast
        rw [hlast, hc, List.getLast?_cons, hc]; rfl
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub a (by simp [ha]))
    · refine ⟨z :: t', List.nodup_cons.mpr ⟨hz, hnd⟩,
        hch.cons (fun y hy => (List.isChain_cons.mp h).1 y (by rw [← hhd]; exact hy)), rfl,
        by rw [List.getLast?_cons, List.getLast?_cons, hlast], ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub a ha)

lemma sep_chain {A B S : Finset V} (hS : Sep G A B S) {l : List V}
    (hch : l.IsChain G.Adj) (hA : ∃ a ∈ A, l.head? = some a)
    (hB : ∃ b ∈ B, l.getLast? = some b) : ∃ z ∈ l, z ∈ S := by
  obtain ⟨l', hnd, hch', hhd, hlast, hsub⟩ := erase_loops l hch
  obtain ⟨z, hz, hzS⟩ := hS l' ⟨hnd, hch', by rw [hhd]; exact hA, by rw [hlast]; exact hB⟩
  exact ⟨z, hsub z hz, hzS⟩

lemma abp_mono {H : SimpleGraph V} (hle : H ≤ G) {A B : Finset V} {l : List V}
    (h : ABP H A B l) : ABP G A B l :=
  ⟨h.1, h.2.1.imp (fun _ _ h => hle h), h.2.2⟩

lemma abp_reverse {A B : Finset V} {l : List V} (h : ABP G A B l) : ABP G B A l.reverse := by
  obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := h
  exact ⟨List.nodup_reverse.mpr hnd, List.isChain_reverse.mpr (hch.imp fun _ _ h => h.symm),
    ⟨b, hb, by simpa using hlb⟩, ⟨a, ha, by simpa using hha⟩⟩

lemma sep_reverse {A B S : Finset V} (h : Sep G A B S) : Sep G B A S := fun l hl => by
  obtain ⟨z, hz, hzS⟩ := h l.reverse (abp_reverse hl)
  exact ⟨z, List.mem_reverse.mp hz, hzS⟩

lemma exists_bad {R R' : V → V → Prop} : ∀ l : List V, l.IsChain R → ¬ l.IsChain R' →
    ∃ p u v q, l = p ++ u :: v :: q ∧ R u v ∧ ¬ R' u v
  | [], _, h' => absurd List.isChain_nil h'
  | [a], _, h' => absurd (List.isChain_singleton a) h'
  | a :: b :: t, h, h' => by
    rw [List.isChain_cons_cons] at h
    by_cases hab : R' a b
    · have : ¬ (b :: t).IsChain R' := fun hc => h' (List.isChain_cons_cons.mpr ⟨hab, hc⟩)
      obtain ⟨p, u, v, q, hl, h1, h2⟩ := exists_bad (b :: t) h.2 this
      exact ⟨a :: p, u, v, q, by rw [hl]; rfl, h1, h2⟩
    · exact ⟨[], a, b, t, rfl, h.1, hab⟩

lemma chain_del {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {l : List V} (hl : l.IsChain G.Adj) (hy : y ∉ l ∨ x ∉ l) : l.IsChain H.Adj :=
  hl.imp_of_mem_imp fun u v hu hv huv => (hH u v).mpr ⟨huv, fun he => by
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> tauto⟩

lemma nodup_aux {p q : List V} {a b : V} (h : (p ++ a :: b :: q).Nodup) : b ∉ p ++ [a] := by
  intro hb
  rw [List.nodup_append] at h
  rcases List.mem_append.mp hb with hb | hb
  · exact h.2.2 b hb b (by simp) rfl
  · have := List.nodup_cons.mp h.2.1
    simp at hb; subst hb; exact this.1 (by simp)

lemma nodup_aux2 {p q : List V} {a b : V} (h : (p ++ a :: b :: q).Nodup) : a ∉ b :: q :=
  (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1

lemma abp_of_prefix {A B : Finset V} {m l : List V} (hp : m <+: l) (hnd : l.Nodup)
    (hA : ∃ a ∈ A, l.head? = some a) (hch : m.IsChain G.Adj)
    (hB : ∃ b ∈ B, m.getLast? = some b) : ABP G A B m := by
  refine ⟨hnd.sublist hp.sublist, hch, ?_, hB⟩
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨b, -, hb⟩ := hB
  obtain ⟨a, ha, hha⟩ := hA
  cases m with
  | nil => simp at hb
  | cons c m => exact ⟨a, ha, by simpa using hha⟩

lemma sep_last {A X : Finset V} : Sep G A X X := fun l hl => by
  obtain ⟨b, hb, hlb⟩ := hl.2.2.2
  exact ⟨b, List.mem_of_getLast? hlb, hb⟩

lemma sep_of_pre {H : SimpleGraph V} {A B X T : Finset V}
    (hpre : ∀ l, ABP G A B l → ∃ m, m <+: l ∧ ABP H A X m) (hT : Sep H A X T) :
    Sep G A B T := fun l hl => by
  obtain ⟨m, hm, hmX⟩ := hpre l hl
  obtain ⟨z, hz, hzT⟩ := hT m hmX
  exact ⟨z, hm.subset hz, hzT⟩

lemma sep_of_suf {H : SimpleGraph V} {A B Y T : Finset V}
    (hsuf : ∀ l, ABP G A B l → ∃ m, m <:+ l ∧ ABP H Y B m) (hT : Sep H Y B T) :
    Sep G A B T := fun l hl => by
  obtain ⟨m, hm, hmX⟩ := hsuf l hl
  obtain ⟨z, hz, hzT⟩ := hT m hmX
  exact ⟨z, hm.subset hz, hzT⟩

/-! ## Trimming -/

lemma exists_first (P : V → Prop) : ∀ l : List V, (∃ z ∈ l, P z) →
    ∃ l1 z l2, l = l1 ++ z :: l2 ∧ P z ∧ ∀ w ∈ l1, ¬ P w
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ha : P a
    · exact ⟨[], a, t, rfl, ha, by simp⟩
    · obtain ⟨z, hz, hPz⟩ := h
      have : ∃ z ∈ t, P z := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hPz ha
        · exact ⟨z, hz, hPz⟩
      obtain ⟨l1, z', l2, rfl, h1, h2⟩ := exists_first P t this
      exact ⟨a :: l1, z', l2, rfl, h1, by simp [ha]; exact h2⟩

lemma exists_last (P : V → Prop) (l : List V) (h : ∃ z ∈ l, P z) :
    ∃ l1 z l2, l = l1 ++ z :: l2 ∧ P z ∧ ∀ w ∈ l2, ¬ P w := by
  obtain ⟨l1, z, l2, hl, h1, h2⟩ := exists_first P l.reverse (by simpa using h)
  refine ⟨l2.reverse, z, l1.reverse, ?_, h1, by simpa using h2⟩
  rw [← List.reverse_reverse l, hl]; simp

lemma trim {A B : Finset V} {l : List V} (hl : ABP G A B l) :
    ∃ l', ABP G A B l' ∧ (∀ x ∈ l'.tail, x ∉ A) ∧ (∀ x ∈ l'.dropLast, x ∉ B) ∧
      ∀ x ∈ l', x ∈ l := by
  obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := hl
  obtain ⟨l1, b', l2, rfl, hb', hl1⟩ :=
    exists_first (· ∈ B) l ⟨b, List.mem_of_getLast? hlb, hb⟩
  have hmA : ∃ z ∈ l1 ++ [b'], z ∈ A := by
    refine ⟨a, ?_, ha⟩
    rcases l1 with _ | ⟨c, l1'⟩
    · simp at hha; simp [hha]
    · simp at hha; simp [hha]
  obtain ⟨m1, a', m2, hm, ha', hm2⟩ := exists_last (· ∈ A) (l1 ++ [b']) hmA
  have hL : l1 ++ b' :: l2 = m1 ++ (a' :: m2) ++ l2 := by
    rw [← hm]; simp
  have hinf : a' :: m2 <:+: l1 ++ b' :: l2 := ⟨m1, l2, hL.symm⟩
  refine ⟨a' :: m2, ⟨hnd.sublist hinf.sublist, chain_sub hch hinf, ⟨a', ha', rfl⟩,
    ⟨b', hb', ?_⟩⟩, hm2, ?_, fun z hz => hinf.subset hz⟩
  · rw [← getLast?_app_cons m1, ← hm]; simp
  · have : l1 = m1 ++ (a' :: m2).dropLast := by
      rw [← List.dropLast_append_cons, ← hm, List.dropLast_concat]
    intro z hz
    exact hl1 z (by rw [this]; exact List.mem_append_right _ hz)

lemma trim_family {A B : Finset V} {k : ℕ} {P : Fin k → List V} (hP : ∀ i, ABP G A B (P i))
    (hd : ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j) :
    ∃ P' : Fin k → List V, (∀ i, ABP G A B (P' i) ∧ (∀ x ∈ (P' i).tail, x ∉ A) ∧
        (∀ x ∈ (P' i).dropLast, x ∉ B)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P' i, x ∉ P' j := by
  choose P' h1 h2 h3 h4 using fun i => trim (hP i)
  exact ⟨P', fun i => ⟨h1 i, h2 i, h3 i⟩,
    fun i j hij x hx hx' => hd i j hij x (h4 i x hx) (h4 j x hx')⟩

/-! ## The edgeless case -/

lemma base {A B : Finset V} {k : ℕ} (hE : ∀ u v, ¬ G.Adj u v)
    (hsep : ∀ S, Sep G A B S → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  have hk : k ≤ (A ∩ B).card := hsep _ (fun l hl => by
    obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := hl
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hha
    cases t with
    | nil =>
      simp at hlb
      exact ⟨a, by simp, Finset.mem_inter.mpr ⟨ha, by rw [hlb]; exact hb⟩⟩
    | cons c t => exact absurd (List.isChain_cons_cons.mp hch).1 (hE a c))
  let e := (A ∩ B).equivFin.symm
  refine ⟨fun i => [(e (Fin.castLE hk i)).1], fun i => ⟨List.nodup_singleton _,
    List.isChain_singleton _, ⟨_, (Finset.mem_inter.mp (e _).2).1, rfl⟩,
    ⟨_, (Finset.mem_inter.mp (e _).2).2, rfl⟩⟩, ?_⟩
  intro i j hij x hx hx'
  simp only [List.mem_singleton] at hx hx'
  exact hij (Fin.castLE_injective hk (e.injective (Subtype.ext (hx.symm.trans hx'))))

/-! ## Prefix and suffix lemmas for the induction step -/

lemma pre {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {A B S : Finset V} (hSH : Sep H A B S) {q : List V} (hq : (y :: q).IsChain H.Adj)
    (hqB : ∃ b ∈ B, (y :: q).getLast? = some b) (hqS : ∀ z ∈ y :: q, z ∉ S)
    {l : List V} (hl : ABP G A B l) : ∃ m, m <+: l ∧ ABP H A (insert x S) m := by
  obtain ⟨hnd, hch, hA, hB⟩ := hl
  have key : ∀ l1, l1 <+: l → l1.IsChain H.Adj → (∃ z ∈ l1, z ∈ S) →
      ∃ m, m <+: l ∧ ABP H A (insert x S) m := by
    rintro l1 hp hc ⟨z, hz, hzS⟩
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hz
    have hp' : s ++ [z] <+: s ++ z :: t := ⟨t, by simp⟩
    exact ⟨s ++ [z], hp'.trans hp, abp_of_prefix (hp'.trans hp) hnd hA (chain_pre hc hp')
      ⟨z, Finset.mem_insert_of_mem hzS, by simp⟩⟩
  by_cases hl : l.IsChain H.Adj
  · exact key l (List.prefix_refl l) hl (sep_chain hSH hl hA hB)
  · obtain ⟨p, u, v, q', rfl, huv, hnuv⟩ := exists_bad l hch hl
    have he : s(u, v) = s(x, y) := by
      by_contra hne; exact hnuv ((hH u v).mpr ⟨huv, hne⟩)
    have hp : p ++ [u] <+: p ++ u :: v :: q' := ⟨v :: q', by simp⟩
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      exact ⟨p ++ [u], hp, abp_of_prefix hp hnd hA
        (chain_del hH (chain_pre hch hp) (Or.inl (nodup_aux hnd)))
        ⟨u, Finset.mem_insert_self _ _, by simp⟩⟩
    · subst h1 h2
      have hc : (p ++ [u]).IsChain H.Adj :=
        chain_del hH (chain_pre hch hp) (Or.inr (nodup_aux hnd))
      by_cases hm : ∃ z ∈ p ++ [u], z ∈ S
      · exact key _ hp hc hm
      · exfalso
        push_neg at hm
        obtain ⟨z, hz, hzS⟩ := sep_chain hSH (l := p ++ u :: q)
          (List.isChain_split.mpr ⟨hc, hq⟩) (by simpa using hA)
          (by rw [getLast?_app_cons]; exact hqB)
        rcases List.mem_append.mp hz with hz | hz
        · exact hm z (List.mem_append_left _ hz) hzS
        · exact hqS z hz hzS

lemma suf {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {A B S : Finset V} (hSH : Sep H A B S) {p : List V} (hp : (p ++ [x]).IsChain H.Adj)
    (hpA : ∃ a ∈ A, (p ++ [x]).head? = some a) (hpS : ∀ z ∈ p ++ [x], z ∉ S)
    {l : List V} (hl : ABP G A B l) : ∃ m, m <:+ l ∧ ABP H (insert y S) B m := by
  have hH' : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(y, x) := by
    intro u v; rw [Sym2.eq_swap (a := y)]; exact hH u v
  have e : x :: p.reverse = (p ++ [x]).reverse := by simp
  obtain ⟨m, hm, hmA⟩ := pre (x := y) (y := x) (q := p.reverse) hH' (sep_reverse hSH)
    (by rw [e]; exact List.isChain_reverse.mpr (hp.imp fun _ _ h => h.symm))
    (by rw [e, List.getLast?_reverse]; exact hpA)
    (fun z hz => hpS z (by rw [e] at hz; simp at hz ⊢; tauto)) (abp_reverse hl)
  exact ⟨m.reverse, List.reverse_prefix.mp (by simpa using hm), by simpa using abp_reverse hmA⟩

/-! ## Gluing -/

lemma mem_tail_of {c d : List V} {v z : V} (hz : z ∈ d) : z ∈ (c ++ v :: d).tail := by
  cases c <;> simp [hz]

lemma glue {H : SimpleGraph V} (hle : H ≤ G) {x y : V} (hxy : G.Adj x y) {A B S : Finset V}
    (hx : x ∉ S) (hy : y ∉ S) (hSH : Sep H A B S) {k : ℕ} (hk : S.card + 1 = k)
    {P Q : Fin k → List V}
    (hP : ∀ i, ABP H A (insert x S) (P i) ∧ ∀ z ∈ (P i).dropLast, z ∉ insert x S)
    (hPd : ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j)
    (hQ : ∀ j, ABP H (insert y S) B (Q j) ∧ ∀ z ∈ (Q j).tail, z ∉ insert y S)
    (hQd : ∀ i j, i ≠ j → ∀ z ∈ Q i, z ∉ Q j) :
    ∃ R : Fin k → List V, (∀ i, ABP G A B (R i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ R i, z ∉ R j := by
  have hxy' : x ≠ y := G.ne_of_adj hxy
  choose lt hltX hlt using fun i => (hP i).1.2.2.2
  choose hd hhdY hhd using fun j => (hQ j).1.2.2.1
  have hPdec : ∀ i, ∃ a, P i = a ++ [lt i] := fun i => List.getLast?_eq_some_iff.mp (hlt i)
  have hQdec : ∀ j, ∃ d, Q j = hd j :: d := fun j => List.head?_eq_some_iff.mp (hhd j)
  have hltmem : ∀ i, lt i ∈ P i := fun i => List.mem_of_getLast? (hlt i)
  have hhdmem : ∀ j, hd j ∈ Q j := fun j => List.mem_of_head? (hhd j)
  have hPS : ∀ i, ∀ z ∈ P i, z ∈ S → z = lt i := by
    intro i z hz hzS
    obtain ⟨a, ha⟩ := hPdec i
    rw [ha] at hz
    rcases List.mem_append.mp hz with h | h
    · exact absurd (Finset.mem_insert_of_mem hzS)
        ((hP i).2 z (by rw [ha, List.dropLast_concat]; exact h))
    · simpa using h
  have hQS : ∀ j, ∀ z ∈ Q j, z ∈ S → z = hd j := by
    intro j z hz hzS
    obtain ⟨d, hd'⟩ := hQdec j
    rw [hd'] at hz
    rcases List.mem_cons.mp hz with h | h
    · exact h
    · exact absurd (Finset.mem_insert_of_mem hzS) ((hQ j).2 z (by rw [hd']; exact h))
  have meet : ∀ i j, ∀ v ∈ P i, v ∈ Q j → v ∈ S := by
    intro i j v hvP hvQ
    by_contra hvS
    obtain ⟨a, b, hab⟩ := List.append_of_mem hvP
    obtain ⟨c, d, hcd⟩ := List.append_of_mem hvQ
    have h1 : (a ++ [v]).IsChain H.Adj := chain_pre (hP i).1.2.1 ⟨b, by rw [hab]; simp⟩
    have h2 : (v :: d).IsChain H.Adj := (hQ j).1.2.1.suffix ⟨c, hcd.symm⟩
    obtain ⟨a0, ha0, hha0⟩ := (hP i).1.2.2.1
    obtain ⟨b0, hb0, hlb0⟩ := (hQ j).1.2.2.2
    obtain ⟨z, hz, hzS⟩ := sep_chain hSH (List.isChain_split.mpr ⟨h1, h2⟩)
      ⟨a0, ha0, by rw [hab] at hha0; simpa using hha0⟩
      ⟨b0, hb0, by rw [hcd, getLast?_app_cons] at hlb0; rw [getLast?_app_cons]; exact hlb0⟩
    rcases List.mem_append.mp hz with hz | hz
    · exact (hP i).2 z (by rw [hab, List.dropLast_append_cons]; exact List.mem_append_left _ hz)
        (Finset.mem_insert_of_mem hzS)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hvS hzS
      · exact (hQ j).2 z (by rw [hcd]; exact mem_tail_of hz) (Finset.mem_insert_of_mem hzS)
  have hdinj : Function.Injective hd := by
    intro j j' h
    by_contra hne
    exact hQd j j' hne (hd j) (hhdmem j) (h ▸ hhdmem j')
  have hY : (insert y S).card = k := by rw [Finset.card_insert_of_notMem hy, hk]
  have hsurj : ∀ w ∈ insert y S, ∃ j, hd j = w := by
    have himg : Finset.univ.image hd = insert y S := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
        exact hhdY j
      · rw [Finset.card_image_of_injective _ hdinj, Finset.card_univ, Fintype.card_fin, hY]
    intro w hw
    rw [← himg] at hw
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hw
    exact ⟨j, hj⟩
  obtain ⟨f, hf⟩ : ∃ f : V → V, f = fun v => if v = x then y else v := ⟨_, rfl⟩
  have hfx : f x = y := by simp [hf]
  have hfS : ∀ v, v ≠ x → f v = v := by intro v hv; simp [hf, hv]
  have hltS : ∀ i, lt i ≠ x → lt i ∈ S := fun i h =>
    (Finset.mem_insert.mp (hltX i)).resolve_left h
  have hfY : ∀ i, f (lt i) ∈ insert y S := by
    intro i
    by_cases h : lt i = x
    · rw [h, hfx]; exact Finset.mem_insert_self _ _
    · rw [hfS _ h]; exact Finset.mem_insert_of_mem (hltS i h)
  choose σ hσ using fun i => hsurj _ (hfY i)
  have hσinj : Function.Injective σ := by
    intro i i' h
    have h1 : f (lt i) = f (lt i') := by rw [← hσ i, ← hσ i', h]
    have h2 : lt i = lt i' := by
      by_cases ha : lt i = x <;> by_cases hb : lt i' = x
      · rw [ha, hb]
      · rw [ha, hfx, hfS _ hb] at h1; exact absurd (h1 ▸ hltS i' hb) hy
      · rw [hb, hfx, hfS _ ha] at h1; exact absurd (h1.symm ▸ hltS i ha) hy
      · rwa [hfS _ ha, hfS _ hb] at h1
    by_contra hne
    exact hPd i i' hne _ (hltmem i) (h2 ▸ hltmem i')
  obtain ⟨R, hR⟩ : ∃ R : Fin k → List V, R = fun i =>
      if lt i = x then P i ++ Q (σ i) else P i ++ (Q (σ i)).tail := ⟨_, rfl⟩
  have memR : ∀ i z, z ∈ R i → z ∈ P i ∨ z ∈ Q (σ i) := by
    intro i z hz
    rw [hR] at hz
    simp only at hz
    split_ifs at hz
    · exact List.mem_append.mp hz
    · rcases List.mem_append.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_tail h)
  have hRabp : ∀ i, ABP G A B (R i) := by
    intro i
    obtain ⟨a, ha⟩ := hPdec i
    obtain ⟨d, hd'⟩ := hQdec (σ i)
    have hPch : (P i).IsChain G.Adj := (hP i).1.2.1.imp fun _ _ h => hle h
    have hQch : (Q (σ i)).IsChain G.Adj := (hQ (σ i)).1.2.1.imp fun _ _ h => hle h
    have hPnd := (hP i).1.1
    have hQnd := (hQ (σ i)).1.1
    obtain ⟨a0, ha0, hha0⟩ := (hP i).1.2.2.1
    obtain ⟨b0, hb0, hlb0⟩ := (hQ (σ i)).1.2.2.2
    rw [ha] at hPch hPnd hha0
    rw [hd'] at hQch hQnd hlb0
    by_cases hx' : lt i = x
    · have hdy : hd (σ i) = y := by rw [hσ i, hx', hfx]
      have hRi : R i = a ++ [lt i] ++ hd (σ i) :: d := by
        rw [hR]; simp only [if_pos hx']; rw [ha, hd']
      rw [hRi]
      refine ⟨?_, ?_, ⟨a0, ha0, by simpa using hha0⟩,
        ⟨b0, hb0, by rw [getLast?_app_cons]; exact hlb0⟩⟩
      · rw [List.nodup_append]
        refine ⟨hPnd, hQnd, ?_⟩
        rintro z hz z' hz' rfl
        have hzS := meet i (σ i) z (by rw [ha]; exact hz) (by rw [hd']; exact hz')
        have := hPS i z (by rw [ha]; exact hz) hzS
        exact hx (by rw [← hx', ← this]; exact hzS)
      · refine hPch.append hQch ?_
        intro u hu w hw
        simp at hu hw
        rw [← hu, ← hw, hx', hdy]; exact hxy
    · have hdl : hd (σ i) = lt i := by rw [hσ i, hfS _ hx']
      have hRi : R i = a ++ lt i :: d := by
        rw [hR]; simp only [if_neg hx']; rw [ha, hd', hdl]; simp
      rw [hdl] at hQch hQnd hlb0
      rw [hRi]
      refine ⟨?_, List.isChain_split.mpr ⟨hPch, hQch⟩, ⟨a0, ha0, by simpa using hha0⟩,
        ⟨b0, hb0, by rw [getLast?_app_cons]; exact hlb0⟩⟩
      have e : a ++ lt i :: d = (a ++ [lt i]) ++ d := by simp
      rw [e, List.nodup_append]
      refine ⟨hPnd, (List.nodup_cons.mp hQnd).2, ?_⟩
      rintro z hz z' hz' rfl
      have hzQ : z ∈ Q (σ i) := by rw [hd', hdl]; exact List.mem_cons_of_mem _ hz'
      have hzS := meet i (σ i) z (by rw [ha]; exact hz) hzQ
      have := hQS (σ i) z hzQ hzS
      rw [hdl] at this
      exact (List.nodup_cons.mp hQnd).1 (this ▸ hz')
  refine ⟨R, hRabp, ?_⟩
  have cross : ∀ i i', i ≠ i' → ∀ z ∈ P i, z ∉ Q (σ i') := by
    intro i i' hii' z h1 h2
    have hzS := meet i (σ i') z h1 h2
    have e1 := hPS i z h1 hzS
    have e2 := hQS (σ i') z h2 hzS
    have hne : lt i ≠ x := fun h => hx (by rw [← h, ← e1]; exact hzS)
    have : hd (σ i) = hd (σ i') := by rw [hσ i, hfS _ hne, ← e1, e2]
    exact hii' (hσinj (hdinj this))
  intro i i' hii' z hz hz'
  rcases memR i z hz with h1 | h1 <;> rcases memR i' z hz' with h2 | h2
  · exact hPd i i' hii' z h1 h2
  · exact cross i i' hii' z h1 h2
  · exact cross i' i (Ne.symm hii') z h2 h1
  · exact hQd (σ i) (σ i') (fun h => hii' (hσinj h)) z h1 h2

/-! ## The induction step -/

lemma step {H : SimpleGraph V} {x y : V} (hle : H ≤ G) (hxy : G.Adj x y)
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    (ih : ∀ (A B : Finset V) (k : ℕ), (∀ S, Sep H A B S → k ≤ S.card) →
      ∃ P : Fin k → List V, (∀ i, ABP H A B (P i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j)
    {A B : Finset V} {k : ℕ} (hsep : ∀ S, Sep G A B S → k ≤ S.card)
    {S : Finset V} (hSH : Sep H A B S) (hSk : S.card < k)
    {p q : List V} (hl0 : ABP G A B (p ++ x :: y :: q)) (hav : ∀ z ∈ p ++ x :: y :: q, z ∉ S) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j := by
  obtain ⟨hnd, hch, hA, hB⟩ := hl0
  have hx : x ∉ S := hav x (by simp)
  have hy : y ∉ S := hav y (by simp)
  have hp : p ++ [x] <+: p ++ x :: y :: q := ⟨y :: q, by simp⟩
  have hs : y :: q <:+ p ++ x :: y :: q := ⟨p ++ [x], by simp⟩
  have hpch : (p ++ [x]).IsChain H.Adj :=
    chain_del hH (chain_pre hch hp) (Or.inl (nodup_aux hnd))
  have hqch : (y :: q).IsChain H.Adj :=
    chain_del hH (hch.suffix hs) (Or.inr (nodup_aux2 hnd))
  have hpre : ∀ l, ABP G A B l → ∃ m, m <+: l ∧ ABP H A (insert x S) m := fun l hl =>
    pre hH hSH hqch (by rw [← getLast?_app_cons p]; simpa using hB)
      (fun z hz => hav z (by simp at hz ⊢; tauto)) hl
  have hsuf : ∀ l, ABP G A B l → ∃ m, m <:+ l ∧ ABP H (insert y S) B m := fun l hl =>
    suf hH hSH hpch (by simpa using hA) (fun z hz => hav z (by simp at hz ⊢; tauto)) hl
  have hXk : k ≤ (insert x S).card := hsep _ (sep_of_pre hpre sep_last)
  have hk : S.card + 1 = k := by rw [Finset.card_insert_of_notMem hx] at hXk; omega
  obtain ⟨P, hP, hPd⟩ := ih A (insert x S) k (fun T hT => hsep T (sep_of_pre hpre hT))
  obtain ⟨Q, hQ, hQd⟩ := ih (insert y S) B k (fun T hT => hsep T (sep_of_suf hsuf hT))
  obtain ⟨P', hP', hP'd⟩ := trim_family hP hPd
  obtain ⟨Q', hQ', hQ'd⟩ := trim_family hQ hQd
  exact glue hle hxy hx hy hSH hk (fun i => ⟨(hP' i).1, (hP' i).2.2⟩) hP'd
    (fun j => ⟨(hQ' j).1, (hQ' j).2.1⟩) hQ'd

/-! ## Menger's theorem -/

theorem menger_aux (G : SimpleGraph V) : ∀ (A B : Finset V) (k : ℕ),
    (∀ S, Sep G A B S → k ≤ S.card) →
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  induction G using WellFoundedLT.induction with
  | _ G ih =>
  intro A B k hsep
  by_cases hE : ∃ x y, G.Adj x y
  swap
  · push_neg at hE; exact base hE hsep
  obtain ⟨x, y, hxy⟩ := hE
  obtain ⟨H, hHdef⟩ : ∃ H, H = G.deleteEdges {s(x, y)} := ⟨_, rfl⟩
  have hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y) := by
    intro u v; rw [hHdef, deleteEdges_adj]; simp
  have hle : H ≤ G := hHdef ▸ deleteEdges_le _
  have hlt : H < G := lt_of_le_of_ne hle (fun h => ((hH x y).mp (by rw [h]; exact hxy)).2 rfl)
  by_cases hc : ∀ S, Sep H A B S → k ≤ S.card
  · obtain ⟨P, hP, hPd⟩ := ih H hlt A B k hc
    exact ⟨P, fun i => abp_mono hle (hP i), hPd⟩
  · push_neg at hc
    obtain ⟨S, hSH, hSk⟩ := hc
    have hnG : ¬ Sep G A B S := fun h => absurd (hsep S h) (by omega)
    simp only [Sep, not_forall, not_exists, not_and] at hnG
    obtain ⟨l0, hl0, hav⟩ := hnG
    have hnH : ¬ l0.IsChain H.Adj := fun hc => by
      obtain ⟨z, hz, hzS⟩ := hSH l0 ⟨hl0.1, hc, hl0.2.2⟩; exact hav z hz hzS
    obtain ⟨p, u, v, q, rfl, huv, hnuv⟩ := exists_bad l0 hl0.2.1 hnH
    have he : s(u, v) = s(x, y) := by
      by_contra hne; exact hnuv ((hH u v).mpr ⟨huv, hne⟩)
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hl0 hav
    · exact step hle hxy hH (ih H hlt) hsep hSH hSk hl0 hav
    · exact step hle hxy.symm (fun a b => by rw [hH a b, Sym2.eq_swap (a := x) (b := y)])
        (ih H hlt) hsep hSH hSk hl0 hav

/-- Menger's theorem (vertex form, finite graphs). -/
theorem menger [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hsep : ∀ S : Finset V, (∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S) → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  exact menger_aux G A B k hsep

/-- Trimmed form: each path meets `A` only in its head and `B` only in its last vertex. -/
theorem menger_trim [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hsep : ∀ S : Finset V, (∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S) → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i) ∧ (∀ x ∈ (P i).tail, x ∉ A) ∧
        (∀ x ∈ (P i).dropLast, x ∉ B)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  obtain ⟨P, hP, hPd⟩ := menger A B k hsep
  exact trim_family hP hPd


/-! ## Pendant paths off a longest path (the residual lemma) -/

/-- Valid path lists in `H`. -/
def VL (G : SimpleGraph V) (H : Finset V) (P : List V) : Prop :=
  P.Nodup ∧ P.IsChain G.Adj ∧ ∀ z ∈ P, z ∈ H

section Helpers

/-! ### Generic list helpers -/

theorem chain_glue {R : V → V → Prop} {A B : List V} {a : V} (hA : A.IsChain R)
    (hl : A.getLast? = some a) (hB : (a :: B).IsChain R) : (A ++ B).IsChain R := by
  rw [List.isChain_append]
  refine ⟨hA, (List.isChain_cons.1 hB).2, ?_⟩
  intro x hx y hy
  rw [hl, Option.mem_def, Option.some.injEq] at hx
  subst hx
  exact (List.isChain_cons.1 hB).1 y hy

theorem getLast?_glue {A B : List V} {a : V} (hl : A.getLast? = some a) :
    (A ++ B).getLast? = (a :: B).getLast? := by
  rw [List.getLast?_append, List.getLast?_cons, hl]
  cases B.getLast? <;> rfl

theorem chain_rev {l : List V} (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj :=
  List.isChain_reverse.2 (h.imp fun _ _ hab => hab.symm)

theorem chain_join {A B : List V} {a b : V} (hA : A.IsChain G.Adj) (hB : B.IsChain G.Adj)
    (ha : A.getLast? = some a) (hb : B.getLast? = some b) (hab : G.Adj a b) :
    (A ++ B.reverse).IsChain G.Adj := by
  rw [List.isChain_append]
  refine ⟨hA, chain_rev hB, ?_⟩
  intro x hx y hy
  rw [ha, Option.mem_def, Option.some.injEq] at hx
  rw [List.head?_reverse, hb, Option.mem_def, Option.some.injEq] at hy
  subst hx hy; exact hab

/-! ### Positions on `Q` -/

theorem getElem?_getD {Q : List V} {d : V} {i : ℕ} (hi : i < Q.length) :
    Q[i]? = some (Q.getD i d) := by
  rw [List.getD_eq_getElem _ _ hi, List.getElem?_eq_getElem hi]

theorem getD_mem {Q : List V} {d : V} {i : ℕ} (hi : i < Q.length) : Q.getD i d ∈ Q := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem getD_inj {Q : List V} (hn : Q.Nodup) {d : V} {i j : ℕ} (hi : i < Q.length)
    (hj : j < Q.length) (h : Q.getD i d = Q.getD j d) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (hn.getElem_inj_iff).1 h

theorem take_succ_getD {Q : List V} {d : V} {i : ℕ} (hi : i < Q.length) :
    Q.take (i+1) = Q.take i ++ [Q.getD i d] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]; rfl

theorem drop_getD {Q : List V} {d : V} {i : ℕ} (hi : i < Q.length) :
    Q.drop i = Q.getD i d :: Q.drop (i+1) := by
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi]

theorem exists_getD {Q : List V} {d z : V} (hz : z ∈ Q) : ∃ i < Q.length, Q.getD i d = z := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩

theorem getLast?_take_getD {Q : List V} {d : V} {i : ℕ} (hi : i < Q.length) :
    (Q.take (i+1)).getLast? = some (Q.getD i d) := by
  rw [take_succ_getD (d := d) hi]; simp

/-- Standing hypotheses: `Q` is a longest valid path list in `H`. -/
structure Std (G : SimpleGraph V) (H : Finset V) (Q : List V) : Prop where
  vl : VL G H Q
  max : ∀ l, VL G H l → l.length ≤ Q.length

/-- Every cycle in `H` has at most `L` vertices. -/
def CycB (G : SimpleGraph V) (H : Finset V) (L : ℕ) : Prop :=
  ∀ l, VL G H l → 3 ≤ l.length → (∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y) → l.length ≤ L

/-- A list of vertices of `H` off `Q`. -/
def Off (H : Finset V) (Q M : List V) : Prop :=
  M.Nodup ∧ (∀ z ∈ M, z ∈ H) ∧ ∀ z ∈ M, z ∉ Q

variable {H : Finset V} {Q : List V}

/-- (F1) A `v_s`–`v_t` path with interior off `Q` has at most `t - s - 1` interior vertices. -/
theorem seg_le (hs : Std G H Q) (d : V) {s t : ℕ} (hst : s < t) (ht : t < Q.length)
    {M : List V} (hM : Off H Q M)
    (hch : (Q.getD s d :: (M ++ [Q.getD t d])).IsChain G.Adj) : s + 1 + M.length ≤ t := by
  obtain ⟨hQn, hQc, hQH⟩ := hs.vl
  obtain ⟨hMn, hMH, hMQ⟩ := hM
  have hs' : s < Q.length := by omega
  have e1 : Q.drop t = Q.getD t d :: Q.drop (t+1) := drop_getD ht
  have c1 : (Q.take (s+1) ++ (M ++ [Q.getD t d])).IsChain G.Adj :=
    chain_glue (hQc.take _) (getLast?_take_getD hs') hch
  have hl2 : (Q.take (s+1) ++ (M ++ [Q.getD t d])).getLast? = some (Q.getD t d) := by simp
  have c3 : (Q.getD t d :: Q.drop (t+1)).IsChain G.Adj := by rw [← e1]; exact hQc.drop t
  have c2 := chain_glue c1 hl2 c3
  have hY : VL G H (Q.take (s+1) ++ (M ++ Q.drop t)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_append, List.nodup_append]
      refine ⟨hQn.sublist (List.take_sublist _ _),
        ⟨hMn, hQn.sublist (List.drop_sublist _ _), ?_⟩, ?_⟩
      · intro a ha b hb hab; subst hab; exact hMQ a ha (List.mem_of_mem_drop hb)
      · intro a ha b hb hab; subst hab
        rcases List.mem_append.1 hb with hb | hb
        · exact hMQ a hb (List.mem_of_mem_take ha)
        · exact List.disjoint_take_drop hQn (by omega) ha hb
    · rw [e1]; simpa using c2
    · intro z hz
      simp only [List.mem_append] at hz
      rcases hz with hz | hz | hz
      · exact hQH z (List.mem_of_mem_take hz)
      · exact hMH z hz
      · exact hQH z (List.mem_of_mem_drop hz)
  have := hs.max _ hY
  simp only [List.length_append, List.length_take, List.length_drop] at this
  omega

/-- (F2) A path off `Q` hanging from `v_j` cannot extend `v_0 … v_j` beyond `p` vertices. -/
theorem ext_le (hs : Std G H Q) (d : V) {j : ℕ} (hj : j < Q.length) {M : List V}
    (hM : Off H Q M) (hch : (Q.getD j d :: M).IsChain G.Adj) :
    j + 1 + M.length ≤ Q.length := by
  obtain ⟨hQn, hQc, hQH⟩ := hs.vl
  obtain ⟨hMn, hMH, hMQ⟩ := hM
  have hY : VL G H (Q.take (j+1) ++ M) := by
    refine ⟨?_, chain_glue (hQc.take _) (getLast?_take_getD hj) hch, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hQn.sublist (List.take_sublist _ _), hMn, ?_⟩
      intro a ha b hb hab; subst hab; exact hMQ a hb (List.mem_of_mem_take ha)
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hQH z (List.mem_of_mem_take hz)
      · exact hMH z hz
  have := hs.max _ hY
  simp only [List.length_append, List.length_take] at this
  omega

/-- (F2, other end) A path off `Q` ending next to `v_j` has at most `j` vertices. -/
theorem ext_le' (hs : Std G H Q) (d : V) {j : ℕ} (hj : j < Q.length) {M : List V}
    (hM : Off H Q M) (hch : (M ++ [Q.getD j d]).IsChain G.Adj) : M.length ≤ j := by
  obtain ⟨hQn, hQc, hQH⟩ := hs.vl
  obtain ⟨hMn, hMH, hMQ⟩ := hM
  have e1 : Q.drop j = Q.getD j d :: Q.drop (j+1) := drop_getD hj
  have c3 : (Q.getD j d :: Q.drop (j+1)).IsChain G.Adj := by rw [← e1]; exact hQc.drop j
  have c2 := chain_glue hch (by simp) c3
  have hY : VL G H (M ++ Q.drop j) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hMn, hQn.sublist (List.drop_sublist _ _), ?_⟩
      intro a ha b hb hab; subst hab; exact hMQ a ha (List.mem_of_mem_drop hb)
    · rw [e1]; simpa using c2
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hMH z hz
      · exact hQH z (List.mem_of_mem_drop hz)
  have := hs.max _ hY
  simp only [List.length_append, List.length_drop] at this
  omega

/-- A cycle made of the segment `v_a … v_b` of `Q` and a path off `Q` has at most `L` vertices. -/
theorem cyc_le (hs : Std G H Q) {L : ℕ} (hc : CycB G H L) (d : V) {a b : ℕ} (hab : a ≤ b)
    (hb : b < Q.length) {M : List V} (hM : Off H Q M)
    (hch : (Q.getD b d :: (M ++ [Q.getD a d])).IsChain G.Adj)
    (h3 : 3 ≤ b + 1 - a + M.length) : b + 1 - a + M.length ≤ L := by
  obtain ⟨hQn, hQc, hQH⟩ := hs.vl
  obtain ⟨hMn, hMH, hMQ⟩ := hM
  have hseg_len : ((Q.take (b+1)).drop a).length = b + 1 - a := by
    simp only [List.length_drop, List.length_take]; omega
  have hseg_head : ((Q.take (b+1)).drop a).head? = some (Q.getD a d) := by
    rw [List.head?_drop, List.getElem?_take_of_lt (by omega), getElem?_getD (by omega)]
  have hseg_last : ((Q.take (b+1)).drop a).getLast? = some (Q.getD b d) := by
    rw [List.getLast?_drop, if_neg (by simp only [List.length_take]; omega),
      getLast?_take_getD hb]
  have hseg_mem : ∀ z ∈ (Q.take (b+1)).drop a, z ∈ Q := fun z hz =>
    List.mem_of_mem_take (List.mem_of_mem_drop hz)
  have hch' : ((Q.getD b d :: M) ++ [Q.getD a d]).IsChain G.Adj := by simpa using hch
  obtain ⟨hbM, -, hclose⟩ := List.isChain_append.1 hch'
  have hY : VL G H ((Q.take (b+1)).drop a ++ M) := by
    refine ⟨?_, chain_glue ((hQc.take _).drop _) hseg_last hbM, ?_⟩
    · rw [List.nodup_append]
      refine ⟨(hQn.sublist (List.take_sublist _ _)).sublist (List.drop_sublist _ _), hMn, ?_⟩
      intro x hx y hy hxy; subst hxy; exact hMQ x hy (hseg_mem x hx)
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hQH z (hseg_mem z hz)
      · exact hMH z hz
  have := hc _ hY (by simp only [List.length_append, hseg_len]; omega) (by
    rw [getLast?_glue hseg_last, List.head?_append, hseg_head]
    intro x hx y hy
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hclose x hx _ (by simp))
  simpa only [List.length_append, hseg_len] using this

/-- Counting lemma: disjoint "slot pairs" `{j - t, j + t + 1}` inside `[lo, hi]`. -/
theorem slot_count (P : Finset (ℤ × ℕ)) (lo hi : ℤ)
    (h1 : ∀ x ∈ P, lo ≤ x.1 - x.2 ∧ x.1 + x.2 + 1 ≤ hi)
    (h2 : ∀ x ∈ P, ∀ y ∈ P, x.1 < y.1 → x.1 + x.2 + 1 < y.1 - y.2) :
    2 * P.card ≤ (hi + 1 - lo).toNat := by
  have hc : (P ×ˢ (Finset.univ : Finset Bool)).card = 2 * P.card := by
    simp [Finset.card_product, mul_comm]
  rw [← hc, ← Int.card_Icc]
  apply Finset.card_le_card_of_injOn
    (fun xb : (ℤ × ℕ) × Bool => if xb.2 then xb.1.1 + xb.1.2 + 1 else xb.1.1 - xb.1.2)
  · intro xb hxb
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hxb
    have := h1 _ hxb.1
    simp only [Finset.coe_Icc, Set.mem_Icc]
    split_ifs <;> omega
  · rintro ⟨⟨a, s⟩, b⟩ hxb ⟨⟨a', s'⟩, b'⟩ hyb hxy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_univ,
      Set.mem_univ, and_true] at hxb hyb
    have h12 := h2 _ hxb _ hyb
    have h21 := h2 _ hyb _ hxb
    simp only at h12 h21 hxy
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_false, if_true] at hxy <;>
      simp only [Prod.mk.injEq, and_true, and_false, reduceCtorEq] <;> omega


/-! ### Systems of pendant tails -/

/-- A system of pairwise disjoint tails `T i`, off `Q`, with `v_i :: T i` a path. -/
def Sys (G : SimpleGraph V) (H : Finset V) (Q : List V) (d : V) (T : ℕ → List V) : Prop :=
  (∀ i < Q.length, Off H Q (T i)) ∧ (∀ i < Q.length, (Q.getD i d :: T i).IsChain G.Adj) ∧
  (∀ i < Q.length, ∀ j < Q.length, i ≠ j → ∀ z ∈ T i, z ∉ T j)

/-- Weight of a tail: its length, plus one if it is nonempty. -/
def wt (l : List V) : ℕ := l.length + if l = [] then 0 else 1

/-- Total weight of a system. -/
def mu (p : ℕ) (T : ℕ → List V) : ℕ := ∑ i ∈ Finset.range p, wt (T i)

/-- A system of maximal weight. -/
def MaxSys (G : SimpleGraph V) (H : Finset V) (Q : List V) (d : V) (T : ℕ → List V) : Prop :=
  Sys G H Q d T ∧ ∀ T', Sys G H Q d T' → mu Q.length T' ≤ mu Q.length T

theorem wt_of_ne_nil {l : List V} (h : l ≠ []) : wt l = l.length + 1 := by simp [wt, h]

theorem wt_le (l : List V) : wt l ≤ l.length + 1 := by unfold wt; split_ifs <;> omega

theorem exists_maxSys (G : SimpleGraph V) (H : Finset V) (Q : List V) (d : V) :
    ∃ T, MaxSys G H Q d T := by
  classical
  have hb : ∀ T, Sys G H Q d T → mu Q.length T ≤ Q.length * (Fintype.card V + 1) := by
    intro T hT
    unfold mu
    calc _ ≤ ∑ i ∈ Finset.range Q.length, (Fintype.card V + 1) :=
          Finset.sum_le_sum fun i hi => by
            have := (hT.1 i (Finset.mem_range.1 hi)).1.length_le_card
            have := wt_le (T i)
            omega
      _ = _ := by simp
  let P : ℕ → Prop := fun n => ∃ T, Sys G H Q d T ∧ mu Q.length T = n
  have h0 : P 0 := ⟨fun _ => [], ⟨fun i _ => ⟨List.nodup_nil, by simp, by simp⟩,
    fun i _ => by simp, by simp⟩, by simp [mu, wt]⟩
  obtain ⟨T, hT, hTn⟩ := Nat.findGreatest_spec (P := P)
    (Nat.zero_le (Q.length * (Fintype.card V + 1))) h0
  refine ⟨T, hT, fun T' hT' => ?_⟩
  rw [hTn]
  exact Nat.le_findGreatest (hb T' hT') ⟨T', hT', rfl⟩

theorem mu_change1 {p i : ℕ} (hi : i < p) {T T' : ℕ → List V}
    (h : ∀ k < p, k ≠ i → T' k = T k) : mu p T' + wt (T i) = mu p T + wt (T' i) := by
  unfold mu
  have hm : i ∈ Finset.range p := Finset.mem_range.2 hi
  rw [← Finset.sum_erase_add _ _ hm, ← Finset.sum_erase_add _ (fun k => wt (T k)) hm]
  have : ∑ k ∈ (Finset.range p).erase i, wt (T' k) = ∑ k ∈ (Finset.range p).erase i, wt (T k) :=
    Finset.sum_congr rfl (fun k hk => by
      rw [h k (Finset.mem_range.1 (Finset.mem_of_mem_erase hk)) (Finset.ne_of_mem_erase hk)])
  rw [this]; ring

theorem mu_change2 {p i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) {T T' : ℕ → List V}
    (h : ∀ k < p, k ≠ i → k ≠ j → T' k = T k) :
    mu p T' + wt (T i) + wt (T j) = mu p T + wt (T' i) + wt (T' j) := by
  have h1 := mu_change1 hi (T := T) (T' := Function.update T i (T' i))
    (fun k _ hk => by simp [Function.update_of_ne hk])
  have h2 := mu_change1 hj (T := Function.update T i (T' i)) (T' := T') (fun k hk hkj => by
    by_cases hki : k = i
    · subst hki; simp
    · simp [Function.update_of_ne hki, h k hk hki hkj])
  simp only [Function.update_self, Function.update_of_ne (Ne.symm hij)] at h1 h2
  omega

variable {d : V} {T : ℕ → List V}

/-- Extending a tail by a fresh vertex contradicts maximality. -/
theorem max_ext (hm : MaxSys G H Q d T) {i : ℕ} (hi : i < Q.length) {w : V} (hwH : w ∈ H)
    (hwQ : w ∉ Q) (hwT : ∀ j < Q.length, w ∉ T j) {z : V}
    (hz : (Q.getD i d :: T i).getLast? = some z) (hzw : G.Adj z w) : False := by
  obtain ⟨⟨hoff, hch, hdis⟩, hmx⟩ := hm
  let T' := Function.update T i (T i ++ [w])
  have hT' : Sys G H Q d T' := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk l hl hkl y hy => ?_⟩
    · by_cases hki : k = i
      · subst hki; simp only [T', Function.update_self]
        obtain ⟨h1, h2, h3⟩ := hoff k hk
        refine ⟨?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨h1, List.nodup_singleton w, ?_⟩
          intro a ha b hb hab
          rw [List.mem_singleton] at hb; subst hb; subst hab; exact hwT k hk ha
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact h2 x hx
          · rw [List.mem_singleton] at hx; subst hx; exact hwH
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact h3 x hx
          · rw [List.mem_singleton] at hx; subst hx; exact hwQ
      · simp only [T', Function.update_of_ne hki]; exact hoff k hk
    · by_cases hki : k = i
      · subst hki; simp only [T', Function.update_self]
        have : (Q.getD k d :: (T k ++ [w])) = (Q.getD k d :: T k) ++ [w] := rfl
        rw [this, List.isChain_append]
        refine ⟨hch k hk, List.isChain_singleton w, ?_⟩
        intro x hx y hy
        rw [hz, Option.mem_def, Option.some.injEq] at hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hx hy; exact hzw
      · simp only [T', Function.update_of_ne hki]; exact hch k hk
    · by_cases hki : k = i
      · subst hki
        have hli : l ≠ k := Ne.symm hkl
        simp only [T', Function.update_self, Function.update_of_ne hli] at hy ⊢
        rcases List.mem_append.1 hy with hy | hy
        · exact hdis k hk l hl hkl y hy
        · rw [List.mem_singleton] at hy; subst hy; exact hwT l hl
      · by_cases hli : l = i
        · subst hli
          simp only [T', Function.update_self, Function.update_of_ne hki] at hy ⊢
          intro hy'
          rcases List.mem_append.1 hy' with hy' | hy'
          · exact hdis k hk l hl hkl y hy hy'
          · rw [List.mem_singleton] at hy'; subst hy'; exact hwT k hk hy
        · simp only [T', Function.update_of_ne hki, Function.update_of_ne hli] at hy ⊢
          exact hdis k hk l hl hkl y hy
  have h1 := mu_change1 hi (T := T) (T' := T') (fun k _ hk => by
    simp [T', Function.update_of_ne hk])
  have h2 := hmx T' hT'
  have hw1 : wt (T' i) = (T i).length + 2 := by
    simp only [T', Function.update_self]
    rw [wt_of_ne_nil (by simp)]; simp
  have hw2 := wt_le (T i)
  omega

/-- Cutting a tail and re-hanging its end at an empty `v_i` contradicts maximality. -/
theorem max_cut (hm : MaxSys G H Q d T) {i j k : ℕ} (hi : i < Q.length) (hj : j < Q.length)
    (hTi : T i = []) (hk : 1 ≤ k) {y : V} (hy : (T j)[k]? = some y)
    (hiy : G.Adj (Q.getD i d) y) : False := by
  obtain ⟨⟨hoff, hch, hdis⟩, hmx⟩ := hm
  obtain ⟨hkl, hky⟩ := List.getElem?_eq_some_iff.1 hy
  have hij : i ≠ j := by rintro rfl; simp [hTi] at hkl
  obtain ⟨hjn, hjH, hjQ⟩ := hoff j hj
  have hdk : (T j).drop k = y :: (T j).drop (k+1) := by rw [List.drop_eq_getElem_cons hkl, hky]
  let T' := Function.update (Function.update T j ((T j).take k)) i ((T j).drop k)
  have eTi : T' i = (T j).drop k := by simp [T']
  have eTj : T' j = (T j).take k := by simp [T', Function.update_of_ne (Ne.symm hij)]
  have eTm : ∀ m, m ≠ i → m ≠ j → T' m = T m := fun m hmi hmj => by
    simp [T', Function.update_of_ne hmi, Function.update_of_ne hmj]
  have mem' : ∀ m z, z ∈ T' m → (m = i ∧ z ∈ (T j).drop k) ∨ (m = j ∧ z ∈ (T j).take k) ∨
      (m ≠ i ∧ m ≠ j ∧ z ∈ T m) := by
    intro m z hz
    by_cases hmi : m = i
    · subst hmi; rw [eTi] at hz; exact Or.inl ⟨rfl, hz⟩
    · by_cases hmj : m = j
      · subst hmj; rw [eTj] at hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)
      · rw [eTm m hmi hmj] at hz; exact Or.inr (Or.inr ⟨hmi, hmj, hz⟩)
  have hT' : Sys G H Q d T' := by
    refine ⟨fun m hm => ?_, fun m hm => ?_, fun m hm l hl hml z hz hz' => ?_⟩
    · by_cases hmi : m = i
      · subst hmi; rw [eTi]
        exact ⟨hjn.sublist (List.drop_sublist _ _), fun z hz => hjH z (List.mem_of_mem_drop hz),
          fun z hz => hjQ z (List.mem_of_mem_drop hz)⟩
      · by_cases hmj : m = j
        · subst hmj; rw [eTj]
          exact ⟨hjn.sublist (List.take_sublist _ _),
            fun z hz => hjH z (List.mem_of_mem_take hz),
            fun z hz => hjQ z (List.mem_of_mem_take hz)⟩
        · rw [eTm m hmi hmj]; exact hoff m hm
    · by_cases hmi : m = i
      · subst hmi; rw [eTi, hdk, List.isChain_cons_cons]
        refine ⟨hiy, ?_⟩
        rw [← hdk]; exact (List.isChain_cons.1 (hch j hj)).2.drop k
      · by_cases hmj : m = j
        · subst hmj; rw [eTj]
          have := (hch m hj).take (k+1)
          simpa using this
        · rw [eTm m hmi hmj]; exact hch m hm
    · have hTk : ∀ a b, a ∈ (T j).take k → b ∈ (T j).drop k → a ≠ b := by
        intro a b ha hb hab; subst hab; exact List.disjoint_take_drop hjn le_rfl ha hb
      rcases mem' m z hz with ⟨hm1, h1⟩ | ⟨hm1, h1⟩ | ⟨hmi, hmj, h1⟩ <;>
        rcases mem' l z hz' with ⟨hl1, h2⟩ | ⟨hl1, h2⟩ | ⟨hli, hlj, h2⟩
      · exact hml (hm1.trans hl1.symm)
      · exact hTk z z h2 h1 rfl
      · exact hdis j hj l hl (Ne.symm hlj) z (List.mem_of_mem_drop h1) h2
      · exact hTk z z h1 h2 rfl
      · exact hml (hm1.trans hl1.symm)
      · exact hdis j hj l hl (Ne.symm hlj) z (List.mem_of_mem_take h1) h2
      · exact hdis m hm j hj hmj z h1 (List.mem_of_mem_drop h2)
      · exact hdis m hm j hj hmj z h1 (List.mem_of_mem_take h2)
      · exact hdis m hm l hl hml z h1 h2
  have h1 := mu_change2 hi hj hij (T := T) (T' := T') (fun m _ hmi hmj => eTm m hmi hmj)
  have h2 := hmx T' hT'
  have w0 : wt (T i) = 0 := by rw [hTi]; rfl
  have w1 : wt (T j) = (T j).length + 1 := wt_of_ne_nil (List.ne_nil_of_length_pos (by omega))
  have w2 : wt ((T j).drop k) = (T j).length - k + 1 := by
    rw [wt_of_ne_nil (by rw [hdk]; simp)]; simp
  have w3 : wt ((T j).take k) = k + 1 := by
    rw [wt_of_ne_nil (List.ne_nil_of_length_pos (by simp; omega))]; simp; omega
  rw [eTi, eTj] at h1
  omega

/-- Claim 3: neighbours of an untouched `v_i` lie on `Q` or are second vertices of tails. -/
theorem nbr_v (hm : MaxSys G H Q d T) {i : ℕ} (hi : i < Q.length) (hTi : T i = []) {w : V}
    (hwH : w ∈ H) (hw : G.Adj (Q.getD i d) w) :
    w ∈ Q ∨ ∃ j < Q.length, (T j).head? = some w := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hwQ, hwh⟩ := hcon
  have hwT : ∀ j < Q.length, w ∉ T j := by
    intro j hj hwj
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hwj
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact hwh j hj (by rw [List.head?_eq_getElem?]; exact hk)
    · exact max_cut hm hi hj hTi hk1 hk hw
  exact max_ext hm hi hwH hwQ hwT (z := Q.getD i d) (by simp [hTi]) hw

/-- Claim 4, first part: neighbours of an end `u_i` lie in `W`. -/
theorem nbr_u (hm : MaxSys G H Q d T) {i : ℕ} (hi : i < Q.length) {w : V} (hwH : w ∈ H)
    {z : V} (hz : (Q.getD i d :: T i).getLast? = some z) (hw : G.Adj z w) :
    w ∈ Q ∨ ∃ j < Q.length, w ∈ T j := by
  by_contra hcon
  push_neg at hcon
  exact max_ext hm hi hwH hcon.1 hcon.2 hz hw


/-! ### Pendant paths and the exchange inequalities -/

theorem getLast?_cons_ne {a : V} {l : List V} (h : l ≠ []) : (a :: l).getLast? = l.getLast? := by
  rw [List.getLast?_cons, List.getLast?_eq_getLast h]; rfl

theorem getLast?_append_ne {l l' : List V} (h : l' ≠ []) : (l ++ l').getLast? = l'.getLast? := by
  rw [List.getLast?_append, List.getLast?_eq_getLast h]; rfl

theorem getLast_take_succ {a : V} {l : List V} {k : ℕ} {w : V} (hk : l[k]? = some w) :
    (a :: l.take (k+1)).getLast? = some w := by
  rw [List.getLast?_cons, List.getLast?_take]; simp [hk]

/-- A pendant path `v_j :: A` (with `A` off `Q`) ending at `y`. -/
structure Pend (G : SimpleGraph V) (H : Finset V) (Q : List V) (d : V) (j : ℕ) (A : List V)
    (y : V) : Prop where
  off : Off H Q A
  ch : (Q.getD j d :: A).IsChain G.Adj
  last : (Q.getD j d :: A).getLast? = some y

theorem off_append {A B : List V} (hA : Off H Q A) (hB : Off H Q B) (hAB : ∀ z ∈ A, z ∉ B) :
    Off H Q (A ++ B) := by
  refine ⟨List.nodup_append.2 ⟨hA.1, hB.1, fun a ha b hb hab => hAB a ha (hab ▸ hb)⟩,
    fun z hz => ?_, fun z hz => ?_⟩
  · rcases List.mem_append.1 hz with hz | hz
    exacts [hA.2.1 z hz, hB.2.1 z hz]
  · rcases List.mem_append.1 hz with hz | hz
    exacts [hA.2.2 z hz, hB.2.2 z hz]

theorem off_reverse {A : List V} (hA : Off H Q A) : Off H Q A.reverse :=
  ⟨List.nodup_reverse.2 hA.1, fun z hz => hA.2.1 z (List.mem_reverse.1 hz),
    fun z hz => hA.2.2 z (List.mem_reverse.1 hz)⟩

theorem off_sub {A B : List V} (hA : Off H Q A) (h : B.Sublist A) : Off H Q B :=
  ⟨hA.1.sublist h, fun z hz => hA.2.1 z (h.subset hz), fun z hz => hA.2.2 z (h.subset hz)⟩

theorem pend_snoc {j : ℕ} {A : List V} {x u : V} (hP : Pend G H Q d j A x) (hxu : G.Adj x u)
    (huH : u ∈ H) (huQ : u ∉ Q) (huA : u ∉ A) : Pend G H Q d j (A ++ [u]) u := by
  refine ⟨off_append hP.off ⟨List.nodup_singleton u, by simpa using huH, by simpa using huQ⟩
    (fun z hz hz' => by rw [List.mem_singleton] at hz'; subst hz'; exact huA hz), ?_,
    by rw [getLast?_cons_ne (by simp)]; simp⟩
  have := chain_join hP.ch (List.isChain_singleton u) hP.last (by simp) hxu
  simpa using this

theorem pend_take {j : ℕ} {A : List V} (hA : Off H Q A) (hch : (Q.getD j d :: A).IsChain G.Adj)
    (t : ℕ) : Pend G H Q d j (A.take t)
      ((Q.getD j d :: A.take t).getLast (List.cons_ne_nil _ _)) :=
  ⟨off_sub hA (List.take_sublist _ _), by have := hch.take (t+1); simpa using this,
    List.getLast?_eq_getLast (List.cons_ne_nil _ _)⟩

theorem pend_hi (hs : Std G H Q) {j : ℕ} (hj : j < Q.length) {A : List V} {x : V}
    (hP : Pend G H Q d j A x) : j + 1 + A.length ≤ Q.length :=
  ext_le hs d hj hP.off hP.ch

theorem pend_lo (hs : Std G H Q) {j : ℕ} (hj : j < Q.length) {A : List V} {x : V}
    (hP : Pend G H Q d j A x) : A.length ≤ j := by
  have := ext_le' hs d hj (off_reverse hP.off) (by have := chain_rev hP.ch; simpa using this)
  simpa using this

/-- Two pendant paths joined at their ends give a `v_a`–`v_b` path off `Q`. -/
theorem join_le (hs : Std G H Q) {a b : ℕ} (hab : a < b) (hb : b < Q.length) {A B : List V}
    {x y : V} (hA : Pend G H Q d a A x) (hB : Pend G H Q d b B y) (hxy : G.Adj x y)
    (hAB : ∀ z ∈ A, z ∉ B) : a + 1 + (A.length + B.length) ≤ b := by
  have := seg_le hs d hab hb (M := A ++ B.reverse)
    (off_append hA.off (off_reverse hB.off) (fun z hz hz' => hAB z hz (List.mem_reverse.1 hz')))
    (by have := chain_join hA.ch hB.ch hA.last hB.last hxy; simpa using this)
  simpa using this

/-- Two pendant paths joined at their ends close a cycle with the segment `v_a … v_b`. -/
theorem join_cyc (hs : Std G H Q) {L : ℕ} (hc : CycB G H L) {a b : ℕ} (hab : a < b)
    (hb : b < Q.length) {A B : List V} {x y : V} (hA : Pend G H Q d a A x)
    (hB : Pend G H Q d b B y) (hxy : G.Adj x y) (hAB : ∀ z ∈ A, z ∉ B)
    (h1 : 1 ≤ A.length + B.length) : b + 1 - a + (A.length + B.length) ≤ L := by
  have := cyc_le hs hc d hab.le hb (M := B ++ A.reverse)
    (off_append hB.off (off_reverse hA.off) (fun z hz hz' => hAB z (List.mem_reverse.1 hz') hz))
    (by have := chain_join hB.ch hA.ch hB.last hA.last hxy.symm; simpa using this)
    (by simp only [List.length_append, List.length_reverse]; omega)
  simp only [List.length_append, List.length_reverse] at this; omega

/-- A chord from the end of a pendant path closes a cycle. -/
theorem chord_le (hs : Std G H Q) {L : ℕ} (hc : CycB G H L) {i : ℕ} (hi : i < Q.length)
    {A : List V} {u y : V} (hP : Pend G H Q d i A u) {t : ℕ} (ht : t + 2 ≤ A.length)
    (hy : (Q.getD i d :: A.take t).getLast? = some y) (huy : G.Adj u y) :
    A.length + 1 - t ≤ L := by
  obtain ⟨hQn, hQc, hQH⟩ := hs.vl
  obtain ⟨hAn, hAH, hAQ⟩ := hP.off
  have he : Q.getD i d :: A = (Q.getD i d :: A.take t) ++ A.drop t := by simp
  have hch := hP.ch
  rw [he, List.isChain_append] at hch
  obtain ⟨-, hc2, hlink⟩ := hch
  have hymem : y ∈ Q.getD i d :: A.take t := List.mem_of_getLast? hy
  have hdn : A.drop t ≠ [] := by
    intro h; rw [List.drop_eq_nil_iff] at h; omega
  have hnd : (Q.getD i d :: A).Nodup := List.nodup_cons.2 ⟨fun h => hAQ _ h (getD_mem hi), hAn⟩
  rw [he, List.nodup_append] at hnd
  have hyd : y ∉ A.drop t := fun h => hnd.2.2 y hymem y h rfl
  have hyH : y ∈ H := by
    rcases List.mem_cons.1 hymem with h | h
    · rw [h]; exact hQH _ (getD_mem hi)
    · exact hAH y (List.mem_of_mem_take h)
  have hC : VL G H (y :: A.drop t) := by
    refine ⟨List.nodup_cons.2 ⟨hyd, hAn.sublist (List.drop_sublist _ _)⟩, ?_, ?_⟩
    · rw [List.isChain_cons]; exact ⟨fun z hz => hlink y (Option.mem_def.2 hy) z hz, hc2⟩
    · intro z hz
      rcases List.mem_cons.1 hz with h | h
      · rw [h]; exact hyH
      · exact hAH z (List.mem_of_mem_drop h)
  have hlast : (y :: A.drop t).getLast? = some u := by
    rw [getLast?_cons_ne hdn, ← getLast?_append_ne hdn (l := Q.getD i d :: A.take t), ← he]
    exact hP.last
  have := hc _ hC (by simp only [List.length_cons, List.length_drop]; omega) (by
    rw [hlast]; intro x hx z hz
    simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hz
    subst hx hz; exact huy)
  simp only [List.length_cons, List.length_drop] at this; omega

variable [DecidableRel G.Adj]

/-- Number of `Q`-neighbours of `z`, counted by position. -/
def nQ (G : SimpleGraph V) [DecidableRel G.Adj] (Q : List V) (d : V) (z : V) : ℕ :=
  ((Finset.range Q.length).filter (fun t => G.Adj z (Q.getD t d))).card

/-- Claim 1: degree of a vertex of `Q` into `Q`. -/
theorem deg_q (hs : Std G H Q) {L : ℕ} (hL : 2 ≤ L) (hc : CycB G H L) (d : V) {l : ℕ}
    (hl : l < Q.length) :
    nQ G Q d (Q.getD l d) ≤ Q.length - 1 ∧ nQ G Q d (Q.getD l d) ≤ 2 * L - 2 := by
  have h0 : Off H Q ([] : List V) := ⟨List.nodup_nil, by simp, by simp⟩
  constructor
  · calc _ ≤ ((Finset.range Q.length).erase l).card := Finset.card_le_card (fun t ht => by
          simp only [Finset.mem_filter, Finset.mem_range] at ht
          refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_range.2 ht.1⟩
          subst h; exact G.irrefl ht.2)
      _ = _ := by rw [Finset.card_erase_of_mem (Finset.mem_range.2 hl), Finset.card_range]
  · calc _ ≤ ((Finset.Icc (l + 1 - L) (l + L - 1)).erase l).card :=
          Finset.card_le_card (fun t ht => by
          simp only [Finset.mem_filter, Finset.mem_range] at ht
          obtain ⟨ht1, ht2⟩ := ht
          have hne : t ≠ l := by rintro rfl; exact G.irrefl ht2
          refine Finset.mem_erase.2 ⟨hne, Finset.mem_Icc.2 ⟨?_, ?_⟩⟩
          · by_contra hlt
            have := cyc_le hs hc d (a := t) (b := l) (by omega) hl h0
              (by simpa [List.isChain_cons_cons] using ht2) (by simp only [List.length_nil]; omega)
            simp only [List.length_nil] at this; omega
          · by_contra hlt
            have := cyc_le hs hc d (a := l) (b := t) (by omega) ht1 h0
              (by simpa [List.isChain_cons_cons] using ht2.symm)
              (by simp only [List.length_nil]; omega)
            simp only [List.length_nil] at this; omega)
      _ ≤ _ := by
          rw [Finset.card_erase_of_mem (Finset.mem_Icc.2 ⟨by omega, by omega⟩), Nat.card_Icc]
          omega

/-- Claim 2: degree into `Q` of a vertex of `H` off `Q`. -/
theorem deg_x (hs : Std G H Q) {L : ℕ} (hL : 2 ≤ L) (hc : CycB G H L) (d : V) {x : V}
    (hxH : x ∈ H) (hxQ : x ∉ Q) : 2 * nQ G Q d x ≤ Q.length - 1 ∧ nQ G Q d x ≤ L - 1 := by
  have hx : Off H Q [x] := ⟨List.nodup_singleton x, by simpa using hxH, by simpa using hxQ⟩
  obtain ⟨S, hS⟩ : ∃ S, S = (Finset.range Q.length).filter (fun t => G.Adj x (Q.getD t d)) :=
    ⟨_, rfl⟩
  have hn : nQ G Q d x = S.card := by rw [hS]; rfl
  have hmem : ∀ s ∈ S, s < Q.length ∧ G.Adj x (Q.getD s d) := by
    intro s hsS; rw [hS] at hsS; simpa using hsS
  have hlo : ∀ s ∈ S, 1 ≤ s := by
    intro s hsS
    obtain ⟨hsp, hadj⟩ := hmem s hsS
    have := ext_le' hs d hsp hx (by simpa [List.isChain_cons_cons] using hadj)
    simpa using this
  have hhi : ∀ s ∈ S, s + 2 ≤ Q.length := by
    intro s hsS
    obtain ⟨hsp, hadj⟩ := hmem s hsS
    have := ext_le hs d hsp hx (by simpa [List.isChain_cons_cons] using hadj.symm)
    simp only [List.length_singleton] at this; omega
  have hgap : ∀ s ∈ S, ∀ s' ∈ S, s < s' → s + 2 ≤ s' := by
    intro s hsS s' hs'S hss'
    obtain ⟨hsp, hadj⟩ := hmem s hsS
    obtain ⟨hsp', hadj'⟩ := hmem s' hs'S
    have := seg_le hs d hss' hsp' hx (by simpa [List.isChain_cons_cons] using ⟨hadj.symm, hadj'⟩)
    simp only [List.length_singleton] at this; omega
  rw [hn]
  constructor
  · have hinj : Function.Injective (fun s : ℕ => ((s : ℤ), (0 : ℕ))) := by
      intro a b h; simp only [Prod.mk.injEq, Nat.cast_inj, and_true] at h; exact h
    have := slot_count (S.image (fun s : ℕ => ((s : ℤ), (0 : ℕ)))) 1 (Q.length - 1)
      (fun y hy => by
        obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.1 hy
        have := hlo s hsS; have := hhi s hsS
        simp only [Nat.cast_zero]; omega)
      (fun y hy z hz hyz => by
        obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.1 hy
        obtain ⟨s', hs'S, rfl⟩ := Finset.mem_image.1 hz
        simp only [Nat.cast_zero] at hyz ⊢
        have := hgap s hsS s' hs'S (by omega)
        omega)
    rw [Finset.card_image_of_injective _ hinj] at this
    omega
  · rcases S.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · calc S.card ≤ (Finset.Icc (S.min' hne) (S.min' hne + L - 2)).card :=
            Finset.card_le_card (fun s hsS => by
              have h1 := Finset.min'_le S s hsS
              refine Finset.mem_Icc.2 ⟨h1, ?_⟩
              rcases Nat.eq_or_lt_of_le h1 with h | h
              · rw [← h]; omega
              · obtain ⟨hsp, hadj⟩ := hmem s hsS
                obtain ⟨hsp0, hadj0⟩ := hmem _ (S.min'_mem hne)
                have := cyc_le hs hc d (a := S.min' hne) (b := s) h1 hsp hx
                  (by simpa [List.isChain_cons_cons] using ⟨hadj.symm, hadj0⟩)
                  (by simp only [List.length_singleton]; omega)
                simp only [List.length_singleton] at this; omega)
        _ ≤ _ := by rw [Nat.card_Icc]; omega


/-- Claim 4: the end `u` of a nonempty tail has small `H`-degree. -/
theorem deg_u (hs : Std G H Q) {L : ℕ} (hL : 2 ≤ L) (hc : CycB G H L) (hm : MaxSys G H Q d T)
    {i : ℕ} (hi : i < Q.length) (hTi : T i ≠ []) {u : V}
    (hu : (Q.getD i d :: T i).getLast? = some u) :
    2 * (H.filter (G.Adj u)).card ≤ Q.length - 1 ∧ (H.filter (G.Adj u)).card ≤ L - 1 := by
  obtain ⟨hoff, hch, hdis⟩ := hm.1
  have hPi : Pend G H Q d i (T i) u := ⟨hoff i hi, hch i hi, hu⟩
  have huT : u ∈ T i := by
    have hu' := hu
    rw [getLast?_cons_ne hTi, List.getLast?_eq_getLast hTi, Option.some.injEq] at hu'
    rw [← hu']; exact List.getLast_mem hTi
  have huH : u ∈ H := (hoff i hi).2.1 u huT
  have huQ : u ∉ Q := (hoff i hi).2.2 u huT
  have hr : 1 ≤ (T i).length := List.length_pos_of_ne_nil hTi
  have hir := pend_hi hs hi hPi
  have hri := pend_lo hs hi hPi
  let g : ℕ → ℕ → V := fun j t => (Q.getD j d :: (T j).take t).getLast (List.cons_ne_nil _ _)
  have hPg : ∀ j < Q.length, ∀ t, Pend G H Q d j ((T j).take t) (g j t) :=
    fun j hj t => pend_take (hoff j hj) (hch j hj) t
  let P := ((Finset.range Q.length) ×ˢ (Finset.range (Fintype.card V + 1))).filter
    (fun jt => jt.2 ≤ (T jt.1).length ∧ G.Adj u (g jt.1 jt.2))
  have hPm : ∀ jt ∈ P, jt.1 < Q.length ∧ jt.2 ≤ (T jt.1).length ∧ G.Adj u (g jt.1 jt.2) := by
    intro jt hjt
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hjt
    exact ⟨hjt.1.1, hjt.2⟩
  -- every neighbour of `u` is the vertex at some position of some `R_j`
  have hA : (H.filter (G.Adj u)).card ≤ P.card := by
    refine le_trans (Finset.card_le_card (t := P.image (fun jt => g jt.1 jt.2)) ?_)
      Finset.card_image_le
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_image]
    rcases nbr_u hm hi hw.1 hu hw.2 with hwQ | ⟨j, hj, hwj⟩
    · obtain ⟨j, hj, rfl⟩ := exists_getD (d := d) hwQ
      have hg0 : g j 0 = Q.getD j d := by simp [g]
      refine ⟨(j, 0), ?_, hg0⟩
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hj, by omega⟩, Nat.zero_le _, by rw [hg0]; exact hw.2⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hwj
      have hkl : k < (T j).length := (List.getElem?_eq_some_iff.1 hk).1
      have hlen := (hoff j hj).1.length_le_card
      have hgw : g j (k+1) = w := by
        have h1 := getLast_take_succ (a := Q.getD j d) hk
        rw [List.getLast?_eq_getLast (List.cons_ne_nil _ _), Option.some.injEq] at h1
        exact h1
      refine ⟨(j, k+1), ?_, hgw⟩
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hj, by omega⟩, by omega, by rw [hgw]; exact hw.2⟩
  let Pon := P.filter (fun jt => jt.1 = i)
  let Pup := P.filter (fun jt => i < jt.1)
  let Pdn := P.filter (fun jt => jt.1 < i)
  have hB : P.card ≤ Pon.card + Pup.card + Pdn.card := by
    calc P.card ≤ (Pon ∪ Pup ∪ Pdn).card := Finset.card_le_card (fun x hx => by
          simp only [Pon, Pup, Pdn, Finset.mem_union, Finset.mem_filter]
          rcases lt_trichotomy x.1 i with h | h | h
          · exact Or.inr ⟨hx, h⟩
          · exact Or.inl (Or.inl ⟨hx, h⟩)
          · exact Or.inl (Or.inr ⟨hx, h⟩))
      _ ≤ _ := by
          have := Finset.card_union_le (Pon ∪ Pup) Pdn
          have := Finset.card_union_le Pon Pup
          omega
  -- neighbours on `R_i` itself
  have hon : Pon.card ≤ (T i).length ∧ Pon.card ≤ L - 1 := by
    have key : ∀ jt ∈ Pon, jt.1 = i ∧ jt.2 < (T i).length ∧ (T i).length + 1 ≤ jt.2 + L := by
      intro jt hjt
      simp only [Pon, Finset.mem_filter] at hjt
      obtain ⟨hjtP, hji⟩ := hjt
      obtain ⟨-, ht, hadj⟩ := hPm jt hjtP
      rw [hji] at ht hadj
      have hlt : jt.2 < (T i).length := by
        rcases Nat.lt_or_ge jt.2 (T i).length with h | h
        · exact h
        · exfalso
          have he : jt.2 = (T i).length := le_antisymm ht h
          have h1 := (hPg i hi jt.2).last
          rw [he, List.take_length, hu, Option.some.injEq] at h1
          rw [he, ← h1] at hadj
          exact G.irrefl hadj
      refine ⟨hji, hlt, ?_⟩
      by_cases h2 : jt.2 + 2 ≤ (T i).length
      · have := chord_le hs hc hi hPi h2 (hPg i hi jt.2).last hadj; omega
      · omega
    have inj : Set.InjOn Prod.snd (Pon : Set (ℕ × ℕ)) := by
      intro x hx y hy hxy
      have := (key x hx).1; have := (key y hy).1
      exact Prod.ext (by omega) hxy
    constructor
    · calc Pon.card ≤ (Finset.range (T i).length).card :=
            Finset.card_le_card_of_injOn Prod.snd (fun x hx => Finset.mem_coe.2
              (Finset.mem_range.2 (key x (Finset.mem_coe.1 hx)).2.1)) inj
        _ = _ := Finset.card_range _
    · calc Pon.card ≤ (Finset.Ico ((T i).length + 1 - L) (T i).length).card :=
            Finset.card_le_card_of_injOn Prod.snd (fun x hx => by
              have := key x (Finset.mem_coe.1 hx)
              rw [Finset.mem_coe, Finset.mem_Ico]; omega) inj
        _ ≤ _ := by rw [Nat.card_Ico]; omega
  -- the exchange inequality between two other tails
  have hgam : ∀ x ∈ P, ∀ y ∈ P, x.1 ≠ i → y.1 ≠ i → x.1 < y.1 →
      x.1 + 1 + (x.2 + 1 + y.2) ≤ y.1 := by
    intro x hx y hy hxi hyi hxy
    obtain ⟨hxj, hxt, hxa⟩ := hPm x hx
    obtain ⟨hyj, hyt, hya⟩ := hPm y hy
    have hPx := hPg x.1 hxj x.2
    have hPy := hPg y.1 hyj y.2
    have hux : u ∉ (T x.1).take x.2 := fun h =>
      hdis i hi x.1 hxj (Ne.symm hxi) u huT (List.mem_of_mem_take h)
    have hPx' := pend_snoc hPx hxa.symm huH huQ hux
    have hdisj : ∀ z ∈ (T x.1).take x.2 ++ [u], z ∉ (T y.1).take y.2 := by
      intro z hz hz'
      rcases List.mem_append.1 hz with hz | hz
      · exact hdis x.1 hxj y.1 hyj (by omega) z (List.mem_of_mem_take hz)
          (List.mem_of_mem_take hz')
      · rw [List.mem_singleton] at hz; subst hz
        exact hdis i hi y.1 hyj (Ne.symm hyi) _ huT (List.mem_of_mem_take hz')
    have := join_le hs hxy hyj hPx' hPy hya hdisj
    simp only [List.length_append, List.length_singleton, List.length_take] at this
    omega
  -- tails above `i`
  have hupf : ∀ jt ∈ Pup, (i:ℤ) + (T i).length + 1 ≤ jt.1 - jt.2 ∧
      (jt.1:ℤ) + jt.2 + 1 ≤ Q.length - 1 ∧ (jt.1:ℤ) + jt.2 + 1 ≤ i + L - (T i).length := by
    intro jt hjt
    simp only [Pup, Finset.mem_filter] at hjt
    obtain ⟨hjtP, hij⟩ := hjt
    obtain ⟨hj, ht, hadj⟩ := hPm jt hjtP
    have hPj := hPg jt.1 hj jt.2
    have hlen : ((T jt.1).take jt.2).length = jt.2 := by simp; omega
    have hdisj : ∀ z ∈ T i, z ∉ (T jt.1).take jt.2 := fun z hz hz' =>
      hdis i hi jt.1 hj (by omega) z hz (List.mem_of_mem_take hz')
    have h1 := join_le hs hij hj hPi hPj hadj hdisj
    have huS : u ∉ (T jt.1).take jt.2 := hdisj u huT
    have h2 := pend_hi hs hj (pend_snoc hPj hadj.symm huH huQ huS)
    have h3 := join_cyc hs hc hij hj hPi hPj hadj hdisj (by omega)
    simp only [List.length_append, List.length_singleton, hlen] at h1 h2 h3
    omega
  -- tails below `i`
  have hdnf : ∀ jt ∈ Pdn, (jt.1:ℤ) + jt.2 + (T i).length + 1 ≤ i ∧ (jt.2:ℤ) + 1 ≤ jt.1 ∧
      (i:ℤ) - jt.1 + 1 + jt.2 + (T i).length ≤ L := by
    intro jt hjt
    simp only [Pdn, Finset.mem_filter] at hjt
    obtain ⟨hjtP, hji⟩ := hjt
    obtain ⟨hj, ht, hadj⟩ := hPm jt hjtP
    have hPj := hPg jt.1 hj jt.2
    have hlen : ((T jt.1).take jt.2).length = jt.2 := by simp; omega
    have hdisj : ∀ z ∈ (T jt.1).take jt.2, z ∉ T i := fun z hz hz' =>
      hdis jt.1 hj i hi (by omega) z (List.mem_of_mem_take hz) hz'
    have h1 := join_le hs hji hi hPj hPi hadj.symm hdisj
    have huS : u ∉ (T jt.1).take jt.2 := fun h => hdisj u h huT
    have h2 := pend_lo hs hj (pend_snoc hPj hadj.symm huH huQ huS)
    have h3 := join_cyc hs hc hji hi hPj hPi hadj.symm hdisj (by omega)
    simp only [List.length_append, List.length_singleton, hlen] at h1 h2 h3
    omega
  -- slot counting above
  obtain ⟨Iu, hIu⟩ : ∃ s : Finset (ℤ × ℕ), s = Pup.image (fun jt => ((jt.1 : ℤ), jt.2)) :=
    ⟨_, rfl⟩
  have hIuc : Iu.card = Pup.card := by
    rw [hIu]
    exact Finset.card_image_of_injective _ (fun a b h => by
      simp only [Prod.mk.injEq, Nat.cast_inj] at h; exact Prod.ext h.1 h.2)
  have hIu2 : ∀ x ∈ Iu, ∀ y ∈ Iu, x.1 < y.1 → x.1 + x.2 + 1 < y.1 - y.2 := by
    intro x hx y hy hxy
    rw [hIu] at hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    simp only [Pup, Finset.mem_filter] at ha hb
    simp only at hxy ⊢
    have := hgam a ha.1 b hb.1 (by omega) (by omega) (by omega)
    omega
  have hupA := slot_count Iu (i + (T i).length + 1) (Q.length - 1) (fun x hx => by
      rw [hIu] at hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      have := hupf a ha; simp only; omega) hIu2
  have hupB := slot_count Iu (i + (T i).length + 1) (i + L - (T i).length) (fun x hx => by
      rw [hIu] at hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      have := hupf a ha; simp only; omega) hIu2
  -- slot counting below (reflected)
  obtain ⟨Id, hId⟩ : ∃ s : Finset (ℤ × ℕ), s = Pdn.image (fun jt => (-(jt.1 : ℤ), jt.2)) :=
    ⟨_, rfl⟩
  have hIdc : Id.card = Pdn.card := by
    rw [hId]
    exact Finset.card_image_of_injective _ (fun a b h => by
      simp only [Prod.mk.injEq, neg_inj, Nat.cast_inj] at h; exact Prod.ext h.1 h.2)
  have hId2 : ∀ x ∈ Id, ∀ y ∈ Id, x.1 < y.1 → x.1 + x.2 + 1 < y.1 - y.2 := by
    intro x hx y hy hxy
    rw [hId] at hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    simp only [Pdn, Finset.mem_filter] at ha hb
    simp only at hxy ⊢
    have := hgam b hb.1 a ha.1 (by omega) (by omega) (by omega)
    omega
  have hdnA := slot_count Id (-(i:ℤ) + (T i).length + 1) 0 (fun x hx => by
      rw [hId] at hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      have := hdnf a ha; simp only; omega) hId2
  have hdnB := slot_count Id (-(i:ℤ) + (T i).length + 1) (L - i - (T i).length) (fun x hx => by
      rw [hId] at hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      have := hdnf a ha; simp only; omega) hId2
  rw [hIuc] at hupA hupB
  rw [hIdc] at hdnA hdnB
  have hdeg := hA.trans hB
  omega


theorem headD_mem {l : List V} (h : l ≠ []) (d : V) : l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => simp

/-- Assembly: double counting the edges from untouched `v_i` to second vertices of tails. -/
theorem sum_bound (hm : MaxSys G H Q d T) (m : ℕ)
    (hA : ∀ i < Q.length, T i = [] → nQ G Q d (Q.getD i d) ≤ m)
    (hB : ∀ i < Q.length, T i ≠ [] → nQ G Q d ((T i).headD d) +
      (H.filter (G.Adj ((Q.getD i d :: T i).getLast (List.cons_ne_nil _ _)))).card ≤ m) :
    ∑ i ∈ Finset.range Q.length,
      (H.filter (G.Adj ((Q.getD i d :: T i).getLast (List.cons_ne_nil _ _)))).card ≤
      Q.length * m := by
  let Fu : ℕ → ℕ := fun i =>
    (H.filter (G.Adj ((Q.getD i d :: T i).getLast (List.cons_ne_nil _ _)))).card
  let c : ℕ → ℕ := fun i => ((Finset.range Q.length).filter
    (fun j => T j ≠ [] ∧ G.Adj (Q.getD i d) ((T j).headD d))).card
  let Cc : ℕ → ℕ := fun i => if T i = [] then c i else 0
  let D : ℕ → ℕ := fun i => if T i = [] then 0 else nQ G Q d ((T i).headD d)
  have step1 : ∀ i < Q.length, T i = [] → Fu i ≤ nQ G Q d (Q.getD i d) + c i := by
    intro i hi hTi
    have hu : (Q.getD i d :: T i).getLast (List.cons_ne_nil _ _) = Q.getD i d := by
      simp [hTi]
    simp only [Fu, hu]
    calc _ ≤ (((Finset.range Q.length).filter (fun t => G.Adj (Q.getD i d) (Q.getD t d))).image
              (fun t => Q.getD t d) ∪ ((Finset.range Q.length).filter
              (fun j => T j ≠ [] ∧ G.Adj (Q.getD i d) ((T j).headD d))).image
              (fun j => (T j).headD d)).card := Finset.card_le_card (fun w hw => by
            rw [Finset.mem_filter] at hw
            rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
            rcases nbr_v hm hi hTi hw.1 hw.2 with hwQ | ⟨j, hj, hwj⟩
            · obtain ⟨t, ht, rfl⟩ := exists_getD (d := d) hwQ
              exact Or.inl ⟨t, Finset.mem_filter.2 ⟨Finset.mem_range.2 ht, hw.2⟩, rfl⟩
            · have hne : T j ≠ [] := by intro h; rw [h] at hwj; simp at hwj
              have hx : (T j).headD d = w := by
                cases hT : T j with
                | nil => exact absurd hT hne
                | cons a l => rw [hT] at hwj; simpa using hwj
              refine Or.inr ⟨j, ?_, hx⟩
              simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨hj, hne, by rw [hx]; exact hw.2⟩)
      _ ≤ _ := (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le
              Finset.card_image_le)
  have step2 : ∑ i ∈ Finset.range Q.length, Cc i ≤ ∑ i ∈ Finset.range Q.length, D i := by
    calc ∑ i ∈ Finset.range Q.length, Cc i ≤ ∑ i ∈ Finset.range Q.length, c i :=
          Finset.sum_le_sum (fun i _ => by simp only [Cc]; split_ifs <;> omega)
      _ = ∑ i ∈ Finset.range Q.length, ∑ j ∈ Finset.range Q.length,
            if T j ≠ [] ∧ G.Adj (Q.getD i d) ((T j).headD d) then 1 else 0 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [c, Finset.card_filter]
      _ = ∑ j ∈ Finset.range Q.length, ∑ i ∈ Finset.range Q.length,
            if T j ≠ [] ∧ G.Adj (Q.getD i d) ((T j).headD d) then 1 else 0 := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [D]
          by_cases hTj : T j = []
          · simp [hTj]
          · simp only [hTj, if_false, ne_eq, not_false_eq_true, true_and]
            rw [nQ, Finset.card_filter]
            exact Finset.sum_congr rfl (fun i _ => by
              split_ifs with h1 h2 h2
              · rfl
              · exact absurd h1.symm h2
              · exact absurd h2.symm h1
              · rfl)
  have step3 : ∀ i ∈ Finset.range Q.length, Fu i + D i ≤ m + Cc i := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    simp only [D, Cc]
    by_cases hTi : T i = []
    · simp only [hTi, if_true]
      have := step1 i hi' hTi
      have := hA i hi' hTi
      omega
    · simp only [hTi, if_false]
      have := hB i hi' hTi
      simp only [Fu]; omega
  have h3 := Finset.sum_le_sum step3
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at h3
  have : ∑ i ∈ Finset.range Q.length, Fu i ≤ Q.length * m := by omega
  exact this

end Helpers

/-- Residual lemma: pendant paths `R i` off a longest path `Q` of `H` whose ends `u i` have small
`H`-degree sum. `hcyc`: every cycle (closed path list) in `H` has at most `L` vertices. -/
theorem residual [DecidableRel G.Adj] (H : Finset V) (Q : List V) (hQ : VL G H Q) (hQ1 : Q ≠ [])
    (hmax : ∀ l, VL G H l → l.length ≤ Q.length) (L : ℕ) (hL : 2 ≤ L)
    (hcyc : ∀ l, VL G H l → 3 ≤ l.length → (∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y) →
      l.length ≤ L) :
    ∃ (R : ℕ → List V) (u : ℕ → V),
      (∀ i < Q.length, VL G H (R i) ∧ (R i).head? = Q[i]? ∧ (R i).getLast? = some (u i) ∧
          ∀ x ∈ R i, x ∈ Q → Q[i]? = some x) ∧
      (∀ i < Q.length, ∀ j < Q.length, i ≠ j → ∀ x ∈ R i, x ∉ R j) ∧
      (∑ i ∈ Finset.range Q.length, (H.filter (G.Adj (u i))).card) ≤ Q.length * (Q.length - 1) ∧
      (∑ i ∈ Finset.range Q.length, (H.filter (G.Adj (u i))).card) ≤ Q.length * (2 * L - 2) := by
  have hs : Std G H Q := ⟨hQ, hmax⟩
  have hc : CycB G H L := hcyc
  obtain ⟨d⟩ : Nonempty V := ⟨Q.head hQ1⟩
  obtain ⟨T, hm⟩ := exists_maxSys G H Q d
  obtain ⟨hoff, hch, hdis⟩ := hm.1
  have hu : ∀ i, (Q.getD i d :: T i).getLast? =
      some ((Q.getD i d :: T i).getLast (List.cons_ne_nil _ _)) :=
    fun i => List.getLast?_eq_getLast _
  have hBx : ∀ i < Q.length, T i ≠ [] →
      2 * nQ G Q d ((T i).headD d) ≤ Q.length - 1 ∧ nQ G Q d ((T i).headD d) ≤ L - 1 :=
    fun i hi hTi => deg_x hs hL hc d ((hoff i hi).2.1 _ (headD_mem hTi d))
      ((hoff i hi).2.2 _ (headD_mem hTi d))
  refine ⟨fun i => Q.getD i d :: T i,
    fun i => (Q.getD i d :: T i).getLast (List.cons_ne_nil _ _), ?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨⟨List.nodup_cons.2 ⟨fun h => (hoff i hi).2.2 _ h (getD_mem hi), (hoff i hi).1⟩,
      hch i hi, fun z hz => ?_⟩, ?_, hu i, fun x hx hxQ => ?_⟩
    · rcases List.mem_cons.1 hz with h | h
      · rw [h]; exact hQ.2.2 _ (getD_mem hi)
      · exact (hoff i hi).2.1 z h
    · rw [List.head?_cons]; exact (getElem?_getD hi).symm
    · rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact getElem?_getD hi
      · exact absurd hxQ ((hoff i hi).2.2 x h)
  · intro i hi j hj hij x hxi hxj
    simp only at hxi hxj
    rcases List.mem_cons.1 hxi with h1 | h1 <;> rcases List.mem_cons.1 hxj with h2 | h2
    · exact hij (getD_inj hQ.1 hi hj (h1.symm.trans h2))
    · exact (hoff j hj).2.2 x h2 (h1 ▸ getD_mem hi)
    · exact (hoff i hi).2.2 x h1 (h2 ▸ getD_mem hj)
    · exact hdis i hi j hj hij x h1 h2
  · refine sum_bound hm _ (fun i hi _ => (deg_q hs hL hc d hi).1) (fun i hi hTi => ?_)
    have h1 := hBx i hi hTi
    have h2 := deg_u hs hL hc hm hi hTi (hu i)
    omega
  · refine sum_bound hm _ (fun i hi _ => (deg_q hs hL hc d hi).2) (fun i hi hTi => ?_)
    have h1 := hBx i hi hTi
    have h2 := deg_u hs hL hc hm hi hTi (hu i)
    omega


/-! ## Closed lists and cycles -/

/-- A closed list: consecutive entries are adjacent and so are the last and the first entry. -/
def CL (G : SimpleGraph V) (l : List V) : Prop :=
  l.IsChain G.Adj ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y

lemma walk_of_chain : ∀ (l : List V) (x : V), (x :: l).IsChain G.Adj →
    ∃ y, ∃ p : G.Walk x y, p.support = x :: l ∧ (x :: l).getLast? = some y
  | [], x, _ => ⟨x, Walk.nil, rfl, rfl⟩
  | z :: l, x, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨y, p, hp, hl⟩ := walk_of_chain l z h.2
    exact ⟨y, Walk.cons h.1 p, by simp [hp], by simpa using hl⟩

lemma start_edge {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (h : s(u, w) ∈ p.edges) :
    w = p.getVert 1 := by
  cases p with
  | nil => simp at h
  | @cons _ x _ hadj q =>
    rw [Walk.edges_cons, List.mem_cons] at h
    rw [Walk.cons_isPath_iff] at hp
    rcases h with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · simp [h2]
      · exact absurd h1 (G.ne_of_adj hadj)
    · exact absurd (q.fst_mem_support_of_mem_edges h) hp.2

/-- A closed nodup list with at least three entries is a cycle of that length. -/
lemma cycle_of_CL (l : List V) (hnd : l.Nodup) (hc : CL G l) (h3 : 3 ≤ l.length) :
    ∃ a, ∃ w : G.Walk a a, w.IsCycle ∧ w.length = l.length := by
  obtain _ | ⟨x, t⟩ := l
  · simp at h3
  obtain ⟨y, p, hp, hl⟩ := walk_of_chain t x hc.1
  have hyx : G.Adj y x := hc.2 y hl x rfl
  have hpath : p.IsPath := Walk.IsPath.mk' (by rw [hp]; exact hnd)
  have hlen : p.length + 1 = (x :: t).length := by
    rw [← hp, Walk.length_support]
  refine ⟨y, Walk.cons hyx p, ?_, by simp [hlen]⟩
  rw [Walk.cons_isCycle_iff]
  refine ⟨hpath, fun he => ?_⟩
  rw [Sym2.eq_swap] at he
  have h1 := start_edge p hpath he
  have hy : p.getVert p.length = y := p.getVert_length
  have := hpath.getVert_injOn (show 1 ∈ {i | i ≤ p.length} by simp; omega)
    (show p.length ∈ {i | i ≤ p.length} by simp) (by rw [hy, ← h1])
  omega

lemma cycle_length_le {a : V} (w : G.Walk a a) (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have h1 := hw.support_nodup
  have h2 : w.support.tail.length = w.length := by
    rw [List.length_tail, Walk.length_support]; simp
  rw [← h2]
  exact h1.length_le_card

lemma le_circumference [DecidableRel G.Adj] {a : V} (w : G.Walk a a) (hw : w.IsCycle) :
    w.length ≤ G.circumference := by
  apply le_csSup
  · exact ⟨Fintype.card V, by rintro m ⟨b, w', hw', rfl⟩; exact cycle_length_le w' hw'⟩
  · exact ⟨a, w, hw, rfl⟩

/-! ## The cycle as a periodic sequence -/

/-- `f` is a `c`-periodic enumeration of a longest cycle of length `c`. -/
structure Cy (G : SimpleGraph V) (c : ℕ) (f : ℕ → V) : Prop where
  three : 3 ≤ c
  per : ∀ t, f (t + c) = f t
  adj : ∀ t, G.Adj (f t) (f (t + 1))
  inj : ∀ i j, i < c → j < c → f i = f j → i = j
  long : ∀ l : List V, l.Nodup → CL G l → l.length ≤ c

variable {c : ℕ} {f : ℕ → V}

lemma Cy.mod (hD : Cy G c f) (t : ℕ) : f t = f (t % c) := by
  conv_lhs => rw [← Nat.mod_add_div t c]
  induction t / c with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, hD.per, ih]

lemma Cy.per' (hD : Cy G c f) (t k : ℕ) : f (t + c * k) = f t := by
  rw [hD.mod, Nat.add_mul_mod_self_left, ← hD.mod]

lemma Cy.eq_iff (hD : Cy G c f) (i j : ℕ) : f i = f j ↔ i % c = j % c := by
  have hc : 0 < c := by have := hD.three; omega
  constructor
  · intro h
    rw [hD.mod i, hD.mod j] at h
    exact hD.inj _ _ (Nat.mod_lt _ hc) (Nat.mod_lt _ hc) h
  · intro h
    rw [hD.mod i, hD.mod j, h]

lemma Cy.ne_of_window (hD : Cy G c f) {b i j : ℕ} (hi1 : b ≤ i) (hi2 : i < b + c) (hj1 : b ≤ j)
    (hj2 : j < b + c) (hij : i ≠ j) : f i ≠ f j := by
  intro h
  rw [hD.eq_iff] at h
  have hc : 0 < c := by have := hD.three; omega
  rcases Nat.lt_or_ge i j with hl | hl
  · have : (j - i) % c = 0 := by
      have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
      exact this
    have h1 : 0 < j - i := by omega
    have h2 : j - i < c := by omega
    rw [Nat.mod_eq_of_lt h2] at this
    omega
  · have : (i - j) % c = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
    have h1 : 0 < i - j := by omega
    have h2 : i - j < c := by omega
    rw [Nat.mod_eq_of_lt h2] at this
    omega

/-- The list `f s, f (s+1), …, f (s+k-1)`. -/
def up (f : ℕ → V) (s k : ℕ) : List V := (List.range' s k).map f

/-- The list `f (s+k-1), …, f s`. -/
def dn (f : ℕ → V) (s k : ℕ) : List V := ((List.range' s k).map f).reverse

lemma chain_up (hD : Cy G c f) (s k : ℕ) : (up f s k).IsChain G.Adj := by
  induction k generalizing s with
  | zero => simp [up]
  | succ k ih =>
    cases k with
    | zero => simp [up]
    | succ k =>
      have := ih (s + 1)
      simp only [up, List.range'_succ, List.map_cons] at this ⊢
      exact List.IsChain.cons_cons (hD.adj s) this

lemma chain_dn (hD : Cy G c f) (s k : ℕ) : (dn f s k).IsChain G.Adj := by
  unfold dn
  rw [List.isChain_reverse]
  exact (chain_up hD s k).imp (fun _ _ h => h.symm)

@[simp] lemma up_length (s k : ℕ) : (up f s k).length = k := by simp [up]
@[simp] lemma dn_length (s k : ℕ) : (dn f s k).length = k := by simp [dn]

lemma up_head (s k : ℕ) : (up f s (k + 1)).head? = some (f s) := by
  simp [up, List.range'_succ]
lemma up_last (s k : ℕ) : (up f s (k + 1)).getLast? = some (f (s + k)) := by
  simp [up, List.getLast?_map, List.getLast?_range']
lemma dn_head (s k : ℕ) : (dn f s (k + 1)).head? = some (f (s + k)) := by
  simp [dn, List.head?_reverse, List.getLast?_map, List.getLast?_range']
lemma dn_last (s k : ℕ) : (dn f s (k + 1)).getLast? = some (f s) := by
  simp [dn, List.getLast?_reverse, List.range'_succ]

lemma mem_up {s k : ℕ} {x : V} : x ∈ up f s k ↔ ∃ i, s ≤ i ∧ i < s + k ∧ f i = x := by
  simp only [up, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; exact ⟨i, h1, h2, rfl⟩
  · rintro ⟨i, h1, h2, rfl⟩; exact ⟨i, ⟨h1, h2⟩, rfl⟩

lemma mem_dn {s k : ℕ} {x : V} : x ∈ dn f s k ↔ ∃ i, s ≤ i ∧ i < s + k ∧ f i = x := by
  rw [dn, List.mem_reverse]; exact mem_up

lemma nodup_up (hD : Cy G c f) {s k : ℕ} (hk : k ≤ c) : (up f s k).Nodup := by
  unfold up
  rw [List.nodup_map_iff_inj_on List.nodup_range']
  intro i hi j hj hij
  simp only [List.mem_range'_1] at hi hj
  by_contra hne
  exact hD.ne_of_window (b := s) (by omega) (by omega) (by omega) (by omega) hne hij

lemma nodup_dn (hD : Cy G c f) {s k : ℕ} (hk : k ≤ c) : (dn f s k).Nodup := by
  rw [dn, List.nodup_reverse]; exact nodup_up hD hk



/-! ## Rerouting -/

lemma nodup_map_window (hD : Cy G c f) (I : List ℕ) (b : ℕ) (hI : ∀ i ∈ I, b ≤ i ∧ i < b + c)
    (hnd : I.Nodup) : (I.map f).Nodup := by
  rw [List.nodup_map_iff_inj_on hnd]
  intro i hi j hj hij
  by_contra hne
  exact hD.ne_of_window (hI i hi).1 (hI i hi).2 (hI j hj).1 (hI j hj).2 hne hij

/-- Any closed list made of off-cycle vertices `O` and cycle vertices indexed by a window
`I` is at most as long as the cycle. -/
lemma reroute (hD : Cy G c f) (l O : List V) (I : List ℕ) (b : ℕ) (hperm : l.Perm (O ++ I.map f))
    (hcl : CL G l) (hO : O.Nodup) (hOff : ∀ x ∈ O, ∀ t, f t ≠ x)
    (hI : ∀ i ∈ I, b ≤ i ∧ i < b + c) (hInd : I.Nodup) : O.length + I.length ≤ c := by
  have hnd : l.Nodup := by
    rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨hO, nodup_map_window hD I b hI hInd, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact hOff x hx i hxy.symm
  have := hD.long l hnd hcl
  rw [hperm.length_eq, List.length_append, List.length_map] at this
  exact this

/-- Off-cycle walk data: a nonempty nodup chain avoiding the cycle. -/
structure OffL (G : SimpleGraph V) (f : ℕ → V) (X : List V) : Prop where
  ne : X ≠ []
  nd : X.Nodup
  ch : X.IsChain G.Adj
  off : ∀ x ∈ X, ∀ t, f t ≠ x

lemma up_succ_eq (s k : ℕ) : up f s (k + 1) = up f s k ++ [f (s + k)] := by
  simp [up, List.range'_concat]

/-- `R1`: an off-cycle path from `f b` to `f (b+j)` forces the forward arc to be long. -/
lemma R1 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j : ℕ} (hj : 1 ≤ j) (hjc : j ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j))) :
    X.length + 1 ≤ j := by
  obtain ⟨k, hk⟩ : ∃ k, c - j = k := ⟨_, rfl⟩
  have key := reroute hD (X ++ up f (b + j) (k + 1)) X (List.range' (b + j) (k + 1)) (b + 1)
    (by simp [up]) ?_ hX.nd hX.off ?_ List.nodup_range'
  · simp at key; omega
  · refine ⟨List.IsChain.append hX.ch (chain_up hD _ _) ?_, ?_⟩
    · intro x hx y hy
      rw [up_head] at hy; cases hy; exact h2 x hx
    · intro x hx y hy
      rw [List.getLast?_append, up_last] at hx
      simp at hx; subst hx
      have hb : f (b + j + k) = f b := by
        rw [show b + j + k = b + c by omega, hD.per]
      rw [hb]
      rw [List.head?_append] at hy
      obtain ⟨x0, l0, hx0⟩ := List.ne_nil_iff_exists_cons.mp hX.ne
      rw [hx0] at hy h1; simp at hy h1; subst hy; exact h1
  · intro i hi; simp at hi; omega


lemma OffL.head (hX : OffL G f X) : ∃ x0, X.head? = some x0 := by
  obtain ⟨x0, l0, rfl⟩ := List.ne_nil_iff_exists_cons.mp hX.ne
  exact ⟨x0, rfl⟩

lemma closing_aux {l : List V} {X : List V} (hX : OffL G f X) {v : V}
    (hl : l.getLast? = some v) (h1 : ∀ z ∈ X.head?, G.Adj v z) :
    ∀ x ∈ (X ++ l).getLast?, ∀ y ∈ (X ++ l).head?, G.Adj x y := by
  intro x hx y hy
  rw [List.getLast?_append, hl] at hx
  simp at hx; subst hx
  obtain ⟨x0, hx0⟩ := hX.head
  rw [List.head?_append, hx0] at hy
  simp at hy; subst hy
  exact h1 _ hx0

/-- `R3`: the two-successor crossing. -/
lemma R3 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j p q : ℕ} (hj : 1 ≤ j)
    (hjp : j + 1 ≤ p) (hpq : p < q) (hqc : q ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) (f (b + p))) (h4 : G.Adj (f (b + j + 1)) (f (b + q))) :
    X.length + p + 1 ≤ q := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, p - (j' + 1) = d + 1 := ⟨p - j' - 2, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - q = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ (dn f (b + j' + 1 + 1) (d + 1) ++ up f (b + q) (k + 1)))) X
    ((List.range' (b + 1) (j' + 1)).reverse ++ ((List.range' (b + j' + 1 + 1) (d + 1)).reverse
      ++ List.range' (b + q) (k + 1))) (b + 1)
    (by simp [up, dn, List.map_reverse]) ?_ hX.nd hX.off ?_ ?_
  · simp at key; omega
  · have hbc : f (b + q + k) = f b := by rw [show b + q + k = b + c by omega, hD.per]
    refine ⟨?_, closing_aux hX (by simp [up_last, hbc]) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) ?_ ?_
      · refine List.IsChain.append (chain_dn hD _ _) (chain_up hD _ _) ?_
        intro x hx y hy
        rw [dn_last] at hx; rw [up_head] at hy; cases hx; cases hy
        exact h4
      · intro x hx y hy
        rw [dn_last] at hx; cases hx
        rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
        rw [show b + j' + 1 + 1 + d = b + p by omega]; exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1,
      List.mem_append]
    refine ⟨List.nodup_range', ⟨List.nodup_range', List.nodup_range', ?_⟩, ?_⟩
    · intro a ha b' hb'; omega
    · intro a ha b' hb'; omega

/-- `R4`: an attachment followed by a successor chord. -/
lemma R4 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j q : ℕ} (hj : 1 ≤ j)
    (hjq : j < q) (hqc : q ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) (f (b + q))) :
    X.length + j + 1 ≤ q := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - q = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ up f (b + q) (k + 1))) X
    ((List.range' (b + 1) (j' + 1)).reverse ++ List.range' (b + q) (k + 1)) (b + 1)
    (by simp [up, dn, List.map_reverse]) ?_ hX.nd hX.off ?_ ?_
  · simp at key; omega
  · have hbc : f (b + q + k) = f b := by rw [show b + q + k = b + c by omega, hD.per]
    refine ⟨?_, closing_aux hX (by simp [up_last, hbc]) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) (chain_up hD _ _) ?_
      intro x hx y hy
      rw [dn_last] at hx; rw [up_head] at hy; cases hx; cases hy
      exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1]
    refine ⟨List.nodup_range', List.nodup_range', ?_⟩
    intro a ha b' hb'; omega

/-- `R22`: two successors with a common off-cycle neighbour `r`. -/
lemma R22 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {r : V} (hr : ∀ t, f t ≠ r)
    (hrX : r ∉ X) {b j : ℕ} (hj : 1 ≤ j) (hjc : j + 1 ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) r) (h4 : G.Adj r (f (b + j + 1))) : False := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - (j' + 1) - 1 = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ (r :: up f (b + j' + 1 + 1) (k + 1)))) (X ++ [r])
    ((List.range' (b + 1) (j' + 1)).reverse ++ List.range' (b + j' + 1 + 1) (k + 1)) (b + 1)
    ?_ ?_ ?_ ?_ ?_ ?_
  · simp at key; omega
  · simp only [up, dn, List.map_append, List.map_reverse, List.append_assoc]
    refine List.Perm.append_left X ?_
    simp only [List.singleton_append]
    exact List.perm_middle
  · have hbc : f (b + j' + 1 + 1 + k) = f b := by
      rw [show b + j' + 1 + 1 + k = b + c by omega, hD.per]
    have hl : (r :: up f (b + j' + 1 + 1) (k + 1)).getLast? = some (f b) := by
      rw [List.getLast?_cons, up_last]; simp [hbc]
    refine ⟨?_, closing_aux hX (by rw [List.getLast?_append, hl]; simp) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) ?_ ?_
      · rw [List.isChain_cons]
        refine ⟨?_, chain_up hD _ _⟩
        intro y hy; rw [up_head] at hy; cases hy; exact h4
      · intro x hx y hy
        rw [dn_last] at hx; cases hx; simp at hy; subst hy; exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · rw [List.nodup_append]
    refine ⟨hX.nd, List.nodup_singleton r, ?_⟩
    intro x hx y hy hxy; simp at hy; subst hy; subst hxy; exact hrX hx
  · intro x hx t; simp at hx; rcases hx with hx | rfl
    · exact hX.off x hx t
    · exact hr t
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1]
    refine ⟨List.nodup_range', List.nodup_range', ?_⟩
    intro a ha b' hb'; omega



/-! ## The counting lemma on one arc -/

/-- An off-cycle path from `x` to `y` with at least `K` interior vertices. -/
def PH (G : SimpleGraph V) (f : ℕ → V) (x y : V) (K : ℕ) : Prop :=
  ∃ X : List V, OffL G f X ∧ K ≤ X.length ∧ (∀ z ∈ X.head?, G.Adj x z) ∧
    (∀ z ∈ X.getLast?, G.Adj z y)

lemma PH.symm {x y : V} {K : ℕ} (h : PH G f x y K) : PH G f y x K := by
  obtain ⟨X, hX, hK, h1, h2⟩ := h
  refine ⟨X.reverse, ⟨by simpa using hX.ne, List.nodup_reverse.mpr hX.nd, ?_, ?_⟩, by simpa, ?_, ?_⟩
  · rw [List.isChain_reverse]; exact hX.ch.imp (fun _ _ h => h.symm)
  · intro x hx; exact hX.off x (List.mem_reverse.mp hx)
  · intro z hz; rw [List.head?_reverse] at hz; exact (h2 z hz).symm
  · intro z hz; rw [List.getLast?_reverse] at hz; exact (h1 z hz).symm

lemma PH.mono {x y : V} {K K' : ℕ} (h : PH G f x y K) (hK : K' ≤ K) : PH G f x y K' := by
  obtain ⟨X, hX, hk, h1, h2⟩ := h; exact ⟨X, hX, by omega, h1, h2⟩

lemma Cy.shift (hD : Cy G c f) {s t : ℕ} (h : s = t + c) : f s = f t := by
  rw [h, hD.per]
/-! ## The off-cycle component -/

/-- A path list inside `H` from `x` to `y`. -/
def HP (G : SimpleGraph V) (H : Finset V) (x y : V) (X : List V) : Prop :=
  X.Nodup ∧ X.IsChain G.Adj ∧ (∀ z ∈ X, z ∈ H) ∧ X.head? = some x ∧ X.getLast? = some y

/-- `H` is a component of `G - C`. -/
structure Comp (G : SimpleGraph V) (f : ℕ → V) (H : Finset V) : Prop where
  off : ∀ x ∈ H, ∀ t, f t ≠ x
  cl : ∀ x ∈ H, ∀ y, G.Adj x y → y ∈ H ∨ ∃ t, f t = y
  conn : ∀ x ∈ H, ∀ y ∈ H, ∃ X, HP G H x y X

variable {H : Finset V}

lemma HP.offL (hC : Comp G f H) {x y : V} {X : List V} (h : HP G H x y X) : OffL G f X :=
  ⟨by rintro rfl; simp [HP] at h, h.1, h.2.1, fun z hz => hC.off z (h.2.2.1 z hz)⟩

lemma HP.two_le {x y : V} {X : List V} (h : HP G H x y X) (hxy : x ≠ y) : 2 ≤ X.length := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  match X, h1, h2 with
  | [a], h1, h2 => simp at h1 h2; exact absurd (h1.symm.trans h2) hxy
  | a :: b :: l, _, _ => simp

lemma ph_of (hC : Comp G f H) {a b z z' : V} (hz : z ∈ H) (hz' : z' ∈ H) (ha : G.Adj a z)
    (hb : G.Adj b z') : PH G f a b 1 := by
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact ⟨X, hX.offL hC, by have := (hX.offL hC).ne; exact List.length_pos_iff.mpr this,
    by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact ha,
    by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hb.symm⟩

lemma ph_two (hC : Comp G f H) {a b z z' : V} (hz : z ∈ H) (hz' : z' ∈ H) (hzz : z ≠ z')
    (ha : G.Adj a z) (hb : G.Adj b z') : PH G f a b 2 := by
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact ⟨X, hX.offL hC, hX.two_le hzz,
    by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact ha,
    by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hb.symm⟩

/-- `f s` is an attachment vertex of `H`. -/
def Att (G : SimpleGraph V) (f : ℕ → V) (H : Finset V) (s : ℕ) : Prop := ∃ z ∈ H, G.Adj (f s) z

lemma G1 (hD : Cy G c f) (hC : Comp G f H) {s : ℕ} (hs : Att G f H s) :
    ∀ z ∈ H, ¬ G.Adj (f (s + 1)) z := by
  intro z hz hadj
  obtain ⟨z0, hz0, ha⟩ := hs
  obtain ⟨X, hX, hK, h1, h2⟩ := ph_of hC hz0 hz ha hadj
  have := R1 hD hX (b := s) (j := 1) le_rfl (by have := hD.three; omega) h1 h2
  omega

lemma G2 (hD : Cy G c f) (hC : Comp G f H) {s j : ℕ} (hs : Att G f H s)
    (hsj : Att G f H (s + j)) (hj : 1 ≤ j) (hjc : j < c) :
    ¬ G.Adj (f (s + 1)) (f (s + j + 1)) := by
  intro hadj
  obtain ⟨z, hz, hsz⟩ := hs
  rcases Nat.lt_or_ge (j + 1) c with h | h
  · obtain ⟨z', hz', hsz'⟩ := hsj
    obtain ⟨X, hX, hK, h1, h2⟩ := ph_of hC hz hz' hsz hsz'
    have := R3 hD hX (b := s) (j := j) (p := j + 1) (q := j + 2) hj le_rfl (by omega) (by omega)
      h1 h2 (by simpa [Nat.add_assoc] using hadj) (by rw [Nat.add_assoc]; exact (hD.adj _))
    omega
  · have : f (s + j + 1) = f s := hD.shift (by omega)
    exact G1 hD hC hsj z hz (by rw [this]; exact hsz)

lemma G3 (hD : Cy G c f) (hC : Comp G f H) {s j : ℕ} (hs : Att G f H s)
    (hsj : Att G f H (s + j)) (hj : 1 ≤ j) (hjc : j < c) {r : V} (hrH : r ∉ H)
    (hrC : ∀ t, f t ≠ r) (h3 : G.Adj (f (s + 1)) r) (h4 : G.Adj r (f (s + j + 1))) : False := by
  obtain ⟨z, hz, hsz⟩ := hs
  obtain ⟨z', hz', hsz'⟩ := hsj
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact R22 hD (hX.offL hC) hrC (fun h => hrH (hX.2.2.1 r h)) (b := s) (j := j) hj (by omega)
    (by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact hsz)
    (by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hsz'.symm) h3 h4


lemma att_shift (hD : Cy G c f) {s t : ℕ} (h : s = t + c) (ht : Att G f H t) : Att G f H s := by
  obtain ⟨z, hz, h⟩ := ht; exact ⟨z, hz, by rw [hD.shift (by omega : s = t + c)]; exact h⟩

lemma split_Ioc (P : ℕ → Prop) [DecidablePred P] {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) :
    ((Finset.Ioc a d).filter P).card =
      ((Finset.Ioc a b).filter P).card + ((Finset.Ioc b d).filter P).card := by
  simp only [Finset.card_filter]
  exact (Finset.sum_Ioc_consecutive _ hab hbd).symm
/-! ## The four-vertex degree count -/

lemma Cy.exists_window (hD : Cy G c f) (b t : ℕ) : ∃ t', b < t' ∧ t' ≤ b + c ∧ f t' = f t := by
  have hc : 0 < c := by have := hD.three; omega
  set m := t + c * (b + 1) - (b + 1)
  have hm : b + 1 ≤ t + c * (b + 1) := by nlinarith
  refine ⟨b + 1 + m % c, by omega, by have := Nat.mod_lt m hc; omega, ?_⟩
  have e1 : f (b + 1 + m % c + c * (m / c)) = f (b + 1 + m % c) := hD.per' _ _
  have e2 : b + 1 + m % c + c * (m / c) = t + c * (b + 1) := by
    have := Nat.mod_add_div m c; omega
  rw [← e1, e2, hD.per']

lemma Cy.mem_cset (hD : Cy G c f) (t : ℕ) : f t ∈ (Finset.range c).image f := by
  obtain ⟨t', h1, h2, h3⟩ := hD.exists_window 0 t
  rw [Finset.mem_image]
  refine ⟨t' % c, Finset.mem_range.mpr (Nat.mod_lt _ (by have := hD.three; omega)), ?_⟩
  rw [← hD.mod, h3]

lemma card_on_cycle [DecidableRel G.Adj] (hD : Cy G c f) (b : ℕ) (x : V) :
    ((Finset.Ioc b (b + c)).filter (fun t => G.Adj x (f t))).card =
      ((G.neighborFinset x).filter (· ∈ (Finset.range c).image f)).card := by
  have hinj : Set.InjOn f ((Finset.Ioc b (b + c)).filter (fun t => G.Adj x (f t))) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hi hj
    by_contra hne
    exact hD.ne_of_window (b := b + 1) (by omega) (by omega) (by omega) (by omega) hne hij
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc, mem_neighborFinset]
  constructor
  · rintro ⟨t, ⟨-, h⟩, rfl⟩; exact ⟨h, Finset.mem_image.mp (hD.mem_cset t)⟩
  · rintro ⟨h, hy⟩
    obtain ⟨t, -, rfl⟩ := hy
    obtain ⟨t', h1, h2, h3⟩ := hD.exists_window b t
    exact ⟨t', ⟨⟨h1, h2⟩, by rw [h3]; exact h⟩, h3⟩

lemma card_cset (hD : Cy G c f) : ((Finset.range c).image f).card = c := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hD.inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-! ## Structure inside `H` -/


lemma VL.length_le {P : List V} (h : VL G H P) : P.length ≤ H.card := by
  rw [← List.toFinset_card_of_nodup h.1]
  exact Finset.card_le_card (fun z hz => h.2.2 z (List.mem_toFinset.mp hz))

/-- A path list in `H` whose first vertex has all its `H`-neighbours on the list. -/
lemma exists_headmax {x : V} (hx : x ∈ H) :
    ∃ v Q, VL G H (v :: Q) ∧ ∀ u ∈ H, G.Adj v u → u ∈ v :: Q := by
  suffices ∀ k, ∀ v Q, VL G H (v :: Q) → H.card - (v :: Q).length ≤ k →
      ∃ v' Q', VL G H (v' :: Q') ∧ ∀ u ∈ H, G.Adj v' u → u ∈ v' :: Q' from
    this _ x [] ⟨List.nodup_singleton x, List.isChain_singleton x, by simpa using hx⟩ le_rfl
  intro k
  induction k with
  | zero =>
    intro v Q hP hk
    refine ⟨v, Q, hP, fun u hu huv => ?_⟩
    by_contra hn
    have : VL G H (u :: v :: Q) := ⟨List.nodup_cons.mpr ⟨hn, hP.1⟩,
      List.IsChain.cons_cons huv.symm hP.2.1, by
        intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact hu
        · exact hP.2.2 z hz⟩
    have := this.length_le; simp at this hk; omega
  | succ k ih =>
    intro v Q hP hk
    by_cases hmax : ∀ u ∈ H, G.Adj v u → u ∈ v :: Q
    · exact ⟨v, Q, hP, hmax⟩
    · push_neg at hmax
      obtain ⟨u, hu, huv, hn⟩ := hmax
      exact ih u (v :: Q) ⟨List.nodup_cons.mpr ⟨hn, hP.1⟩, List.IsChain.cons_cons huv.symm hP.2.1, by
        intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact hu
        · exact hP.2.2 z hz⟩ (by simp at hk ⊢; omega)

lemma HP.three_le {x y : V} {X : List V} (h : HP G H x y X) (hxy : ¬ G.Adj x y) (hne : x ≠ y) :
    3 ≤ X.length := by
  obtain ⟨-, hch, -, h1, h2⟩ := h
  match X, hch, h1, h2 with
  | [a], _, h1, h2 => simp at h1 h2; exact absurd (h1.symm.trans h2) hne
  | [a, b], hch, h1, h2 =>
    simp at h1 h2; subst h1; subst h2
    exact absurd (List.isChain_cons_cons.mp hch).1 hxy
  | a :: b :: d :: l, _, _, _ => simp

lemma HP_of_VL {P : List V} (h : VL G H P) {x y : V} (hx : P.head? = some x)
    (hy : P.getLast? = some y) : HP G H x y P := ⟨h.1, h.2.1, h.2.2, hx, hy⟩


/-! ## The shifted successor count

Attachments at positions `s 0 < s 1 < … < s (q-1)` with `s q = s 0 + c`, any two joined through
`H` by a path with at least `q - 1` interior vertices. On the arc `(s m, s (m+1)]` the cycle
neighbours of the successor `f (s i + 1)`, shifted by `σ i = (m - i) mod q`, are pairwise disjoint
(rerouting `R3`) and avoid the first slot, so the arc carries at most `s (m+1) - s m + q - 2` of
them. Summing over the `q` arcs gives `Σ d_C (f (s i + 1)) + 2 q ≤ c + q²`. -/

section count

variable [DecidableRel G.Adj]

/-- Cycle-neighbour positions of `x` in the window `(a, b]`. -/
def cn (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℕ → V) (x : V) (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter (fun t => G.Adj x (f t))

lemma cn_split (x : V) {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) :
    (cn G f x a d).card = (cn G f x a b).card + (cn G f x b d).card :=
  split_Ioc (fun t => G.Adj x (f t)) hab hbd

/-- The shift of index `i` on arc `m`. -/
def sh (q m i : ℕ) : ℕ := if i ≤ m then m - i else m + q - i

lemma sh_le {q m i : ℕ} (hm : m < q) (hi : i < q) : sh q m i ≤ q - 1 := by
  unfold sh; split_ifs <;> omega

lemma sh_eq_zero {q m i : ℕ} (hi : i < q) (h : sh q m i = 0) : i = m ∨ m < i ∧ False := by
  unfold sh at h; split_ifs at h with h1
  · left; omega
  · omega

lemma sh_inj {q m i j : ℕ} (hm : m < q) (hi : i < q) (hj : j < q) (h : sh q m i = sh q m j) :
    i = j := by
  unfold sh at h; split_ifs at h <;> omega

/-- The base position of attachment `i` seen from arc `m` (shifted by `c` when `i ≤ m`). -/
def bp (c : ℕ) (s : ℕ → ℕ) (m i : ℕ) : ℕ := if i ≤ m then s i + c else s i

lemma arc_bound (hD : Cy G c f) (hC : Comp G f H) {q m : ℕ} (hm : m < q) {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j ≤ q → s i < s j) (hq : s q = s 0 + c)
    (hatt : ∀ i < q, Att G f H (s i))
    (hph : ∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) (q - 1)) :
    (∑ i ∈ Finset.range q, (cn G f (f (s i + 1)) (s m) (s (m + 1))).card) + s m + 2 ≤
      s (m + 1) + q := by
  have hs0 : ∀ i, i ≤ q → s 0 ≤ s i := by
    intro i hi; rcases Nat.eq_zero_or_pos i with rfl | h
    · exact le_rfl
    · exact (hs 0 i h hi).le
  have hsq : ∀ i, i < q → s i < s 0 + c := by intro i hi; rw [← hq]; exact hs i q hi le_rfl
  have hmm : s m < s (m + 1) := hs m (m + 1) (by omega) (by omega)
  -- the shifted images
  set img : ℕ → Finset ℕ := fun i => (cn G f (f (s i + 1)) (s m) (s (m + 1))).image
    (· + sh q m i) with himg
  have hcard : ∀ i, (img i).card = (cn G f (f (s i + 1)) (s m) (s (m + 1))).card := by
    intro i; exact Finset.card_image_of_injective _ (add_left_injective _)
  have hsub : ∀ i ∈ Finset.range q, img i ⊆ Finset.Ioc (s m + 1) (s (m + 1) + q - 1) := by
    intro i hi y hy
    rw [Finset.mem_range] at hi
    simp only [himg, Finset.mem_image, cn, Finset.mem_filter, Finset.mem_Ioc] at hy
    obtain ⟨t, ⟨⟨ht1, ht2⟩, hadj⟩, rfl⟩ := hy
    have hle := sh_le hm hi
    rw [Finset.mem_Ioc]
    refine ⟨?_, by omega⟩
    by_cases h0 : sh q m i = 0
    · rcases sh_eq_zero hi h0 with rfl | ⟨-, hf⟩
      · rw [h0, Nat.add_zero]
        rcases Nat.lt_or_ge (s i + 1) t with h | h
        · exact h
        · exfalso; have : t = s i + 1 := by omega
          subst this; exact G.irrefl hadj
      · exact hf.elim
    · omega
  have hdisj : ∀ i ∈ (Finset.range q : Set ℕ), ∀ j ∈ (Finset.range q : Set ℕ), i ≠ j →
      Disjoint (img i) (img j) := by
    -- the collision lemma, ordered by shift
    have key : ∀ i j, i < q → j < q → sh q m i < sh q m j → ∀ t t', s m < t → t ≤ s (m + 1) →
        s m < t' → t' ≤ s (m + 1) → G.Adj (f (s i + 1)) (f t) → G.Adj (f (s j + 1)) (f t') →
        t + sh q m i = t' + sh q m j → False := by
      intro i j hi hj hlt t t' ht1 ht2 ht1' ht2' ha ha' heq
      have hlei := sh_le hm hi
      have hlej := sh_le hm hj
      -- bases
      set bi := bp c s m i with hbi
      set bj := bp c s m j with hbj
      have fbi : f bi = f (s i) := by
        simp only [hbi, bp]; split_ifs
        · exact hD.shift rfl
        · rfl
      have fbj : f bj = f (s j) := by
        simp only [hbj, bp]; split_ifs
        · exact hD.shift rfl
        · rfl
      have fbi1 : f (bi + 1) = f (s i + 1) := by
        simp only [hbi, bp]; split_ifs
        · exact hD.shift (by omega)
        · rfl
      have fbj1 : f (bj + 1) = f (s j + 1) := by
        simp only [hbj, bp]; split_ifs
        · exact hD.shift (by omega)
        · rfl
      have hord : bj < bi := by
        have hsij : ∀ a b, a < b → b < q → s a < s b := fun a b h hb => hs a b h (by omega)
        simp only [hbi, hbj, bp]
        unfold sh at hlt
        by_cases hi' : i ≤ m <;> by_cases hj' : j ≤ m <;>
          simp only [hi', hj', if_true, if_false] at hlt ⊢
        · have := hsij j i (by omega) hi; omega
        · have := hsq j hj; have := hs0 i (by omega); omega
        · omega
        · have := hsij j i (by omega) hi; omega
      have hbi_le : bi ≤ s m + c := by
        simp only [hbi, bp]; split_ifs with h
        · rcases Nat.lt_or_ge i m with h' | h'
          · have := hs i m h' (by omega); omega
          · have : i = m := by omega
            subst this; omega
        · have := hsq i hi; have := hs0 m (by omega); omega
      have ht_le : t ≤ bj := by
        simp only [hbj, bp]; split_ifs with h
        · have := hs0 j (by omega)
          have : s (m + 1) ≤ s q := by
            rcases Nat.lt_or_ge (m + 1) q with h' | h'
            · exact (hs _ _ h' le_rfl).le
            · rw [show m + 1 = q by omega]
          omega
        · have : s (m + 1) ≤ s j := by
            rcases Nat.lt_or_ge (m + 1) j with h' | h'
            · exact (hs _ _ h' (by omega)).le
            · rw [show m + 1 = j by omega]
          omega
      -- the path between the two attachments
      have hX : PH G f (f bj) (f bi) (q - 1) := by
        rw [fbi, fbj]
        rcases Nat.lt_or_ge i j with h | h
        · exact (hph i hi j hj h).symm
        · have hne : i ≠ j := fun h' => by subst h'; omega
          exact hph j hj i hi (by omega)
      obtain ⟨X, hXo, hXl, h1, h2⟩ := hX
      have := R3 hD hXo (b := bj) (j := bi - bj) (p := t' + c - bj) (q := t + c - bj)
        (by omega) (by omega) (by omega) (by omega) h1
        (by rw [show bj + (bi - bj) = bi by omega]; exact h2)
        (by rw [fbj1, show bj + (t' + c - bj) = t' + c by omega, hD.shift rfl]; exact ha')
        (by rw [show bj + (bi - bj) + 1 = bi + 1 by omega, fbi1,
              show bj + (t + c - bj) = t + c by omega, hD.shift rfl]; exact ha)
      omega
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [himg, Finset.mem_image, cn, Finset.mem_filter, Finset.mem_Ioc] at hy hy'
    obtain ⟨t, ⟨⟨ht1, ht2⟩, ha⟩, rfl⟩ := hy
    obtain ⟨t', ⟨⟨ht1', ht2'⟩, ha'⟩, heq⟩ := hy'
    rcases Nat.lt_trichotomy (sh q m i) (sh q m j) with h | h | h
    · exact key i j hi hj h t t' ht1 ht2 ht1' ht2' ha ha' heq.symm
    · exact hij (sh_inj hm hi hj h)
    · exact key j i hj hi h t' t ht1' ht2' ht1 ht2 ha' ha heq
  have hU := Finset.card_biUnion (s := Finset.range q) (t := img) hdisj
  have hU2 := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
  rw [Nat.card_Ioc] at hU2
  simp only [hcard] at hU
  omega

/-- The shifted successor count summed over all arcs. -/
lemma succ_count (hD : Cy G c f) (hC : Comp G f H) {q : ℕ} (hq1 : 1 ≤ q) {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j ≤ q → s i < s j) (hq : s q = s 0 + c)
    (hatt : ∀ i < q, Att G f H (s i))
    (hph : ∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) (q - 1)) :
    (∑ i ∈ Finset.range q, (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card) + 2 * q ≤ c + q * q := by
  have hmono : ∀ m, m ≤ q → s 0 ≤ s m := by
    intro m hm; rcases Nat.eq_zero_or_pos m with rfl | h
    · exact le_rfl
    · exact (hs 0 m h hm).le
  -- splitting each window into arcs
  have hsplit : ∀ x M, M ≤ q → (cn G f x (s 0) (s M)).card =
      ∑ m ∈ Finset.range M, (cn G f x (s m) (s (m + 1))).card := by
    intro x M
    induction M with
    | zero => intro _; simp [cn]
    | succ M ih =>
      intro hM
      rw [Finset.sum_range_succ, ← ih (by omega)]
      exact cn_split x (hmono M (by omega)) (hs M (M + 1) (by omega) hM).le
  have h1 : ∀ i, (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card =
      ∑ m ∈ Finset.range q, (cn G f (f (s i + 1)) (s m) (s (m + 1))).card := by
    intro i; rw [← hq]; exact hsplit _ q le_rfl
  simp only [h1]
  rw [Finset.sum_comm]
  have harc : ∀ m ∈ Finset.range q,
      (∑ i ∈ Finset.range q, (cn G f (f (s i + 1)) (s m) (s (m + 1))).card) + s m + 2 ≤
        s (m + 1) + q := fun m hm =>
    arc_bound hD hC (Finset.mem_range.mp hm) hs hq hatt hph
  have hsum := Finset.sum_le_sum harc
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have htel : ∑ m ∈ Finset.range q, s (m + 1) = (∑ m ∈ Finset.range q, s m) + s q - s 0 := by
    have e1 := Finset.sum_range_succ' (fun m => s m) q
    have e2 := Finset.sum_range_succ (fun m => s m) q
    omega
  have h0 : s 0 ≤ (∑ m ∈ Finset.range q, s m) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Finset.sum_range_succ']; omega
  rw [htel, hq] at hsum
  have : (∑ m ∈ Finset.range q, s m) + (s 0 + c) - s 0 = (∑ m ∈ Finset.range q, s m) + c := by
    omega
  rw [this] at hsum
  nlinarith

end count

/-! ## Degree sums: Lemma B (`q` successors) and Lemma A' (`q` successors and one vertex of `H`) -/

section degsum

variable [DecidableRel G.Adj]

/-- Vertices off the cycle and off `H`. -/
def Rest (c : ℕ) (f : ℕ → V) (H : Finset V) : Finset V :=
  Finset.univ.filter (fun y => y ∉ (Finset.range c).image f ∧ y ∉ H)

lemma offCs (hC : Comp G f H) : ∀ y ∈ H, y ∉ (Finset.range c).image f := by
  intro y hy hyC
  obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hyC
  exact hC.off y hy t ht

lemma deg_split (hC : Comp G f H) (x : V) : G.degree x =
    ((G.neighborFinset x).filter (· ∈ (Finset.range c).image f)).card +
      ((G.neighborFinset x).filter (· ∈ H)).card +
      ((G.neighborFinset x).filter (· ∈ Rest c f H)).card := by
  set Cs := (Finset.range c).image f with hCs
  rw [← card_neighborFinset_eq_degree,
    ← Finset.card_filter_add_card_filter_not (s := G.neighborFinset x) (· ∈ Cs)]
  have : ((G.neighborFinset x).filter (fun a => ¬ a ∈ Cs)) =
      ((G.neighborFinset x).filter (· ∈ H)) ∪ ((G.neighborFinset x).filter (· ∈ Rest c f H)) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_union, Rest, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; by_cases hy : y ∈ H
      · exact Or.inl ⟨h1, hy⟩
      · exact Or.inr ⟨h1, h2, hy⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, -⟩)
      · exact ⟨h1, offCs hC y h2⟩
      · exact ⟨h1, h2⟩
  rw [this, Finset.card_union_of_disjoint, Nat.add_assoc]
  rw [Finset.disjoint_left]
  intro y h1 h2
  simp only [Finset.mem_filter, Rest, Finset.mem_univ, true_and] at h1 h2
  exact h2.2.2 h1.2

lemma n_split (hD : Cy G c f) (hC : Comp G f H) :
    Fintype.card V = c + H.card + (Rest c f H).card := by
  set Cs := (Finset.range c).image f with hCs
  have hcs : Cs.card = c := card_cset hD
  have : (Finset.univ : Finset V) = Cs ∪ H ∪ Rest c f H := by
    ext y; simp only [Finset.mem_univ, Finset.mem_union, Rest, Finset.mem_filter, true_iff]
    tauto
  have hu : Fintype.card V = (Cs ∪ H ∪ Rest c f H).card := by rw [← this, Finset.card_univ]
  rw [hu, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, hcs]
  · rw [Finset.disjoint_left]; intro y h1 h2; exact offCs hC y h2 h1
  · rw [Finset.disjoint_left]; intro y h1 h2
    simp only [Rest, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    rcases Finset.mem_union.mp h1 with h | h
    · exact h2.1 h
    · exact h2.2 h

/-- The successors of `q` attachments: `Σ d(f (s i + 1)) + 2 q + |H| ≤ n + q²`. -/
lemma succ_deg (hD : Cy G c f) (hC : Comp G f H) {q : ℕ} (hq1 : 1 ≤ q) {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j ≤ q → s i < s j) (hq : s q = s 0 + c)
    (hatt : ∀ i < q, Att G f H (s i))
    (hph : ∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) (q - 1)) :
    (∑ i ∈ Finset.range q, G.degree (f (s i + 1))) + 2 * q + H.card ≤
      Fintype.card V + q * q := by
  have hSC := succ_count hD hC hq1 hs hq hatt hph
  have hsq : ∀ i, i < q → s i < s 0 + c := by intro i hi; rw [← hq]; exact hs i q hi le_rfl
  have hs0 : ∀ i, i ≤ q → s 0 ≤ s i := by
    intro i hi; rcases Nat.eq_zero_or_pos i with rfl | h
    · exact le_rfl
    · exact (hs 0 i h hi).le
  have hCpart : ∀ i, ((G.neighborFinset (f (s i + 1))).filter
      (· ∈ (Finset.range c).image f)).card = (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card := by
    intro i; rw [← card_on_cycle hD (s 0)]; rfl
  have sH : ∀ i < q, ((G.neighborFinset (f (s i + 1))).filter (· ∈ H)).card = 0 := by
    intro i hi
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyH
    exact G1 hD hC (hatt i hi) y hyH ((mem_neighborFinset _ _ _).mp hy)
  -- off-cycle neighbours of different successors are distinct
  have hdisj : ∀ i ∈ (Finset.range q : Set ℕ), ∀ j ∈ (Finset.range q : Set ℕ), i ≠ j →
      Disjoint ((G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H))
        ((G.neighborFinset (f (s j + 1))).filter (· ∈ Rest c f H)) := by
    have key : ∀ i j, i < j → j < q → Disjoint
        ((G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H))
        ((G.neighborFinset (f (s j + 1))).filter (· ∈ Rest c f H)) := by
      intro i j hij hj
      have hlt := hs i j hij (by omega)
      have hjc := hsq j hj
      have hi0 := hs0 i (by omega)
      rw [Finset.disjoint_left]
      intro y h1 h2
      simp only [Finset.mem_filter, mem_neighborFinset, Rest, Finset.mem_univ, true_and] at h1 h2
      have hatj : Att G f H (s i + (s j - s i)) := by
        rw [show s i + (s j - s i) = s j by omega]; exact hatt j hj
      refine G3 hD hC (hatt i (by omega)) hatj (by omega) (by omega) h1.2.2
        (fun t ht => h1.2.1 (ht ▸ hD.mem_cset t)) h1.1 ?_
      rw [show s i + (s j - s i) + 1 = s j + 1 by omega]; exact h2.1.symm
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i j h (by simpa using hj)
    · exact (key j i h (by simpa using hi)).symm
  have hR := Finset.card_biUnion (s := Finset.range q)
    (t := fun i => (G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H)) hdisj
  have hR2 : ((Finset.range q).biUnion
      (fun i => (G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H))).card ≤
      (Rest c f H).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hy
    obtain ⟨_, _, _, h⟩ := hy; exact h
  have hdeg : ∀ i ∈ Finset.range q, G.degree (f (s i + 1)) =
      (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card +
        ((G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H)).card := by
    intro i hi
    rw [deg_split hC, hCpart, sH i (Finset.mem_range.mp hi), Nat.add_zero]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_add_distrib]
  have hn := n_split hD hC
  omega

/-- Lemma A': a vertex `v ∈ H` all of whose cycle neighbours are among the `q` attachments. -/
lemma vert_deg (hD : Cy G c f) (hC : Comp G f H) {v : V} (hv : v ∈ H) {q : ℕ} {s : ℕ → ℕ}
    (hN : ∀ t, G.Adj v (f t) → ∃ i < q, f t = f (s i)) :
    G.degree v + 1 ≤ H.card + q := by
  have hvR : ((G.neighborFinset v).filter (· ∈ Rest c f H)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyR
    simp only [Rest, Finset.mem_filter, Finset.mem_univ, true_and] at hyR
    rcases hC.cl v hv y ((mem_neighborFinset _ _ _).mp hy) with h | ⟨t, rfl⟩
    · exact hyR.2 h
    · exact hyR.1 (hD.mem_cset t)
  have hvH : ((G.neighborFinset v).filter (· ∈ H)).card + 1 ≤ H.card := by
    have : (G.neighborFinset v).filter (· ∈ H) ⊆ H.erase v := by
      intro y hy
      simp only [Finset.mem_filter, mem_neighborFinset] at hy
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.1).symm, hy.2⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hv] at this
    have : 1 ≤ H.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  have hvC : ((G.neighborFinset v).filter (· ∈ (Finset.range c).image f)).card ≤ q := by
    have : (G.neighborFinset v).filter (· ∈ (Finset.range c).image f) ⊆
        (Finset.range q).image (fun i => f (s i)) := by
      intro y hy
      simp only [Finset.mem_filter, mem_neighborFinset, Finset.mem_image, Finset.mem_range] at hy
      obtain ⟨hadj, t, -, rfl⟩ := hy
      obtain ⟨i, hi, he⟩ := hN t hadj
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, he.symm⟩
    exact (Finset.card_le_card this).trans (Finset.card_image_le.trans (by simp))
  rw [deg_split hC, hvR]
  omega

end degsum

/-! ## The linked-set bound `|C| ≥ e(U, C) + |N_C(U)|`

`Q` is a path list in `H`; each `Q[i]` carries a path list `R i` in `H` that meets `Q` only in
`Q[i]` and ends at `u i`; different `R i` are disjoint. Two cycle vertices `f x`, `f y` adjacent to
`u a`, `u b` (`a ≠ b`) are joined through `H` by `R a` reversed, `Q` between `a` and `b`, and `R b`,
which has at least `|a - b| + 1` vertices. Choosing `a, b` far apart (Lemma 3.1 of Ma–Ning–Zhao)
and summing over consecutive attachment positions gives the bound. -/

section link

variable [DecidableRel G.Adj]

structure Link (G : SimpleGraph V) (H : Finset V) (Q : List V) (R : ℕ → List V) (u : ℕ → V) :
    Prop where
  vl : VL G H Q
  r : ∀ i < Q.length, VL G H (R i) ∧ (R i).head? = Q[i]? ∧ (R i).getLast? = some (u i) ∧
    ∀ x ∈ R i, x ∈ Q → Q[i]? = some x
  disj : ∀ i < Q.length, ∀ j < Q.length, i ≠ j → ∀ x ∈ R i, x ∉ R j

lemma decomp (Q : List V) {a b : ℕ} (hab : a < b) (hb : b < Q.length) :
    ∃ Q1 M Q2, Q = Q1 ++ Q[a] :: (M ++ Q[b] :: Q2) ∧ M.length = b - a - 1 := by
  refine ⟨Q.take a, (Q.drop (a + 1)).take (b - a - 1), Q.drop (b + 1), ?_, ?_⟩
  · have e1 : Q.drop a = Q[a] :: Q.drop (a + 1) := List.drop_eq_getElem_cons (by omega)
    have e2 : (Q.drop (a + 1)).drop (b - a - 1) = Q[b] :: Q.drop (b + 1) := by
      rw [List.drop_drop, show a + 1 + (b - a - 1) = b by omega]
      exact List.drop_eq_getElem_cons hb
    calc Q = Q.take a ++ Q.drop a := (List.take_append_drop a Q).symm
      _ = Q.take a ++ Q[a] :: ((Q.drop (a + 1)).take (b - a - 1) ++
          (Q.drop (a + 1)).drop (b - a - 1)) := by rw [e1, List.take_append_drop]
      _ = _ := by rw [e2]
  · simp only [List.length_take, List.length_drop]; omega

lemma getLast?_cons_of {a x : V} {M : List V} (h : M.getLast? = some x) :
    (a :: M).getLast? = some x := by
  cases M with
  | nil => simp at h
  | cons m M' => rw [List.getLast?_cons_cons]; exact h

/-- The linking path between the ends of two pendant paths. -/
lemma ph_link (hC : Comp G f H) {Q : List V} {R : ℕ → List V} {u : ℕ → V}
    (hL : Link G H Q R u) {a b : ℕ} (hab : a < b) (hb : b < Q.length) {x y : V}
    (hx : G.Adj (u a) x) (hy : G.Adj (u b) y) : PH G f x y (b - a + 1) := by
  obtain ⟨Q1, M, Q2, hQ, hM⟩ := decomp Q hab hb
  obtain ⟨qa, hqa⟩ : ∃ qa, qa = Q[a] := ⟨_, rfl⟩
  obtain ⟨qb, hqb⟩ : ∃ qb, qb = Q[b] := ⟨_, rfl⟩
  rw [← hqa, ← hqb] at hQ
  have gqa : Q[a]? = some qa := by rw [hqa]; exact List.getElem?_eq_getElem _
  have gqb : Q[b]? = some qb := by rw [hqb]; exact List.getElem?_eq_getElem _
  obtain ⟨hRa, hRah, hRal, hRaQ⟩ := hL.r a (by omega)
  obtain ⟨hRb, hRbh, hRbl, hRbQ⟩ := hL.r b hb
  rw [gqa] at hRah hRaQ
  rw [gqb] at hRbh hRbQ
  have hdis := hL.disj a (by omega) b hb (by omega)
  obtain ⟨hQn, hQc, hQH⟩ := hL.vl
  rw [hQ] at hQn hQc hQH
  have hinf : (qa :: (M ++ [qb])) <:+: Q1 ++ qa :: (M ++ qb :: Q2) :=
    ⟨Q1, Q2, by simp⟩
  have hch : (qa :: (M ++ [qb])).IsChain G.Adj := chain_sub hQc hinf
  have hnd : (qa :: (M ++ [qb])).Nodup := hQn.sublist hinf.sublist
  have hMQ : ∀ z ∈ M, z ∈ Q := by
    intro z hz; rw [hQ]; simp [hz]
  have hMH : ∀ z ∈ M, z ∈ H := fun z hz => hQH z (by simp [hz])
  have hqaM : qa ∉ M := by
    intro h; exact (List.nodup_cons.mp hnd).1 (List.mem_append_left _ h)
  have hqbM : qb ∉ M := by
    intro h
    have := (List.nodup_cons.mp hnd).2
    rw [List.nodup_append] at this
    exact this.2.2 qb h qb (by simp) rfl
  have hMnd : M.Nodup := ((List.nodup_cons.mp hnd).2).sublist (List.sublist_append_left _ _)
  have hRane : R a ≠ [] := by intro h; rw [h] at hRah; simp at hRah
  -- the list
  refine ⟨(R a).reverse ++ (M ++ R b), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hRane]
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hRa.1, ⟨hMnd, hRb.1, ?_⟩, ?_⟩
    · intro z hz w hw hzw; subst hzw
      have := hRbQ z hw (hMQ z hz)
      exact hqbM (by cases this; exact hz)
    · intro z hz w hw hzw; subst hzw
      rw [List.mem_reverse] at hz
      rcases List.mem_append.mp hw with hw | hw
      · have := hRaQ z hz (hMQ z hw); cases this; exact hqaM hw
      · exact hdis z hz hw
  · rw [List.isChain_append, List.isChain_append]
    refine ⟨List.isChain_reverse.mpr (hRa.2.1.imp (fun _ _ h => h.symm)), ⟨?_, hRb.2.1, ?_⟩, ?_⟩
    · exact chain_sub hch ⟨[qa], [qb], by simp⟩
    · intro z hz w hw
      rw [hRbh] at hw; cases hw
      have h2 : ((qa :: M) ++ [qb]).IsChain G.Adj := by simpa using hch
      rw [List.isChain_append] at h2
      exact h2.2.2 z (getLast?_cons_of hz) qb (by simp)
    · intro z hz w hw
      rw [List.getLast?_reverse, hRah] at hz; cases hz
      have h1 := (List.isChain_cons.mp hch).1
      apply h1
      cases M with
      | nil => simp at hw ⊢; rw [hRbh] at hw; simpa using hw
      | cons m M' => simpa using hw
  · intro z hz t ht
    rcases List.mem_append.mp hz with hz | hz
    · exact hC.off z (hRa.2.2 z (List.mem_reverse.mp hz)) t ht
    · rcases List.mem_append.mp hz with hz | hz
      · exact hC.off z (hMH z hz) t ht
      · exact hC.off z (hRb.2.2 z hz) t ht
  · have h1 : 1 ≤ (R a).length := List.length_pos_iff.mpr hRane
    have h2 : 1 ≤ (R b).length := List.length_pos_iff.mpr (by intro h; rw [h] at hRbh; simp at hRbh)
    simp only [List.length_append, List.length_reverse]; omega
  · intro z hz
    have : ((R a).reverse ++ (M ++ R b)).head? = some (u a) := by
      rw [List.head?_append, List.head?_reverse, hRal]; rfl
    rw [this] at hz; cases hz; exact hx.symm
  · intro z hz
    have : ((R a).reverse ++ (M ++ R b)).getLast? = some (u b) := by
      rw [List.getLast?_append, List.getLast?_append, hRbl]; rfl
    rw [this] at hz; cases hz; exact hy

/-- The pendant-path indices adjacent to the cycle position `t`. -/
def Sx (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℕ → V) (u : ℕ → V) (p t : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun i => G.Adj (u i) (f t))

lemma gap (hD : Cy G c f) (hC : Comp G f H) {Q : List V} {R : ℕ → List V} {u : ℕ → V}
    (hL : Link G H Q R u) {x y : ℕ} (hxy : x < y) (hyc : y ≤ x + c)
    (hA : (Sx G f u Q.length x).Nonempty) (hB : (Sx G f u Q.length y).Nonempty) :
    (Sx G f u Q.length x).card + (Sx G f u Q.length y).card + 2 ≤ 2 * (y - x) := by
  set A := Sx G f u Q.length x with hAdef
  set B := Sx G f u Q.length y with hBdef
  have memA : ∀ i ∈ A, i < Q.length ∧ G.Adj (u i) (f x) := by
    intro i hi; simpa [hAdef, Sx] using hi
  have memB : ∀ i ∈ B, i < Q.length ∧ G.Adj (u i) (f y) := by
    intro i hi; simpa [hBdef, Sx] using hi
  -- an off-cycle path with `K` vertices from `f x` to `f y` forces `y - x ≥ K + 1`
  have useR : ∀ K, PH G f (f x) (f y) K → K + 1 ≤ y - x := by
    intro K ⟨X, hX, hK, h1, h2⟩
    have := R1 hD hX (b := x) (j := y - x) (by omega) (by omega) h1
      (by rw [show x + (y - x) = y by omega]; exact h2)
    omega
  have pair : ∀ a ∈ A, ∀ b ∈ B, a ≠ b → (a < b → b - a + 2 ≤ y - x) ∧ (b < a → a - b + 2 ≤ y - x) := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := memA a ha
    obtain ⟨hb1, hb2⟩ := memB b hb
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := useR _ (ph_link hC hL h hb1 ha2 hb2); omega
    · have := useR _ (ph_link hC hL h ha1 hb2 ha2).symm; omega
  set a1 := A.min' hA
  set a2 := A.max' hA
  set b1 := B.min' hB
  set b2 := B.max' hB
  have ha1 : a1 ∈ A := A.min'_mem hA
  have ha2 : a2 ∈ A := A.max'_mem hA
  have hb1 : b1 ∈ B := B.min'_mem hB
  have hb2 : b2 ∈ B := B.max'_mem hB
  have hcA : A.card ≤ a2 + 1 - a1 := by
    have : A ⊆ Finset.Icc a1 a2 := fun i hi =>
      Finset.mem_Icc.mpr ⟨A.min'_le i hi, A.le_max' i hi⟩
    have := Finset.card_le_card this; rwa [Nat.card_Icc] at this
  have hcB : B.card ≤ b2 + 1 - b1 := by
    have : B ⊆ Finset.Icc b1 b2 := fun i hi =>
      Finset.mem_Icc.mpr ⟨B.min'_le i hi, B.le_max' i hi⟩
    have := Finset.card_le_card this; rwa [Nat.card_Icc] at this
  have o1 : a1 ≤ a2 := A.min'_le a2 ha2
  have o2 : b1 ≤ b2 := B.min'_le b2 hb2
  by_cases e1 : a1 = b2
  · by_cases e2 : a2 = b1
    · -- all four coincide: single indices
      have hA1 : A.card ≤ 1 := by omega
      have hB1 : B.card ≤ 1 := by omega
      obtain ⟨hi1, hi2⟩ := memA a1 ha1
      obtain ⟨-, hi3⟩ := memB b2 hb2
      rw [← e1] at hi3
      have : 2 ≤ y - x := by
        have := useR 1 ⟨[u a1], ⟨by simp, by simp, by simp, fun z hz t ht => ?_⟩, by simp,
          by intro z hz; simp at hz; subst hz; exact hi2.symm,
          by intro z hz; simp at hz; subst hz; exact hi3⟩
        · omega
        · simp at hz; subst hz
          obtain ⟨hR, hRh, hRl, -⟩ := hL.r a1 hi1
          exact hC.off _ (hR.2.2 _ (List.mem_of_getLast? hRl)) t ht
      omega
    · have := pair a2 ha2 b1 hb1 e2; omega
  · by_cases e2 : a2 = b1
    · have := pair a1 ha1 b2 hb2 e1; omega
    · have := pair a1 ha1 b2 hb2 e1; have := pair a2 ha2 b1 hb1 e2; omega

/-- The attachment positions of `U = {u i}` in the window `(0, c]`. -/
def Wp (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℕ) (f : ℕ → V) (u : ℕ → V) (p : ℕ) :
    Finset ℕ :=
  (Finset.Ioc 0 c).filter (fun t => (Sx G f u p t).Nonempty)

lemma Sx_per (hD : Cy G c f) (u : ℕ → V) (p t : ℕ) : Sx G f u p (t + c) = Sx G f u p t := by
  simp only [Sx, hD.per]

lemma e_eq (u : ℕ → V) (p : ℕ) :
    (∑ i ∈ Finset.range p, (cn G f (u i) 0 c).card) = ∑ t ∈ Wp G c f u p, (Sx G f u p t).card := by
  have : (∑ i ∈ Finset.range p, (cn G f (u i) 0 c).card) =
      ∑ t ∈ Finset.Ioc 0 c, (Sx G f u p t).card := by
    simp only [cn, Finset.card_filter, Sx]
    exact Finset.sum_comm
  rw [this, Wp, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs with h
  · rfl
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]; rfl

/-- **(L20)** `|C| ≥ e(U, C) + |N_C(U)|`. -/
lemma L20 (hD : Cy G c f) (hC : Comp G f H) {Q : List V} {R : ℕ → List V} {u : ℕ → V}
    (hL : Link G H Q R u) (h2 : 2 ≤ (Wp G c f u Q.length).card) :
    (∑ i ∈ Finset.range Q.length, (cn G f (u i) 0 c).card) + (Wp G c f u Q.length).card ≤ c := by
  set p := Q.length with hp
  set W := Wp G c f u p with hW
  set d : ℕ → ℕ := fun t => (Sx G f u p t).card with hd
  have s1 := e_eq (G := G) (f := f) (c := c) u p
  obtain ⟨N, hN⟩ : ∃ N, W.card = N := ⟨_, rfl⟩
  have hN0 : 0 < N := by omega
  set τ := W.orderEmbOfFin hN with hτ
  set g : ℕ → ℕ := fun j => if h : j < N then τ ⟨j, h⟩ else τ ⟨0, hN0⟩ + c with hg
  have gW : ∀ j (h : j < N), g j ∈ W := by
    intro j h; simp only [hg, dif_pos h]; exact W.orderEmbOfFin_mem hN _
  have Wmem : ∀ t ∈ W, 0 < t ∧ t ≤ c ∧ (Sx G f u p t).Nonempty := by
    intro t ht; simp only [hW, Wp, Finset.mem_filter, Finset.mem_Ioc] at ht; exact ⟨ht.1.1, ht.1.2, ht.2⟩
  have gmono : ∀ i j, i < j → j < N → g i < g j := by
    intro i j hij hj
    simp only [hg, dif_pos hj, dif_pos (show i < N by omega)]
    exact τ.lt_iff_lt.mpr (by simp [Fin.lt_def]; omega)
  have gN : g N = g 0 + c := by simp [hg, dif_pos hN0]
  -- step 2: the sum over `W` is the sum over the sorted positions
  have s2 : ∑ t ∈ W, d t = ∑ j ∈ Finset.range N, d (g j) := by
    have himg : (Finset.range N).image g = W := by
      ext t; simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact gW j hj
      · intro ht
        have : t ∈ Set.range τ := by rw [hτ, Finset.range_orderEmbOfFin]; exact ht
        obtain ⟨⟨j, hj⟩, rfl⟩ := this
        exact ⟨j, hj, by simp [hg, dif_pos hj]⟩
    rw [← himg, Finset.sum_image]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd hij (gmono i j h hj).ne
    · exact h
    · exact absurd hij (gmono j i h hi).ne'
  -- step 3: one gap
  have hgap : ∀ j < N, d (g j) + d (g (j + 1)) + 2 + 2 * g j ≤ 2 * g (j + 1) := by
    intro j hj
    obtain ⟨hx0, hxc, hxS⟩ := Wmem _ (gW j hj)
    rcases Nat.lt_or_ge (j + 1) N with h | h
    · obtain ⟨hy0, hyc, hyS⟩ := Wmem _ (gW (j + 1) h)
      have hlt := gmono j (j + 1) (by omega) h
      have := gap hD hC hL hlt (by omega) hxS hyS
      rw [← hp] at this
      simp only [hd]; omega
    · have hjN : j + 1 = N := by omega
      rw [hjN, gN]
      obtain ⟨h00, h0c, h0S⟩ := Wmem _ (gW 0 hN0)
      have hlt : g 0 < g j := gmono 0 j (by omega) hj
      have hS : (Sx G f u p (g 0 + c)).Nonempty := by rw [Sx_per hD]; exact h0S
      have := gap hD hC hL (x := g j) (y := g 0 + c) (by omega) (by omega) hxS hS
      rw [← hp] at this
      have e : d (g 0 + c) = d (g 0) := by simp only [hd]; rw [Sx_per hD]
      simp only [hd] at this e ⊢; omega
  have hsum := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range N) => hgap j (Finset.mem_range.mp hj))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum] at hsum
  have t1 := Finset.sum_range_succ' (fun j => g j) N
  have t2 := Finset.sum_range_succ (fun j => g j) N
  have t3 := Finset.sum_range_succ' (fun j => d (g j)) N
  have t4 := Finset.sum_range_succ (fun j => d (g j)) N
  have e : d (g N) = d (g 0) := by rw [gN]; simp only [hd]; rw [Sx_per hD]
  rw [s1, s2, ← hN]
  rw [hN]
  omega

end link

/-! ## The residual case: arithmetic and assembly -/

lemma ar1 (k p δ m e w c n : ℕ) (hk : 1 ≤ k) (hp : k ≤ p) (hδ : 6 * k ≤ δ)
    (he : p * δ ≤ e + p * m) (hw : e ≤ p * w) (hc : e + w ≤ c) (hn : c + p ≤ n)
    (hkn : n + k * (k - 1) ≤ (k + 1) * δ)
    (hm : (p ≤ 5 * k + 1 ∧ m + 1 ≤ p) ∨ (5 * k + 2 ≤ p ∧ m ≤ 4 * k)) : False := by
  have hp0 : 0 < p := by omega
  have h1 : (p + 1) * e ≤ p * c := by nlinarith
  have hmd : m < δ := by rcases hm with ⟨h0, h⟩ | ⟨h0, h⟩ <;> omega
  have h2 : (p + 1) * (δ - m) ≤ c := by
    have : p * ((p + 1) * (δ - m)) ≤ p * c := by
      have : p * (δ - m) ≤ e := by
        have : p * (δ - m) + p * m = p * δ := by rw [← Nat.mul_add, Nat.sub_add_cancel hmd.le]
        omega
      nlinarith
    exact Nat.le_of_mul_le_mul_left this hp0
  have hk1 : k * (k - 1) + k = k * k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp; ring
  zify [hmd.le, hk] at h2 hn hkn hδ hp hm
  rcases hm with ⟨h5, hm⟩ | ⟨h5, hm⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr h5), mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hδ),
      mul_nonneg (show (0:ℤ) ≤ p + 1 by positivity) (sub_nonneg.mpr (show (m:ℤ) ≤ p - 1 by linarith))]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hδ),
      mul_nonneg (show (0:ℤ) ≤ p + 1 by positivity) (sub_nonneg.mpr hm)]

section resid

variable [DecidableRel G.Adj]

lemma rest_zero (hD : Cy G c f) (hC : Comp G f H) {x : V} (hx : x ∈ H) :
    ((G.neighborFinset x).filter (· ∈ Rest c f H)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y hy hyR
  simp only [Rest, Finset.mem_filter, Finset.mem_univ, true_and] at hyR
  rcases hC.cl x hx y ((mem_neighborFinset _ _ _).mp hy) with h | ⟨t, rfl⟩
  · exact hyR.2 h
  · exact hyR.1 (hD.mem_cset t)

lemma degH_eq (x : V) : ((G.neighborFinset x).filter (· ∈ H)).card = (H.filter (G.Adj x)).card := by
  congr 1; ext y; simp [mem_neighborFinset, and_comm]

/-- A vertex of `H`: degree = cycle neighbours + `H`-neighbours. -/
lemma deg_H (hD : Cy G c f) (hC : Comp G f H) {x : V} (hx : x ∈ H) :
    G.degree x = (cn G f x 0 c).card + (H.filter (G.Adj x)).card := by
  rw [deg_split hC, rest_zero hD hC hx, degH_eq (H := H) x, Nat.add_zero]
  congr 1
  rw [← card_on_cycle hD 0, Nat.zero_add]; rfl

/-- The residual case: a linked family whose ends have small `H`-degree sum is impossible. -/
lemma resid_contra (hD : Cy G c f) (hC : Comp G f H) {δ k : ℕ} (hδ : ∀ x, δ ≤ G.degree x)
    (hk : 2 ≤ k) (hδ6 : 6 * k ≤ δ) (hkn : Fintype.card V + k * (k - 1) ≤ (k + 1) * δ)
    {Q : List V} {R : ℕ → List V} {u : ℕ → V} (hL : Link G H Q R u) (hpk : k ≤ Q.length)
    {m : ℕ} (hsum : ∑ i ∈ Finset.range Q.length, (H.filter (G.Adj (u i))).card ≤ Q.length * m)
    (hm : (Q.length ≤ 5 * k + 1 ∧ m + 1 ≤ Q.length) ∨ (5 * k + 2 ≤ Q.length ∧ m ≤ 4 * k)) :
    False := by
  set p := Q.length with hp
  have uH : ∀ i < p, u i ∈ H := by
    intro i hi
    obtain ⟨hR, -, hRl, -⟩ := hL.r i hi
    exact hR.2.2 _ (List.mem_of_getLast? hRl)
  set e := ∑ i ∈ Finset.range p, (cn G f (u i) 0 c).card with he_def
  have he : p * δ ≤ e + p * m := by
    have : ∑ i ∈ Finset.range p, δ ≤ ∑ i ∈ Finset.range p,
        ((cn G f (u i) 0 c).card + (H.filter (G.Adj (u i))).card) :=
      Finset.sum_le_sum (fun i hi => by
        rw [← deg_H hD hC (uH i (Finset.mem_range.mp hi))]; exact hδ _)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    omega
  set W := Wp G c f u p with hW
  have hw : e ≤ p * W.card := by
    rw [he_def, e_eq, hW]
    calc ∑ t ∈ Wp G c f u p, (Sx G f u p t).card ≤ ∑ t ∈ Wp G c f u p, p :=
          Finset.sum_le_sum (fun t _ => by
            calc (Sx G f u p t).card ≤ (Finset.range p).card := Finset.card_filter_le _ _
              _ = p := Finset.card_range p)
      _ = p * (Wp G c f u p).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hp0 : 0 < p := by omega
  have hc : e + W.card ≤ c := by
    by_cases h2 : 2 ≤ W.card
    · exact L20 hD hC hL h2
    · exfalso
      have : p * δ ≤ p * (1 + m) := by
        have : e ≤ p := by have : p * W.card ≤ p * 1 := Nat.mul_le_mul_left _ (by omega); omega
        rw [Nat.mul_add]; omega
      have := Nat.le_of_mul_le_mul_left this hp0
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hn : c + p ≤ Fintype.card V := by
    have := n_split hD hC
    have := hL.vl.length_le
    omega
  exact ar1 k p δ m e W.card c (Fintype.card V) (by omega) hpk hδ6 he hw hc hn hkn hm

end resid

/-! ## Linked sets (Fable's theorem)

`D ⊆ H` with `|D| ≥ k + 1`, any two vertices of `D` joined inside `D` by a path list with at least
`k` vertices. Menger gives `k + 1` disjoint `D`–`C` paths (then Lemma B) or `k` of them together
with a separator `S` of size `k`; a vertex `v ∈ D \ S` then has all its cycle neighbours among the
ends of the paths (Lemma A'). Both contradict `(k + 1) δ ≥ n + k (k - 1)`. -/

section linked

variable [DecidableRel G.Adj]

/-- The separation property supplied by `k`-connectivity. -/
def KSep (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card + 1 ≤ k → ∀ X : Finset V, (∀ a ∈ X, a ∉ S) →
    (∀ a ∈ X, ∀ b, G.Adj a b → b ∉ S → b ∈ X) → X.Nonempty → ∀ y, y ∉ S → y ∉ X → False

lemma mem_cset_iff (hD : Cy G c f) (y : V) : y ∈ (Finset.range c).image f ↔ ∃ t, f t = y := by
  constructor
  · intro h; obtain ⟨t, -, ht⟩ := Finset.mem_image.mp h; exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩; exact hD.mem_cset t

/-- `k`-connectivity forces at least `k` cycle vertices. -/
lemma k_le_c (hD : Cy G c f) (hC : Comp G f H) {k : ℕ} (hK : KSep G k) (hH : H.Nonempty) :
    k ≤ c := by
  set A := ((Finset.range c).image f).filter (fun y => ∃ z ∈ H, G.Adj y z) with hA
  by_contra hlt
  push_neg at hlt
  have hAc : A.card ≤ c := (Finset.card_filter_le _ _).trans (card_cset hD).le
  have hclos : ∀ a ∈ H, ∀ b, G.Adj a b → b ∉ A → b ∈ H := by
    intro a ha b hab hbA
    rcases hC.cl a ha b hab with h | ⟨t, rfl⟩
    · exact h
    · exact absurd (Finset.mem_filter.mpr ⟨hD.mem_cset t, a, ha, hab.symm⟩) hbA
  have hHA : ∀ a ∈ H, a ∉ A := by
    intro a ha haA
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (Finset.mem_filter.mp haA).1
    exact hC.off a ha t ht
  by_cases hne : A.Nonempty
  · obtain ⟨y, hy⟩ := hne
    obtain ⟨hyC, z, hz, hyz⟩ := Finset.mem_filter.mp hy
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hyC
    refine hK A (by omega) H hHA hclos hH (f (t + 1)) ?_ ?_
    · intro h
      obtain ⟨-, z', hz', h'⟩ := Finset.mem_filter.mp h
      exact G1 hD hC ⟨z, hz, hyz⟩ z' hz' h'
    · intro h; exact hC.off _ h (t + 1) rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine hK A (by rw [hne]; simp; omega) H hHA hclos hH (f 0) ?_ ?_
    · rw [hne]; simp
    · intro h; exact hC.off _ h 0 rfl

/-- Lists that stay off the cycle and start in `H` stay in `H`. -/
lemma chain_in_H (hC : Comp G f H) : ∀ l : List V, l.IsChain G.Adj → (∀ x ∈ l.head?, x ∈ H) →
    (∀ x ∈ l, ∀ t, f t ≠ x) → ∀ x ∈ l, x ∈ H
  | [], _, _, _ => by simp
  | [a], _, h1, _ => by simpa using h1
  | a :: b :: l, hch, h1, hoff => by
    have ha : a ∈ H := h1 a rfl
    rw [List.isChain_cons_cons] at hch
    have hb : b ∈ H := by
      rcases hC.cl a ha b hch.1 with h | ⟨t, ht⟩
      · exact h
      · exact absurd ht (hoff b (by simp) t)
    have := chain_in_H hC (b :: l) hch.2 (by simpa using hb)
      (fun x hx => hoff x (List.mem_cons_of_mem a hx))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact this x hx

/-- Separators of `D` from the cycle have at least `k` vertices. -/
lemma sep_ge (hD : Cy G c f) (hC : Comp G f H) {k : ℕ} (hK : KSep G k) {D : Finset V}
    (hDH : D ⊆ H) (hDk : k + 1 ≤ D.card) (S : Finset V)
    (hS : ∀ l, ABP G D ((Finset.range c).image f) l → ∃ x ∈ l, x ∈ S) : k ≤ S.card := by
  by_contra hlt
  push_neg at hlt
  have hH : H.Nonempty := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < D.card by omega); exact ⟨x, hDH hx⟩
  have hkc := k_le_c hD hC hK hH
  -- a start vertex outside `S`, and a cycle vertex outside `S`
  obtain ⟨d0, hd0D, hd0S⟩ : ∃ d ∈ D, d ∉ S := by
    by_contra h; push_neg at h
    have := Finset.card_le_card (show D ⊆ S from h); omega
  obtain ⟨y, hyC, hyS⟩ : ∃ y ∈ (Finset.range c).image f, y ∉ S := by
    by_contra h; push_neg at h
    have := Finset.card_le_card (show (Finset.range c).image f ⊆ S from h)
    rw [card_cset hD] at this; omega
  classical
  set X : Finset V := Finset.univ.filter (fun z => ∃ hz : z ∉ S, ∃ d, ∃ hd : d ∉ S, d ∈ D ∧
    (G.induce ((S : Set V)ᶜ)).Reachable ⟨d, hd⟩ ⟨z, hz⟩) with hX
  have memX : ∀ z, z ∈ X ↔ ∃ hz : z ∉ S, ∃ d, ∃ hd : d ∉ S, d ∈ D ∧
      (G.induce ((S : Set V)ᶜ)).Reachable ⟨d, hd⟩ ⟨z, hz⟩ := by
    intro z; simp [hX]
  refine hK S (by omega) X (fun a ha => ((memX a).mp ha).1) ?_ ⟨d0, (memX d0).mpr
    ⟨hd0S, d0, hd0S, hd0D, Reachable.refl _⟩⟩ y hyS ?_
  · intro a ha b hab hbS
    obtain ⟨haS, d, hdS, hdD, hr⟩ := (memX a).mp ha
    exact (memX b).mpr ⟨hbS, d, hdS, hdD, hr.trans (Adj.reachable (G := G.induce ((S : Set V)ᶜ))
      (u := ⟨a, haS⟩) (v := ⟨b, hbS⟩) hab)⟩
  · intro hy
    obtain ⟨hyS', d, hdS, hdD, hr⟩ := (memX y).mp hy
    obtain ⟨w⟩ := hr
    obtain ⟨p, hp⟩ := w.toPath
    obtain ⟨x, hx, hxS⟩ := hS (p.support.map Subtype.val) ⟨hp.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr p.isChain_adj_support,
      ⟨d, hdD, by rw [Walk.support_eq_cons, List.map_cons, List.head?_cons]⟩,
      ⟨y, hyC, by rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
        Walk.getLast_support]; rfl⟩⟩
    obtain ⟨x', -, rfl⟩ := List.mem_map.mp hx
    exact x'.2 hxS

/-- The pieces of a trimmed `D`–`C` path: `l = M ++ [a]` with `M` a path in `H` from `d ∈ D`. -/
lemma path_parts (hD : Cy G c f) (hC : Comp G f H) {D : Finset V} (hDH : D ⊆ H) {l : List V}
    (hl : ABP G D ((Finset.range c).image f) l ∧ (∀ x ∈ l.tail, x ∉ D) ∧
      (∀ x ∈ l.dropLast, x ∉ (Finset.range c).image f)) :
    ∃ d a w M, l = M ++ [a] ∧ M.head? = some d ∧ M.getLast? = some w ∧ d ∈ D ∧
      (∃ t, f t = a) ∧ G.Adj w a ∧ (∀ x ∈ M, x ∈ H) ∧ (∀ x ∈ M.tail, x ∉ D) ∧ M.Nodup ∧
      M.IsChain G.Adj := by
  obtain ⟨⟨hnd, hch, ⟨d, hd, hdh⟩, ⟨a, ha, hal⟩⟩, htl, hdl⟩ := hl
  have hne : l ≠ [] := by intro h; rw [h] at hdh; simp at hdh
  have hsplit : l = l.dropLast ++ [a] := by
    have h := List.dropLast_append_getLast hne
    rw [List.getLast?_eq_getLast_of_ne_nil hne, Option.some.injEq] at hal
    rw [← hal]; exact h.symm
  set M := l.dropLast with hM
  have hMne : M ≠ [] := by
    intro h
    rw [h] at hsplit; rw [hsplit] at hdh; simp at hdh; subst hdh
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp ha
    exact hC.off _ (hDH hd) t ht
  have hMh : M.head? = some d := by
    rw [hsplit, List.head?_append] at hdh
    obtain ⟨m, M', hm⟩ := List.ne_nil_iff_exists_cons.mp hMne
    rw [hm] at hdh ⊢; simpa using hdh
  obtain ⟨w, hw⟩ : ∃ w, M.getLast? = some w := by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hMne); exact ⟨w, hw⟩
  rw [hsplit] at hnd hch
  have hMch : M.IsChain G.Adj := (List.isChain_append.mp hch).1
  have hwa : G.Adj w a := (List.isChain_append.mp hch).2.2 w hw a rfl
  have hMoff : ∀ x ∈ M, ∀ t, f t ≠ x := by
    intro x hx t ht; exact hdl x hx (by rw [← ht]; exact hD.mem_cset t)
  refine ⟨d, a, w, M, hsplit, hMh, hw, hd, (mem_cset_iff hD a).mp ha, hwa,
    chain_in_H hC M hMch (by rw [hMh]; intro x hx; cases hx; exact hDH hd) hMoff, ?_,
    (List.nodup_append.mp hnd).1, hMch⟩
  intro x hx
  apply htl
  rw [hsplit]
  obtain ⟨m, M', hm⟩ := List.ne_nil_iff_exists_cons.mp hMne
  rw [hm] at hx ⊢; simp only [List.tail_cons] at hx; simp [hx]

lemma getLast?_tail_append {X M : List V} {d : V} (hX : X.tail ≠ []) (hXl : X.getLast? = some d)
    (hMh : M.head? = some d) : (X.tail ++ M.tail).getLast? = M.getLast? := by
  obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
    cases M with
    | nil => simp at hMh
    | cons m M' => exact ⟨m, M', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hMh; subst hMh
  cases M' with
  | nil =>
    simp only [List.tail_cons, List.append_nil, List.getLast?_singleton]
    obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
      cases X with
      | nil => simp at hX
      | cons x X' => exact ⟨x, X', rfl⟩
    simp only [List.tail_cons] at hX ⊢
    rw [List.getLast?_cons, List.getLast?_eq_getLast_of_ne_nil hX] at hXl
    rw [List.getLast?_eq_getLast_of_ne_nil hX]; simpa using hXl
  | cons m' M'' =>
    rw [List.getLast?_append_of_ne_nil _ (by simp), List.tail_cons, List.getLast?_cons_cons]

/-- Two ends of disjoint trimmed paths are linked through `D` by at least `k` vertices. -/
lemma ends_linked (hC : Comp G f H) {D : Finset V} (hDH : D ⊆ H) {k : ℕ}
    {di dj wi wj ai aj : V} {Mi Mj X : List V}
    (hMih : Mi.head? = some di) (hMil : Mi.getLast? = some wi) (hMjh : Mj.head? = some dj)
    (hMjl : Mj.getLast? = some wj) (hwi : G.Adj wi ai) (hwj : G.Adj wj aj)
    (hMiH : ∀ x ∈ Mi, x ∈ H) (hMjH : ∀ x ∈ Mj, x ∈ H) (hMiD : ∀ x ∈ Mi.tail, x ∉ D)
    (hMjD : ∀ x ∈ Mj.tail, x ∉ D) (hMin : Mi.Nodup) (hMjn : Mj.Nodup) (hMic : Mi.IsChain G.Adj)
    (hMjc : Mj.IsChain G.Adj) (hdisj : ∀ x ∈ Mi, x ∉ Mj)
    (hX : HP G D di dj X) (hXk : k ≤ X.length) (hdd : di ≠ dj) :
    PH G f ai aj k := by
  obtain ⟨hXn, hXc, hXD, hXh, hXl⟩ := hX
  obtain ⟨x0, X', rfl⟩ : ∃ x0 X', X = x0 :: X' := by
    cases X with
    | nil => simp at hXh
    | cons x X' => exact ⟨x, X', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hXh; subst hXh
  have hX'ne : X' ≠ [] := by
    intro h; subst h; simp at hXl; exact hdd hXl
  obtain ⟨m0, Mj', rfl⟩ : ∃ m0 Mj', Mj = m0 :: Mj' := by
    cases Mj with
    | nil => simp at hMjh
    | cons m Mj' => exact ⟨m, Mj', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hMjh; subst hMjh
  have hdiMi : ∀ x ∈ Mi, x ∈ D → x = x0 := by
    intro x hx hxD
    obtain ⟨m, Mi', rfl⟩ : ∃ m Mi', Mi = m :: Mi' := by
      cases Mi with
      | nil => simp at hx
      | cons m Mi' => exact ⟨m, Mi', rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hMih; subst hMih
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact absurd hxD (hMiD x hx)
  refine ⟨Mi.reverse ++ (X' ++ Mj'), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hX'ne]
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hMin, ⟨(List.nodup_cons.mp hXn).2, (List.nodup_cons.mp hMjn).2,
      ?_⟩, ?_⟩
    · intro x hx y hy hxy; subst hxy; exact hMjD x hy (hXD x (by simp [hx]))
    · intro x hx y hy hxy; subst hxy
      rw [List.mem_reverse] at hx
      rcases List.mem_append.mp hy with hy | hy
      · have := hdiMi x hx (hXD x (by simp [hy])); subst this
        exact (List.nodup_cons.mp hXn).1 hy
      · exact hdisj x hx (List.mem_cons_of_mem _ hy)
  · rw [List.isChain_append, List.isChain_append]
    refine ⟨List.isChain_reverse.mpr (hMic.imp (fun _ _ h => h.symm)),
      ⟨(List.isChain_cons.mp hXc).2, (List.isChain_cons.mp hMjc).2, ?_⟩, ?_⟩
    · intro x hx y hy
      have : x = m0 := by
        rw [List.getLast?_cons, List.getLast?_eq_getLast_of_ne_nil hX'ne] at hXl
        rw [List.getLast?_eq_getLast_of_ne_nil hX'ne] at hx; simp at hXl hx; rw [← hx, hXl]
      subst this
      exact (List.isChain_cons.mp hMjc).1 y hy
    · intro x hx y hy
      rw [List.getLast?_reverse, hMih] at hx; cases hx
      rw [List.head?_append] at hy
      obtain ⟨x1, X'', rfl⟩ := List.ne_nil_iff_exists_cons.mp hX'ne
      simp at hy; subst hy
      exact (List.isChain_cons.mp hXc).1 _ rfl
  · intro x hx t ht
    rcases List.mem_append.mp hx with hx | hx
    · exact hC.off x (hMiH x (List.mem_reverse.mp hx)) t ht
    · rcases List.mem_append.mp hx with hx | hx
      · exact hC.off x (hDH (hXD x (by simp [hx]))) t ht
      · exact hC.off x (hMjH x (by simp [hx])) t ht
  · simp only [List.length_append, List.length_reverse, List.length_cons] at hXk ⊢
    have : 1 ≤ Mi.length := List.length_pos_iff.mpr (by intro h; rw [h] at hMih; simp at hMih)
    omega
  · intro z hz
    rw [List.head?_append, List.head?_reverse, hMil] at hz; cases hz; exact hwi.symm
  · intro z hz
    have e := getLast?_tail_append (X := x0 :: X') (M := m0 :: Mj') (d := m0)
      (by simpa using hX'ne) hXl rfl
    simp only [List.tail_cons] at e
    rw [List.getLast?_append_of_ne_nil _ (by simp [hX'ne]), e, hMjl] at hz
    cases hz; exact hwj

/-- Sorting distinct cycle positions. -/
lemma sort_pos {q c : ℕ} (hq : 1 ≤ q) (t : Fin q → ℕ) (ht : Function.Injective t)
    (htc : ∀ i, t i < c) :
    ∃ s : ℕ → ℕ, (∀ i j, i < j → j ≤ q → s i < s j) ∧ s q = s 0 + c ∧
      (∀ j < q, ∃ i, s j = t i) ∧ ∀ i, ∃ j < q, s j = t i := by
  set T := Finset.univ.image t with hT
  have hTc : T.card = q := by rw [hT, Finset.card_image_of_injective _ ht]; simp
  set τ := T.orderEmbOfFin hTc
  refine ⟨fun j => if h : j < q then τ ⟨j, h⟩ else τ ⟨0, hq⟩ + c, ?_,
    by simp only []; rw [dif_neg (lt_irrefl q), dif_pos (show 0 < q by omega)], ?_, ?_⟩
  · intro i j hij hj
    have hi : i < q := by omega
    simp only [dif_pos hi]
    by_cases hjq : j < q
    · simp only [dif_pos hjq]; exact τ.lt_iff_lt.mpr (by simp [Fin.lt_def]; omega)
    · simp only [dif_neg hjq]
      have hm : τ ⟨i, hi⟩ ∈ T := T.orderEmbOfFin_mem hTc ⟨i, hi⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hm
      have := htc a; rw [ha] at this; omega
  · intro j hj
    simp only [dif_pos hj]
    have hm : τ ⟨j, hj⟩ ∈ T := T.orderEmbOfFin_mem hTc ⟨j, hj⟩
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hm
    exact ⟨a, ha.symm⟩
  · intro i
    have : t i ∈ Set.range τ := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (by simp))
    obtain ⟨⟨j, hj⟩, hji⟩ := this
    exact ⟨j, hj, by simp only [dif_pos hj]; exact hji⟩

lemma ends_sorted (hD : Cy G c f) (hC : Comp G f H) {k : ℕ} {D : Finset V} (hDH : D ⊆ H)
    (hDl : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ∃ X, HP G D x y X ∧ k ≤ X.length) {q : ℕ} (hq : 1 ≤ q)
    (P : Fin q → List V)
    (hP : ∀ i, ABP G D ((Finset.range c).image f) (P i) ∧ (∀ x ∈ (P i).tail, x ∉ D) ∧
      (∀ x ∈ (P i).dropLast, x ∉ (Finset.range c).image f))
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j) :
    ∃ s : ℕ → ℕ, (∀ i j, i < j → j ≤ q → s i < s j) ∧ s q = s 0 + c ∧
      (∀ j < q, Att G f H (s j)) ∧ (∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) k) ∧
      (∀ i, ∃ j < q, (P i).getLast? = some (f (s j))) := by
  have hc : 0 < c := by have := hD.three; omega
  choose d a w M hPM hMh hMl hdD hat hwa hMH hMD hMn hMc using
    fun i => path_parts hD hC hDH (hP i)
  choose tt htt using hat
  set t' : Fin q → ℕ := fun i => tt i % c with ht'
  have ft' : ∀ i, f (t' i) = a i := by intro i; simp only [ht']; rw [← hD.mod, htt]
  have aP : ∀ i, a i ∈ P i := by intro i; rw [hPM i]; simp
  have dP : ∀ i, d i ∈ P i := by
    intro i; rw [hPM i]; exact List.mem_append_left _ (List.mem_of_head? (hMh i))
  have wM : ∀ i, w i ∈ M i := fun i => List.mem_of_getLast? (hMl i)
  have tinj : Function.Injective t' := by
    intro i j hij
    by_contra hne
    have : a i = a j := by rw [← ft', ← ft', hij]
    exact hdisj i j hne _ (aP i) (this ▸ aP j)
  obtain ⟨s, hs, hsq, hs1, hs2⟩ := sort_pos hq t' tinj (fun i => Nat.mod_lt _ hc)
  refine ⟨s, hs, hsq, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi⟩ := hs1 j hj
    exact ⟨w i, hMH i _ (wM i), by rw [hi, ft']; exact (hwa i).symm⟩
  · intro i hi j hj hij
    obtain ⟨α, hα⟩ := hs1 i hi
    obtain ⟨β, hβ⟩ := hs1 j hj
    have hne : α ≠ β := by
      intro h; subst h; have := hs i j hij (by omega); omega
    have hdd : d α ≠ d β := fun h => hdisj α β hne _ (dP α) (h ▸ dP β)
    obtain ⟨X, hX, hXk⟩ := hDl _ (hdD α) _ (hdD β) hdd
    have hdM : ∀ x ∈ M α, x ∉ M β := by
      intro x hx hx'
      exact hdisj α β hne x (by rw [hPM α]; exact List.mem_append_left _ hx)
        (by rw [hPM β]; exact List.mem_append_left _ hx')
    rw [hα, hβ, ft', ft']
    exact ends_linked hC hDH (hMh α) (hMl α) (hMh β) (hMl β) (hwa α) (hwa β) (hMH α) (hMH β)
      (hMD α) (hMD β) (hMn α) (hMn β) (hMc α) (hMc β) hdM hX hXk hdd
  · intro i
    obtain ⟨j, hj, hji⟩ := hs2 i
    exact ⟨j, hj, by rw [hPM i, List.getLast?_concat, hji, ft']⟩

/-- **Linked-set theorem.** -/
lemma linked_contra (hD : Cy G c f) (hC : Comp G f H) {δ k : ℕ} (hδ : ∀ x, δ ≤ G.degree x)
    (hk : 1 ≤ k) (hkn : Fintype.card V + k * (k - 1) ≤ (k + 1) * δ) (hK : KSep G k)
    {D : Finset V} (hDH : D ⊆ H) (hDk : k + 1 ≤ D.card)
    (hDl : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ∃ X, HP G D x y X ∧ k ≤ X.length) : False := by
  set Cs := (Finset.range c).image f with hCs
  have hsepk := sep_ge hD hC hK hDH hDk
  have hHD : D.card ≤ H.card := Finset.card_le_card hDH
  have hk1 : k * (k - 1) + k = k * k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp; ring
  by_cases h : ∀ S : Finset V, (∀ l, ABP G D Cs l → ∃ x ∈ l, x ∈ S) → k + 1 ≤ S.card
  · obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs (k + 1) h
    obtain ⟨s, hs, hsq, hatt, hph, -⟩ := ends_sorted hD hC hDH hDl (by omega) P hP hdisj
    have := succ_deg hD hC (q := k + 1) (by omega) hs hsq hatt
      (fun i hi j hj hij => by simpa using hph i hi j hj hij)
    have hsum : (k + 1) * δ ≤ ∑ i ∈ Finset.range (k + 1), G.degree (f (s i + 1)) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) => hδ (f (s i + 1)))
      simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this
    have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    omega
  · push_neg at h
    obtain ⟨S, hS, hSk⟩ := h
    have hSc : S.card = k := le_antisymm (by omega) (hsepk S hS)
    obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs k (fun S' hS' => hsepk S' hS')
    obtain ⟨s, hs, hsq, hatt, hph, hend⟩ := ends_sorted hD hC hDH hDl hk P hP hdisj
    -- every separator vertex lies on one of the paths
    have hmeet : ∀ i, ∃ x ∈ P i, x ∈ S := fun i => hS _ (hP i).1
    choose σ hσP hσS using hmeet
    have σinj : Function.Injective σ := by
      intro i j hij; by_contra hne; exact hdisj i j hne _ (hσP i) (hij ▸ hσP j)
    have himg : Finset.univ.image σ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact hσS i
      · rw [Finset.card_image_of_injective _ σinj, hSc]; simp
    have onP : ∀ x ∈ S, ∃ i, x ∈ P i := by
      intro x hx; rw [← himg] at hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact ⟨i, hσP i⟩
    obtain ⟨v, hvD, hvS⟩ : ∃ v ∈ D, v ∉ S := by
      by_contra h'; push_neg at h'
      have := Finset.card_le_card (show D ⊆ S from h'); omega
    have hvH := hDH hvD
    have hN : ∀ t, G.Adj v (f t) → ∃ j < k, f t = f (s j) := by
      intro t hvt
      have hl : ABP G D Cs [v, f t] := ⟨by simp; intro h; exact hC.off v hvH t h.symm,
        by simp [hvt], ⟨v, hvD, rfl⟩, ⟨f t, hD.mem_cset t, rfl⟩⟩
      obtain ⟨x, hx, hxS⟩ := hS _ hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd hxS hvS
      · obtain ⟨i, hi⟩ := onP _ hxS
        obtain ⟨j, hj, hjl⟩ := hend i
        refine ⟨j, hj, ?_⟩
        have hne : P i ≠ [] := by intro h; rw [h] at hi; simp at hi
        have hsplit := List.dropLast_append_getLast hne
        rw [← hsplit] at hi
        rcases List.mem_append.mp hi with h1 | h1
        · exact absurd (hD.mem_cset t) ((hP i).2.2 _ h1)
        · simp at h1
          rw [List.getLast?_eq_getLast_of_ne_nil hne] at hjl
          simp at hjl; rw [h1, hjl]
    have hv := vert_deg hD hC hvH hN
    have hsd := succ_deg hD hC (q := k) hk hs hsq hatt
      (fun i hi j hj hij => (hph i hi j hj hij).mono (by omega))
    have hsum : k * δ ≤ ∑ i ∈ Finset.range k, G.degree (f (s i + 1)) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => hδ (f (s i + 1)))
      simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this
    have hvd := hδ v
    have e : (k + 1) * δ = k * δ + δ := by ring
    omega

end linked

/-! ## A long cycle in `H` is a linked set -/

section cyc

lemma HP.reverse' {D : Finset V} {x y : V} {X : List V} (h : HP G D x y X) : HP G D y x X.reverse :=
  ⟨List.nodup_reverse.mpr h.1, List.isChain_reverse.mpr (h.2.1.imp (fun _ _ h => h.symm)),
    fun z hz => h.2.2.1 z (List.mem_reverse.mp hz), by rw [List.head?_reverse]; exact h.2.2.2.2,
    by rw [List.getLast?_reverse]; exact h.2.2.2.1⟩

/-- Two positions `i < j` on a closed nodup chain `l`: the two arcs. -/
lemma arcs {l : List V} (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hcl : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y) {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    HP G l.toFinset l[i] l[j] ((l.drop i).take (j - i + 1)) ∧
      HP G l.toFinset l[j] l[i] (l.drop j ++ l.take (i + 1)) := by
  have hi : i < l.length := by omega
  constructor
  · refine ⟨(hnd.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _),
      chain_sub (chain_sub hch (List.drop_suffix _ _).isInfix) (List.take_prefix _ _).isInfix,
      fun z hz => List.mem_toFinset.mpr (List.mem_of_mem_drop (List.mem_of_mem_take hz)), ?_, ?_⟩
    · rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]; rfl
    · rw [List.getLast?_eq_getElem?]
      simp only [List.length_take, List.length_drop, List.getElem?_take, List.getElem?_drop]
      rw [show min (j - i + 1) (l.length - i) = j - i + 1 by omega]
      rw [if_pos (by omega), show i + (j - i + 1 - 1) = j by omega]
      exact List.getElem?_eq_getElem hj
  · have hdj : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd.sublist (List.drop_sublist _ _), hnd.sublist (List.take_sublist _ _), ?_⟩
      intro a ha b hb hab; subst hab
      have := List.disjoint_take_drop hnd (show i + 1 ≤ j by omega)
      exact this hb ha
    · rw [List.isChain_append]
      refine ⟨chain_sub hch (List.drop_suffix _ _).isInfix, chain_sub hch (List.take_prefix _ _).isInfix, ?_⟩
      intro a ha b hb
      have hne : l ≠ [] := by intro h; rw [h] at hj; simp at hj
      rw [List.getLast?_drop, if_neg (by omega)] at ha
      rw [List.head?_take, if_neg (by omega)] at hb
      exact hcl a ha b hb
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_toFinset.mpr (List.mem_of_mem_drop hz)
      · exact List.mem_toFinset.mpr (List.mem_of_mem_take hz)
    · rw [List.head?_append, hdj]; simp
    · rw [List.getLast?_append_of_ne_nil _ (List.ne_nil_of_length_pos (by simp; omega)),
        List.getLast?_eq_getElem?]
      simp only [List.length_take, List.getElem?_take]
      rw [show min (i + 1) l.length = i + 1 by omega, if_pos (by omega),
        show i + 1 - 1 = i by omega]
      exact List.getElem?_eq_getElem hi

/-- A closed path list in `H` with at least `2 k - 2` (and at least `k + 1`) vertices is linked. -/
lemma cyc_linked {H : Finset V} {k : ℕ} {l : List V} (hl : VL G H l)
    (hcl : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y) (hL : 2 * k ≤ l.length + 2) :
    ∀ x ∈ l.toFinset, ∀ y ∈ l.toFinset, x ≠ y → ∃ X, HP G l.toFinset x y X ∧ k ≤ X.length := by
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hy)
  have hij : i ≠ j := by intro h; subst h; exact hxy rfl
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · obtain ⟨h1, h2⟩ := arcs hl.1 hl.2.1 hcl h hj
    by_cases hlen : k ≤ j - i + 1
    · refine ⟨_, h1, ?_⟩
      simp only [List.length_take, List.length_drop]; omega
    · refine ⟨_, h2.reverse', ?_⟩
      simp only [List.length_reverse, List.length_append, List.length_drop, List.length_take]
      omega
  · obtain ⟨h1, h2⟩ := arcs hl.1 hl.2.1 hcl h hi
    by_cases hlen : k ≤ i - j + 1
    · refine ⟨_, h1.reverse', ?_⟩
      simp only [List.length_reverse, List.length_take, List.length_drop]; omega
    · refine ⟨_, h2, ?_⟩
      simp only [List.length_append, List.length_drop, List.length_take]; omega

end cyc

/-! ## The case `k = 1` and the case analysis -/

section main

variable [DecidableRel G.Adj]

/-- `k = 1` (Dirac): two different attachments give two successors of small degree sum; a single
attachment gives a vertex of `H` and the successor of the attachment. -/
lemma k1_contra (hD : Cy G c f) (hC : Comp G f H) {δ : ℕ} (hδ : ∀ x, δ ≤ G.degree x)
    (hkn : Fintype.card V ≤ 2 * δ) (hK : KSep G 1) (hH : H.Nonempty) : False := by
  have hc : 0 < c := by have := hD.three; omega
  obtain ⟨v, hv⟩ := hH
  have hHc : 1 ≤ H.card := Finset.card_pos.mpr ⟨v, hv⟩
  by_cases h2 : ∃ t1 t2, Att G f H t1 ∧ Att G f H t2 ∧ f t1 ≠ f t2
  · obtain ⟨t1, t2, h1, h2', hne⟩ := h2
    have e1 : f (t1 % c) = f t1 := (hD.mod t1).symm
    have e2 : f (t2 % c) = f t2 := (hD.mod t2).symm
    have a1 : Att G f H (t1 % c) := by rw [Att, e1]; exact h1
    have a2 : Att G f H (t2 % c) := by rw [Att, e2]; exact h2'
    have hne' : t1 % c ≠ t2 % c := fun h => hne (by rw [← e1, ← e2, h])
    have l1 := Nat.mod_lt t1 hc
    have l2 := Nat.mod_lt t2 hc
    set a := min (t1 % c) (t2 % c)
    set b := max (t1 % c) (t2 % c)
    have ha : Att G f H a := by
      simp only [a]; rcases le_total (t1 % c) (t2 % c) with h | h
      · rw [min_eq_left h]; exact a1
      · rw [min_eq_right h]; exact a2
    have hb : Att G f H b := by
      simp only [b]; rcases le_total (t1 % c) (t2 % c) with h | h
      · rw [max_eq_right h]; exact a2
      · rw [max_eq_left h]; exact a1
    have hab : a < b := by simp only [a, b]; omega
    have hbc : b < c := by simp only [b]; omega
    set s : ℕ → ℕ := fun j => if j = 0 then a else if j = 1 then b else a + c with hs
    have := succ_deg hD hC (q := 2) (s := s) (by omega)
      (by intro i j hij hj; simp only [hs]; split_ifs <;> omega) (by simp [hs])
      (by intro i hi; simp only [hs]; split_ifs
          · exact ha
          · exact hb
          · omega)
      (by
        intro i hi j hj hij
        have hi0 : i = 0 := by omega
        have hj1 : j = 1 := by omega
        subst hi0; subst hj1
        simp only [hs, if_true, if_neg one_ne_zero]
        obtain ⟨z, hz, hza⟩ := ha
        obtain ⟨z', hz', hzb⟩ := hb
        exact ph_of hC hz hz' hza hzb)
    have d0 := hδ (f (s 0 + 1))
    have d1 := hδ (f (s 1 + 1))
    simp [Finset.sum_range_succ] at this
    omega
  · push_neg at h2
    by_cases h1 : ∃ t, Att G f H t
    · obtain ⟨t0, ht0⟩ := h1
      have hv' := vert_deg hD hC hv (q := 1) (s := fun _ => t0)
        (fun t ht => ⟨0, by omega, h2 t t0 ⟨v, hv, ht.symm⟩ ht0⟩)
      have hu := succ_deg hD hC (q := 1) (s := fun j => if j = 0 then t0 else t0 + c) le_rfl
        (by intro i j hij hj; have : i = 0 := by omega
            have : j = 1 := by omega
            subst_vars; simp; omega)
        (by simp)
        (by intro i hi; have : i = 0 := by omega
            subst this; simpa using ht0)
        (by intro i hi j hj hij; omega)
      have d0 := hδ v
      have d1 := hδ (f (t0 + 1))
      simp at hu
      omega
    · push_neg at h1
      refine hK ∅ (by simp) H (by simp) ?_ ⟨v, hv⟩ (f 0) (by simp) (fun h => hC.off _ h 0 rfl)
      intro x hx y hxy _
      rcases hC.cl x hx y hxy with h | ⟨t, rfl⟩
      · exact h
      · exact absurd ⟨x, hx, hxy.symm⟩ (h1 t)

/-- The combinatorial core: no component of `G - C` holds a path list with `k` vertices. -/
theorem coreK (hD : Cy G c f) (hC : Comp G f H) {δ k : ℕ} (hδ : ∀ x, δ ≤ G.degree x)
    (hk : 1 ≤ k) (hkn : Fintype.card V + k * (k - 1) ≤ (k + 1) * δ)
    (hn : 5 * k ^ 2 + 7 * k ≤ Fintype.card V) (hK : KSep G k) {P : List V} (hP : VL G H P)
    (hPk : k ≤ P.length) : False := by
  have hk1 : k * (k - 1) + k = k * k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp; ring
  have hδ6 : 6 * k ≤ δ := by
    have : (k + 1) * (6 * k) ≤ (k + 1) * δ := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hHne : H.Nonempty := by
    obtain ⟨x, P', rfl⟩ : ∃ x P', P = x :: P' := by
      cases P with
      | nil => simp at hPk; omega
      | cons x P' => exact ⟨x, P', rfl⟩
    exact ⟨x, hP.2.2 x (by simp)⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    exact k1_contra hD hC hδ (by simpa using hkn) hK hHne
  -- a longest path list in `H`
  classical
  set pm := Nat.findGreatest (fun m => ∃ l, VL G H l ∧ l.length = m) H.card with hpm
  obtain ⟨Q, hQ, hQl⟩ : ∃ l, VL G H l ∧ l.length = pm :=
    Nat.findGreatest_spec (P := fun m => ∃ l, VL G H l ∧ l.length = m) hP.length_le ⟨P, hP, rfl⟩
  have hmax : ∀ l, VL G H l → l.length ≤ Q.length := by
    intro l hl; rw [hQl]; exact Nat.le_findGreatest hl.length_le ⟨l, hl, rfl⟩
  have hpk : k ≤ Q.length := (hPk.trans (hmax P hP))
  have hQ1 : Q ≠ [] := by intro h; rw [h] at hpk; simp at hpk; omega
  have hHc : Q.length ≤ H.card := hQ.length_le
  rcases Nat.lt_or_ge (5 * k + 1) Q.length with hp5 | hp5
  · by_cases hcy : ∃ l, VL G H l ∧ (∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y) ∧
        3 ≤ l.length ∧ 2 * k ≤ l.length + 2
    · obtain ⟨l, hl, hcl, h3, h2k⟩ := hcy
      have hDc : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl.1
      exact linked_contra hD hC hδ (by omega) hkn hK (D := l.toFinset)
        (fun z hz => hl.2.2 z (List.mem_toFinset.mp hz)) (by omega) (cyc_linked hl hcl h2k)
    · push_neg at hcy
      obtain ⟨R, u, hr, hdisj, -, hsum⟩ := residual H Q hQ hQ1 hmax (max (2 * k - 3) 2)
        (le_max_right _ _) (by
          intro l hl h3 hcl
          have := hcy l hl hcl h3
          omega)
      exact resid_contra hD hC hδ hk2 hδ6 hkn ⟨hQ, hr, hdisj⟩ hpk hsum
        (Or.inr ⟨by omega, by omega⟩)
  · obtain ⟨R, u, hr, hdisj, hsum, -⟩ := residual H Q hQ hQ1 hmax H.card (by omega)
      (fun l hl _ _ => hl.length_le)
    exact resid_contra hD hC hδ hk2 hδ6 hkn ⟨hQ, hr, hdisj⟩ hpk hsum
      (Or.inl ⟨hp5, by omega⟩)

end main

/-! ## From the statement to the combinatorial core -/

section glue

variable [DecidableRel G.Adj]

/-- The periodic enumeration of a closed walk. -/
def cyc {a : V} (C : G.Walk a a) : ℕ → V := fun t => C.getVert (t % C.length)

lemma cy_of {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference) :
    Cy G C.length (cyc C) := by
  have hc := hC.three_le_length
  refine ⟨hc, fun t => by simp [cyc], fun t => ?_, fun i j hi hj h => ?_, fun l hnd hcl => ?_⟩
  · simp only [cyc]
    have hlt : t % C.length < C.length := Nat.mod_lt _ (by omega)
    have hm : (t + 1) % C.length = (t % C.length + 1) % C.length := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < C.length by omega)]
    rw [hm]
    by_cases h : t % C.length + 1 < C.length
    · rw [Nat.mod_eq_of_lt h]; exact C.adj_getVert_succ hlt
    · have h' : t % C.length + 1 = C.length := by omega
      rw [h', Nat.mod_self, Walk.getVert_zero]
      have := C.adj_getVert_succ hlt
      rwa [h', Walk.getVert_length] at this
  · simp only [cyc, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
    exact hC.getVert_injOn' (by simp; omega) (by simp; omega) h
  · by_cases h3 : l.length < 3
    · omega
    · obtain ⟨b, w, hw, hwl⟩ := cycle_of_CL l hnd hcl (by omega)
      rw [← hwl, hlong]; exact le_circumference w hw

lemma mem_support_cyc {a : V} (C : G.Walk a a) (hC : C.IsCycle) (y : V) :
    y ∈ C.support ↔ ∃ t, cyc C t = y := by
  have hc := hC.three_le_length
  constructor
  · intro hy
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hy
    rcases Nat.lt_or_ge n C.length with h | h
    · exact ⟨n, by simp [cyc, Nat.mod_eq_of_lt h, hn]⟩
    · refine ⟨0, ?_⟩
      have : n = C.length := by omega
      subst this
      simp [cyc, ← hn, Walk.getVert_length]
  · rintro ⟨t, rfl⟩; exact Walk.getVert_mem_support _ _

lemma reach_mem {s : Set V} {x y : s} (w : (G.induce s).Walk x y) {z : s} (hz : z ∈ w.support) :
    (G.induce s).Reachable x z := ⟨w.takeUntil z hz⟩

def offWalk {a b : V} (w : G.Walk a b) : Set V := {v | v ∉ w.support}

theorem mainK {k : ℕ} (hk : 1 ≤ k) (hn : 5 * k ^ 2 + 7 * k ≤ Fintype.card V)
    (hG : IsKConnected G k)
    (hd : ((Fintype.card V : ℝ) + k * (k - 1)) / (k + 1) ≤ G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference)
    (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v)
    (hP : P.IsPath) : P.support.length + 1 ≤ k := by
  by_contra hlt
  push_neg at hlt
  have hD := cy_of C hC hlong
  have hsupp := mem_support_cyc C hC
  have mem_s : ∀ y, y ∈ offWalk C ↔ y ∉ C.support := fun y => Iff.rfl
  classical
  obtain ⟨H, hH⟩ : ∃ H : Finset V, H = Finset.univ.filter
      (fun y => ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩) := ⟨_, rfl⟩
  have memH : ∀ y, y ∈ H ↔ ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩ := by
    intro y; simp [hH]
  have hComp : Comp G (cyc C) H := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx t ht
      obtain ⟨hxs, -⟩ := (memH x).mp hx
      exact (mem_s x).mp hxs ((hsupp x).mpr ⟨t, ht⟩)
    · intro x hx y hxy
      obtain ⟨hxs, hr⟩ := (memH x).mp hx
      by_cases hy : y ∈ C.support
      · exact Or.inr ((hsupp y).mp hy)
      · left
        have hys : y ∈ offWalk C := (mem_s y).mpr hy
        exact (memH y).mpr ⟨hys, hr.trans (Adj.reachable (G := G.induce (offWalk C))
          (u := ⟨x, hxs⟩) (v := ⟨y, hys⟩) hxy)⟩
    · intro x hx y hy
      obtain ⟨hxs, hrx⟩ := (memH x).mp hx
      obtain ⟨hys, hry⟩ := (memH y).mp hy
      obtain ⟨w⟩ := hrx.symm.trans hry
      obtain ⟨p, hp⟩ := w.toPath
      refine ⟨p.support.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
      · exact hp.support_nodup.map Subtype.val_injective
      · exact (List.isChain_map Subtype.val).mpr p.isChain_adj_support
      · intro z hz
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact (memH z').mpr ⟨z'.2, hrx.trans (reach_mem p hz')⟩
      · rw [Walk.support_eq_cons, List.map_cons, List.head?_cons]
      · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
          Walk.getLast_support]; rfl
  have hVL : VL G H (P.support.map Subtype.val) := by
    refine ⟨hP.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr P.isChain_adj_support, ?_⟩
    intro z hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (memH z').mpr ⟨z'.2, reach_mem P hz'⟩
  have hKs : KSep G k := by
    intro S hS X hXS hXcl hXne y hyS hyX
    obtain ⟨x, hx⟩ := hXne
    have hconn := hG.2 S (by omega)
    obtain ⟨w⟩ := hconn.preconnected ⟨x, hXS x hx⟩ ⟨y, hyS⟩
    have key : ∀ (p q : ((S : Set V)ᶜ : Set V)) (w : (G.induce ((S : Set V)ᶜ)).Walk p q),
        p.1 ∈ X → q.1 ∈ X := by
      intro p q w
      induction w with
      | nil => exact id
      | @cons p0 p1 q h w ih =>
        intro hp
        exact ih (hXcl _ hp _ h (fun h' => p1.2 h'))
    exact hyX (key _ _ w hx)
  have hkn : Fintype.card V + k * (k - 1) ≤ (k + 1) * G.minDegree := by
    have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < k + 1)).mp hd
    have h2 : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hk]; simp
    rw [h2] at h1
    have h' : ((Fintype.card V + k * (k - 1) : ℕ) : ℝ) ≤ (((k + 1) * G.minDegree : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  exact coreK hD hComp (fun x => G.minDegree_le_degree x) hk hkn hn hKs hVL
    (by rw [List.length_map]; omega)

end glue

end OMA.BondyK


#print axioms OMA.BondyK.mainK
#print axioms OMA.BondyK.linked_contra
#print axioms OMA.BondyK.cyc_linked
