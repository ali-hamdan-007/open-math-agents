import Graph189ScalarReplay

namespace Graph189ReplaySearch

private def f (h k a : ℤ) : ℤ := a*(h-a-k)

private def step (s k h : ℤ) (_ : ℕ) (p : ℤ × ℤ) : Id (ForInStep (ℤ × ℤ)) :=
  let a := p.1
  let b := p.2
  if a+1 ≥ b then .done (a,b)
  else
    let m := (a+b)/2
    if decide (f h k m ≤ s*k*k) = true then .yield (m,b)
    else .yield (a,m)

/-- Two rejected endpoints of a concave quadratic cannot enclose an accepted integer. -/
private theorem below_rejection {h k t a x e : ℤ} (he : t < f h k e)
    (ha : t < f h k a) (hx : f h k x ≤ t) (hxe : x ≤ e) : x < a := by
  by_contra! hax
  by_cases same : a = x
  · subst a
    omega
  by_cases h' : x = e
  · subst e
    omega
  have p := mul_pos (show 0 < e-x by omega) (show 0 < f h k a - f h k x by omega)
  have q := mul_pos (show 0 < x-a by omega) (show 0 < f h k e - f h k x by omega)
  have r := mul_nonneg (mul_nonneg (sub_nonneg.mpr hxe) (sub_nonneg.mpr hax))
    (sub_nonneg.mpr (hax.trans hxe))
  dsimp [f] at p q
  nlinarith only [p,q,r]

private theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

private theorem id_bind {α β : Type} (a : Id α) (g : α → Id β) : (a >>= g) = g a := rfl

private theorem loop {s k h x e : ℤ} (he : s*k*k < f h k e)
    (hx : f h k x ≤ s*k*k) (hxe : x ≤ e)
    (ticks : List ℕ) (a b : ℤ)
    (hxb : x < b) (hsize : b-a-1 ≤ (ticks.length : ℤ)) :
    x ≤ (forIn ticks (a,b) (step s k h) : Id (ℤ × ℤ)).1 := by
  induction ticks generalizing a b with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero] at hsize
    simpa only [List.forIn_nil, id_pure] using (show x ≤ a by omega)
  | cons j rest ih =>
    rw [List.forIn_cons]
    simp only [List.length_cons, Nat.cast_succ] at hsize
    by_cases done' : a+1 ≥ b
    · simp [step, done', id_bind, id_pure]
      omega
    · let m := (a+b)/2
      have hm1 : a < m := by dsimp [m]; omega
      have hm2 : m < b := by dsimp [m]; omega
      by_cases hm : f h k m ≤ s*k*k
      · have hr := ih m b hxb (by omega)
        simpa [step, done', m, hm, id_bind, id_pure] using hr
      · have hr := ih a m (below_rejection he (lt_of_not_ge hm) hx hxe) (by omega)
        simpa [step, done', m, hm, id_bind, id_pure] using hr

/-- Every feasible smaller side is at most the actual return value of the
finite projection's imperative binary search. -/
theorem le_smallerSide {s k h x : ℤ} (hsmall : x ≤ h/2)
    (hprod : x*(h-x-k) ≤ s*k*k) : x ≤ Graph189ScalarReplay.smallerSide s k h := by
  let e := h/2
  have form : Graph189ScalarReplay.smallerSide s k h =
      if decide (f h k e ≤ s*k*k) = true then e
      else (forIn ([:e.toNat] : Std.Legacy.Range) (0,e) (step s k h) : Id (ℤ × ℤ)).1 := rfl
  rw [form]
  by_cases he : f h k e ≤ s*k*k
  · simp [he, e, hsmall]
  · rw [if_neg (by simpa using he), Std.Legacy.Range.forIn_eq_forIn_range']
    have hxe : x < e := by
      change x ≤ e at hsmall
      change f h k x ≤ s*k*k at hprod
      by_contra! h
      have : x = e := by omega
      exact he (this ▸ hprod)
    apply loop (lt_of_not_ge he) hprod hsmall _ _ _ hxe
    simp [Std.Legacy.Range.size]

/-- In the low-on-cut calculation the two high populations sum to h. -/
theorem actual_smallerSide {s k x y : ℤ} (hxy : x ≤ y)
    (prod : x*y ≤ k*x+s*k*k) : x ≤ Graph189ScalarReplay.smallerSide s k (x+y) := by
  apply le_smallerSide (by omega)
  nlinarith only [prod]

#print axioms le_smallerSide
#print axioms actual_smallerSide
end Graph189ReplaySearch
