import Graph189FiniteDomain

namespace Graph189ScalarReplay
open Graph189FiniteDomain

def ceilDiv (a b : Int) : Int := -((-a)/b)

def widthPossible (k n : Int) : Bool :=
  let low := k + max 0 (ceilDiv (n-3*k-1) k)
  let f := fun d => (n-d-k-2)*(2*(n-2*k)+k*(d-k)) - (k+1)*k*d
  n ≤ 4*k+2 || (low ≤ 3*k && min (f low) (f (3*k)) ≤ 0)

def orderBounds (s k : Int) : Int × Int := Id.run do
  let mut lo := (s+1)*(k-s+2)-1
  if k ≥ 4*s then
    lo := max lo (min ((s+2)*(k-2*s+2)-1) (ceilDiv (k*(k-1)) 4))
  let mut hi := 2*k+1+s*k*k/(k-s)
  if k > 6*(s-1) then
    hi := min hi (ceilDiv ((2*s+3)*k) 2 + 2*s+1)
    hi := min hi (ceilDiv (((s+1)*(s-2)+3)*k) (s-2) + 2*s+2)
  return (lo,hi)

def smallerSide (s k h : Int) : Int := Id.run do
  let endPt := h/2
  let accept := fun x => decide (x*(h-x-k) ≤ s*k*k)
  if accept endPt then return endPt
  let mut lo := 0
  let mut hi := endPt
  for _ in [:endPt.toNat] do
    if lo+1 ≥ hi then break
    let x := (lo+hi)/2
    if accept x then lo := x else hi := x
  return lo

def maximumExcess (k n : Int) : Option Int := Id.run do
  let mut low := max 0 (ceilDiv (n-3*k-1) (k-2))
  for t in [:((k-1)/2+1).toNat] do
    let e : Int := t
    if n ≤ 3*k+1+e*(k-e-1) then break
    low := max low (e+1)
  for j in [:(2*k-low+1).toNat] do
    let e := 2*k-(j : Int)
    let w := ceilDiv (2*(n-2*k)+k*e) (k+1)
    if w*(n-2*k-e-2) ≤ k*(k+e) then return some e
  return none

def viable (s k n : Int) : Bool := Id.run do
  let some e := maximumExcess k n | return false
  let debit := (s+1)*k-n+smallerSide s k (n-s)+s
  let mut deficit : Int := 0
  for rr in [:s.toNat] do
    let r := (rr : Int)+1
    if (r-1)*(k-s+1) ≤ debit+r*(e+s-1) then
      deficit := max deficit (min (r-1) ((2*k+(k+1)*r-n)/k))
  if 2*(k-deficit-1)>3*s && (k-2*deficit-2)/2+1≥s+1 && 4*n<k*(k-1) then
    return n ≥ (s+2)*(k-deficit-s+1)-1
  return true

/-- Recompute all enclosing order intervals from the finite scalar inequalities.
The unrounded maximum-width test is monotone in the order, allowing the early
exit below. The rounded, cut-deficit test is checked at every remaining order. -/
def projection : List Band := Id.run do
  let mut out := #[]
  for ss in [5:100] do
    let s : Int := ss
    for kk in [max 26 (3*ss+1):4*ss*ss+8*ss-2] do
      let k : Int := kk
      let (lo,hi) := orderBounds s k
      if lo > hi || !widthPossible k lo then continue
      let mut first : Option Int := none
      let mut last := lo
      for index in [:(hi-lo+1).toNat] do
        let n := lo+(index : Int)
        if !widthPossible k n then break
        if viable s k n then
          if first.isNone then first := some n
          last := n
      if let some n := first then
        out := out.push ⟨s,k,n,last,smallerSide s k (n-s-1)⟩
  return out.toList

/- Reaching this command checks the full projection by executing Lean's
evaluator, independently of Python. The terminal arithmetic theorem imported
above is separately checked by kernel reduction. -/
#guard projection == terminalBands
#eval IO.println "The recomputed projection equals all 102 recorded intervals and population caps."

end Graph189ScalarReplay
