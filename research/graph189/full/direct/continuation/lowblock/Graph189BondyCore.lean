import Graph189UpstreamBondy

/-- The focused extraction and full upstream source use the same exterior
vertex set under different names. -/
abbrev Arxiv.«2606.03696».offWalk {V : Type*} {G : SimpleGraph V} {x y : V} (q : G.Walk x y) : Set V :=
  OMA.BondyK.offWalk q
