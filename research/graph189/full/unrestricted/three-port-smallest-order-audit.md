# Independent audit of the `(a,s)=(3,3)`, `h=2k-3` closure

This audits the equality case in `degree-five-three-four-ports.md` under
the standing hypotheses `k>=7`.  Here `|K|=k-3`, there is no fourth layer,
`D=P union R` has order

    3+(2k-3)=2k,

and every vertex of `R` has degree at least `k`, all inside `D`.

After adjoining either the degree-two marker used in the three-active-port
case or the leaf used in the two-active-port case, the augmented graph has
order `2k+1`.  The Hamilton-path closure threshold is therefore `2k`.
Every missing `R-R` edge has endpoint degree sum at least `2k`, so closure
does make `R` a clique while preserving existence of a spanning path.  No
edge used outside `R` in the displayed routes is a closure edge.

The two preliminary consequences of 2-connectivity are valid:

1. At least two ports meet `R`; otherwise deleting the unique active port
   separates the nonempty residual `R` from the shell.
2. The union of the port neighbourhoods in `R` has size at least two;
   otherwise deleting its sole member separates `R` minus that member from
   the shell.  This remainder is nonempty because `|R|=2k-3>=11`.

If exactly two ports `p,q` meet `R`, connectedness of `D` forces the inactive
port `t` to be adjacent to `p` or `q`; relabel so `tp` is an edge.  The two
nonempty sets `N_R(p),N_R(q)` have union of size at least two, hence possess
distinct representatives `x,y`.  In the closed graph

    leaf,t,p,x, (all of R ending at y),q

is a spanning path.  During closure reversal the leaf remains an endpoint,
because it retains degree one.  Deleting it exposes `t` as an endpoint, and
concatenating at an anchor adjacent to `t` with a prescribed shell path is
valid.

If all three ports meet `R`, 2-connectivity forces the edges from `D` to the
shell to use at least two distinct anchors; otherwise their sole anchor is a
cut vertex.  Therefore two ports `p,q` can be assigned distinct anchor
neighbours.  With `t` the third port, swapping `p,q` if necessary ensures

    |N_R(q) union N_R(t)| >= 2:

failure for both choices would make all three nonempty port neighbourhoods
the same singleton, contrary to item 2.  Thus `q,t` have distinct
representatives `x,y`, and the closed marked graph has the spanning path

    p,b,q,x, (all of R ending at y),t.

After closure reversal, the marker `b` either is an endpoint, or is internal
with path-neighbours exactly `p,q`, since these are its only graph
neighbours.  The manuscript's two shell expansions cover these exhaustive
possibilities.  In the internal case the previously assigned distinct
anchors give the prescribed shell endpoints; in the endpoint case any
second anchor distinct from the incident port anchor suffices.

Finally, the shell lemma itself uses an augmented shell of order
`k-a+7=k+4`.  A `K` vertex has shell degree at least `k`, and an anchor has
shell degree at least `k-3`, so every missing anchor--`K` pair has degree
sum at least `2k-3>=k+4` for `k>=7`.  The completed shell route has enough
`K` vertices because `|K|=k-3>=4`.

**Conclusion:** the `(3,3)`, `h=2k-3` equality closure is correct as written;
no extra hypothesis or endpoint-preservation claim is needed.
