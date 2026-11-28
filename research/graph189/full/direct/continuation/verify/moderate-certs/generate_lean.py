"""Emit exact Rejection trees which Lean checks against finite concrete graph intervals."""
from pathlib import Path
import json,sys
here=Path(__file__).resolve().parent
degree=int(sys.argv[1])
cases=json.loads((here/f'traces-{degree}.json').read_text())
lines=['import Graph189CompletionRows','', f'namespace Graph189ModerateK{degree}',
       'open SimpleGraph Graph189Completion','','set_option maxRecDepth 24000','set_option maxHeartbeats 6000000','']
for c in cases:
    name=c['id'];n=c['n'];z=n-1;k=c['k'];p=c['p'];f=n-(k+1)//2-1;d=p+1
    low=c['lower'];up=c['upper'].copy();uterm=f'(maskGraph {n} {up})'
    lines+= [f'def {name}L := maskGraph {n} {low}',f'def {name}U := maskGraph {n} {up}',
         f'theorem {name} : Rejection ({z} : Fin {n}) {f} {d} {k} (fun v => if v={z} then 2 else {k}) {name}L {name}U := by',
        f'  unfold {name}L {name}U']
    def path(s,prefix,extra):
        root,*rest=s['vertices']
        chain='(by decide)' if not extra else '(by simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, sup_adj, edge_adj, maskGraph, fromRel_adj]; decide)'
        if s['scope']=='G':
            return [prefix+f'exact Or.inl (hasPath_of_list (a := {root}) (l := {rest}) {chain} (by decide) (by decide))']
        return [prefix+f'exact Or.inr (hasPath_induce_of_list (a := {root}) (l := {rest}) (by decide) {chain} (by decide) (by decide))']
    for s in c['steps']:
        a,b=s['a'],s['b'];lines += [f'  apply Rejection.forbid {a} {b}']+path(s,'  · ',True)
        up[a]&=~(1<<b);up[b]&=~(1<<a);uterm=f'({uterm} \\ edge {a} {b})'
    end=c['end']
    if end['kind']=='path':
        lines+=['  apply Rejection.path']+path(end,'  ',False)
    else:
        lines += [f'  have hu : RowsRepresent (maskRows {up}) {uterm} := by',
                  '    unfold RowsRepresent',
                  '    simp only [maskRows, Finset.mem_filter, Finset.mem_univ, true_and, sdiff_adj, edge_adj, maskGraph, fromRel_adj]',
                  '    decide']
        if end['kind']=='cut':
            left=end['left'];right=end['right'];v=end['v']
            lines += [f'  let C : Finset (Fin {n}) := {{{", ".join(map(str,left))}}}',
                f'  exact Rejection.cut_row hu {v} C (a := {left[0]}) (b := {right[0]}) (by decide) (by decide) (by decide) (by decide) (by decide)']
        elif end['kind']=='degree':
            lines += [f'  exact Rejection.degree_row hu {end["v"]} (by decide)']
        else:
            assert end['kind']=='even'
            lines += [f'  have hl : RowsRepresent (maskRows {low}) (maskGraph {n} {low}) := maskRows_represent _ (by decide) (by decide)',
                      f'  exact Rejection.even {end["v"]} (hl.excess_of_pairs hu {end["v"]} {[(a,b) for a,b in end["pairs"]]} (by decide) (by decide) (by decide))' ]
    lines+=['']
lines+=[f'#print axioms {r["id"]}' for r in cases]+[f'end Graph189ModerateK{degree}']
(here/f'Graph189ModerateK{degree}.lean').write_text('\n'.join(lines)+'\n')
