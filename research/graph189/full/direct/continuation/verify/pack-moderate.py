"""Emit the exact moderate Graph 189 child from its checked declaration sources."""
import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
import re

STEP = "WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1"
R2 = "OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2"
TARGET = R2 + "_H2_R1.H1"
ROOT = "Graph189ModerateComplete.moderate"
CMD = re.compile(r"^(?:@\[[^\]]+\]\s*)?(?:private\s+|protected\s+|public\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([\w'][\w'?!]*(?:\.[\w'][\w'?!]*)*)")
CONTEXT = re.compile(r"^(?:module|(?:public\s+)?import|(?:public\s+|noncomputable\s+)?section|end|namespace|open|variable|universe|omit|include|set_option|attribute|#\w+|@\[)")
IMPORT = re.compile(r"^(?:public\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)
IDENT = re.compile(r"[\w'][\w'?!]*(?:\.[\w'][\w'?!]*)*")
CREDITS = """-- Graph 189, moderate two-connected case, by @ali-hamdan-007 and contributors.
-- R2 and the short-order proof are by @carl2sheriff (PR 22587), with R1
-- path and metric arguments by @computerfreak97 (PR 2971) and philipsaint.
-- The linked-set argument of Ma, Ning and Zhao is formalized by @koolkao (PR 7971).
-- Source and full provenance: github.com/ali-hamdan-007/open-math-agents,
-- branch research/parallel-lean-results, research/graph189/full/direct/continuation.
"""
def uncomment(s):
    result = []
    i = depth = 0
    while i < len(s):
        if s.startswith("/-", i):
            depth += 1
            result.append(" ")
            i += 2
        elif depth and s.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and s.startswith("--", i):
            end = s.find("\n", i)
            i = len(s) if end < 0 else end
        else:
            if not depth or s[i] == "\n":
                result.append(s[i])
            i += 1
    assert depth == 0
    return "".join(result)

@dataclass(eq=False)
class Command:
    module: str
    start: int
    end: int
    text: str
    name: str = ""
    namespace: str = ""
    private: bool = False

def parse(module, source):
    lines = uncomment(source).splitlines()
    cuts = [i for i, line in enumerate(lines) if CMD.match(line) or CONTEXT.match(line)]
    cuts.append(len(lines))
    commands = []
    scope = []
    for a, b in zip(cuts, cuts[1:]):
        chunk = "\n".join(lines[a:b]).strip("\n").rstrip()
        first = lines[a]
        name = ""
        if match := CMD.match(first):
            name = ".".join(item for item in [*scope,match[2]] if item)
        commands.append(Command(module,a+1,b,chunk,name,".".join(filter(None,scope)),"private " in first))
        if first.startswith("namespace "):
            scope.append(first.split()[1])
        elif re.match(r"^(?:noncomputable )?section\b", first):
            scope.append("")
        elif re.match(r"^end\b", first):
            if scope: scope.pop()
    return commands

def in_official(c):
    return c.module == "Graph189ParentFocused" and (
        c.name.startswith(R2+".") or c.name.startswith(R2+"_H2_R1."))

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("build", type=Path, help="focused/pinned module source snapshot")
    p.add_argument("output", type=Path)
    p.add_argument("--kernel-only",action="store_true",help="measure only declarations occurring in the elaborated proof and its transitive types")
    p.add_argument("--leaf", type=int, choices=(1,2,3,4), help="package a hypothesis of the moderate four-case reduction")
    p.add_argument("--checkout-sources",action="store_true",help="use the source checkout except for the generated parent module")
    p.add_argument("--root", default=ROOT, help="fully qualified statement implementing the exact child")
    p.add_argument("--dependencies", type=Path, help="TSV produced by extract-kernel-deps.py")
    args = p.parse_args()
    base = R2 + "_H2_R1"
    if args.leaf:
        args.root = "Graph189ModerateSplitProofs." + ("short","five","six","seven")[args.leaf-1]
        base += "_H1_R1"
    target = base + (f".H{args.leaf}" if args.leaf else ".H1")
    graph = Path(__file__).resolve().parents[4]
    files = {}
    for f in sorted(graph.rglob("*.lean"),key=lambda f: ("continuation" not in f.parts,"verify" not in f.parts,len(f.parts),str(f))):
        files.setdefault(f.stem,f)
    for f in graph.parent.glob("*.lean"): files.setdefault(f.stem,f)
    modules = {}
    def visit(n):
        if n in modules: return
        candidate = args.build / (n+".lean")
        source = (candidate if candidate.exists() and (not args.checkout_sources or n=="Graph189ParentFocused" or n not in files) else files[n]).read_text()
        for dep in IMPORT.findall(uncomment(source)):
            if dep.startswith("Graph189"): visit(dep)
        modules[n] = parse(n,source)
    visit(args.root.split(".")[0])
    by_name = defaultdict(list)
    by_leaf = defaultdict(list)
    all_decls = []
    for commands in modules.values():
        for c in commands:
            if c.name:
                by_name[c.name].append(c)
                by_leaf[c.name.rsplit(".",1)[-1]].append(c)
                all_decls.append(c)
    # The historical focused parent inlined a few of the same cut-vertex
    # and trace-closure sources that the modular replay imports separately.
    canonical = {}
    for items in by_name.values():
        for item in items:
            if item.module != "Graph189ParentFocused": continue
            copy = next((other for other in items if other.module!=item.module and other.text==item.text),None)
            if copy is not None:
                canonical[item]=copy
    opens = {}
    for module, records in modules.items():
        opened = []
        for r in records:
            if r.text.startswith("open "):
                opened.extend(n for n in r.text.split()[1:] if re.fullmatch(r"[\w.]+",n) and n!="in")
        opens[module] = list(dict.fromkeys(opened))
    chosen = set()
    pending = list(by_name[args.root])
    if not pending: raise SystemExit(f"unknown root {args.root}")
    if args.dependencies:
        for entry in args.dependencies.read_text().splitlines():
            mod,name,line,_body = entry.split("\t")
            records = modules[mod]
            if int(line):
                matches=[c for c in records if c.name and c.start<=int(line)<=c.end]
            else: matches=[]
            if not matches:
                matches=[c for c in records if c.name and (name==c.name or name.startswith(c.name+"."))]
            pending.extend(matches)
    while pending:
        c = pending.pop()
        c = canonical.get(c,c)
        if c in chosen or in_official(c) or (args.leaf and c.module=="Graph189ModerateSplit"): continue
        chosen.add(c)
        if args.kernel_only: continue
        for tok in set(IDENT.findall(c.text)):
            if tok in by_name:
                pending.extend(by_name[tok])
                continue
            ns = c.namespace.split(".")
            prefixes = [".".join(ns[:i]) for i in range(len(ns),0,-1)] + opens[c.module]
            scoped = [v for prefix in prefixes for v in by_name.get(prefix+"."+tok,())]
            if scoped:
                pending.extend(scoped)
                continue
            if "." in tok:
                continue
            local = [v for v in by_leaf.get(tok,[]) if v.module==c.module and v.namespace==c.namespace]
            if local:
                pending.extend(local)
            elif not args.dependencies:
                pending.extend(v for v in by_leaf.get(tok,[]) if v.module==c.module)
    counts = Counter(c.name for c in chosen)
    rename = defaultdict(dict)
    for c in chosen:
        if counts[c.name]>1 and c.private:
            leaf=c.name.rsplit(".",1)[-1]
            rename[c.module][leaf]=f"{c.module.removeprefix('Graph189')}_{leaf}"
    chunks = [f"import OMAReductions.{base[4:]}",CREDITS]
    report = []
    for mod, commands in modules.items():
        if not any(c in chosen for c in commands): continue
        body = []
        stack = 0
        enclosing = {}
        closes = {}
        scopes = []
        for j,command in enumerate(commands):
            if re.match(r"^(?:(?:noncomputable )?section|namespace)\b",command.text):
                scopes.append(j)
            enclosing[j] = scopes[-1] if scopes else None
            if re.match(r"^end\b",command.text) and scopes:
                closes[scopes.pop()] = j
        for j in scopes:
            closes[j] = len(commands)-1
        chosen_lines = [j for j,command in enumerate(commands) if command in chosen]
        for i,c in enumerate(commands):
            t = c.text
            outer = enclosing[i]
            if outer is not None and not any(outer <= j <= closes[outer] for j in chosen_lines):
                continue
            if c.name:
                if c not in chosen: continue
            elif t.startswith(("#","module","import ","public import ","public section")):
                continue
            elif ((re.match(r"^(?:open|include|omit|set_option)\b",t) and t.endswith(" in"))
                  or (t.startswith("@[") and t.endswith("]"))):
                after = next((n for n in commands[i+1:] if n.name),None)
                if after not in chosen: continue
            elif t == "attribute [instance] Core.finite Core.decAdj":
                if not any(k.name=="Graph189ExteriorCore.Core" and k in chosen for k in commands): continue
                t = """instance {V : Type u} {G : SimpleGraph V} {d : ℕ} (K : Core G d) : Fintype K.X := K.finite
instance {V : Type u} {G : SimpleGraph V} {d : ℕ} (K : Core G d) : DecidableRel K.graph.Adj := K.decAdj"""
            if re.match(r"^(?:(?:noncomputable )?section|namespace)\b",t): stack+=1
            if re.match(r"^end\b",t): stack-=1
            for before,after in rename.get(mod,{}).items():
                t=re.sub(r"(?<![\w'.])"+re.escape(before)+r"(?![\w'])",after,t)
            body.append(t)
        rendered="\n".join(body)+"\n"+"end\n"*max(0,stack)
        rendered="\n".join(line.rstrip() for line in rendered.splitlines() if line.strip())
        chunks.extend(["section",rendered,"end"])
        report.append(f"{mod}\t{sum(c in chosen for c in commands)}\t{len(rendered.encode())}")
    chunks.append(f"theorem OMA.solution : {target} := {args.root}")
    text="\n".join(chunks)+"\n"
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(text)
    args.output.with_suffix(".modules.tsv").write_text("\n".join(report)+"\n")
    print(f"{len(chosen)} source declarations, {len(report)} modules, {len(text.encode())} bytes")
if __name__=="__main__":
    main()
