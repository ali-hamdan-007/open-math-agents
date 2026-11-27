from ctypes import CDLL,c_char_p,c_void_p
import sys
from itertools import combinations
z=CDLL('libz3.so.4')
for f,args,res in [('Z3_mk_config',[],c_void_p),('Z3_mk_context',[c_void_p],c_void_p),('Z3_del_config',[c_void_p],None),('Z3_del_context',[c_void_p],None),('Z3_eval_smtlib2_string',[c_void_p,c_char_p],c_char_p)]:
 t=getattr(z,f);t.argtypes=args;t.restype=res
def search(k,n,anchor,masks,sec=3):
 v=range(n); pairs=list(combinations(v,2))
 def e(i,j):return 'false' if i==j else f'e{min(i,j)}_{max(i,j)}'
 def d(i,j):return 'false' if i==j else f'd{min(i,j)}_{max(i,j)}'
 def dis(l):return '(or '+' '.join(l)+')'
 def card(op,k,l):return f'((_ {op} {k}) '+' '.join(l)+')'
 s=[f'(set-option :timeout {sec*1000})']
 def put(p):s.append(f'(assert {p})')
 for i,j in pairs:
  for f in (e,d):s.append(f'(declare-const {f(i,j)} Bool)')
 for i,j in pairs:
  put(f'(= {d(i,j)} (and (not {e(i,j)}) '+dis(f'(and {e(i,h)} {e(h,j)})' for h in v if h not in (i,j))+'))')
 def fix(i,j,b):put(e(i,j) if b else f'(not {e(i,j)})')
 for j in range(1,n):fix(0,j,j<4)
 for l,(i,j) in enumerate(combinations(range(1,4),2)):fix(i,j,anchor&(1<<l))
 W=range(4,4+len(masks));R=range(W.stop,n)
 for i in range(1,4):
  for j,m in zip(W,masks):fix(i,j,m&(1<<(i-1)))
  for j in R:fix(i,j,False)
 for j in R:put(dis(e(w,j) for w in W))
 for j in v:
  put(card('at-most',k,[d(i,j) for i in v if i!=j]))
  if j:put(card('at-least',k,[e(i,j) for i in v if i!=j]))
 # Standard row-major lexicographic minimum under pair transpositions.
 for i,j in pairs:
  if not ((i in R and j in R) or (i in W and j in W and masks[i-4]==masks[j-4])): continue
  lex='true'
  for h in reversed([h for h in v if h not in (i,j)]):
   x,y=e(i,h),e(j,h)
   lex=f'(ite (= {x} {y}) {lex} (not {x}))'
  put(lex)
 conf=z.Z3_mk_config();ctx=z.Z3_mk_context(conf);z.Z3_del_config(conf)
 out=z.Z3_eval_smtlib2_string(ctx,('\n'.join(s)+'\n(check-sat)').encode()).decode().strip()
 if out=='sat':
  vals=z.Z3_eval_smtlib2_string(ctx,('(get-value ('+' '.join(e(i,j) for i,j in pairs)+'))').encode()).decode()
  import re
  print('SAT',k,n,anchor,masks,[(i,j) for i,j in pairs if re.search(r'\('+e(i,j)+' true\\)',vals)],flush=True)
 z.Z3_del_context(ctx);return out

if __name__ == "__main__":
 k=int(sys.argv[1])
 for n in range(3*k+1,4*k-2):
  print(k,n,search(k,n,3,[1,2,4,6]+[7]*(k-4),int(sys.argv[2])),flush=True)
