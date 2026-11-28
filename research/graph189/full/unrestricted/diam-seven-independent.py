from itertools import product
h=7
rows=[]
# Each range contains all possible values of that variable from the certified
# initial constraints. Iterate the order and allowance first, then enumerate
# unoptimized independent products for the remaining six integers.
for c,l in product(range(11,16),range(2,7)):
    for a in range(9,29):
        s=a+l
        f=s-h
        for g in range(5):
            for j in range(20):
                i=a-h-1-j-g
                if i<1 or c<h+l+g+2: continue
                for m in range(1,7):
                    r=j+g+m+2
                    if i<m or c>=(m+1)*(h-m) or c*r>a*(h-m): continue
                    if c<h+l+g+2+i-m: continue
                    for P,Q in product(range(h-m+1),range(l+1)):
                        if not 1<=P+Q<=c or (P and Q==l): continue
                        if P and (i+g+1>l or c>(m+1)*(h-m)-m*P): continue
                        if Q and r>h: continue
                        uncovered=P*l<f
                        if uncovered and Q*h<a: continue
                        hidden_b=(i+Q)*(a-h) if uncovered else (a-h if Q else 0)
                        high_coverage=max(Q*r,a) if uncovered else Q*r
                        if max(a*m,hidden_b)+(c-P-Q)*r+P*a+high_coverage>a*h: continue
                        if not Q and not any(f*(t-l)<=t*l for t in range(max(h+1,a-2*l),h+j+2)): continue
                        rows.append((i,m,j,l,c,P,Q,g))
print(*sorted(rows),sep='\n')
print("Total",len(rows))
