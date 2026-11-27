#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <vector>
using Wide = __int128_t;

static int mod(Wide x,int p) {
    int r=x%p;
    return r<0?r+p:r;
}

int main(int argc,char**argv) {
    const int limit=argc>1?std::atoi(argv[1]):50000;
    if(limit<23 || limit>1000000) return 2;
    std::vector<bool> prime(limit+1,true);
    prime[0]=prime[1]=false;
    for(int i=2;i<=limit/i;++i) if(prime[i])
        for(int j=i*i;j<=limit;j+=i) prime[j]=false;
    std::vector<int> primes;
    for(int i=2;i<=limit;++i) if(prime[i]) primes.push_back(i);
    unsigned long long ps=0,as=0,bmod=0,bsmall=0,bpair=0,qinteger=0,qsurv=0,cmom=0;
    for(int p:primes) {
        if(p<23 || p%4!=3 || (p%5!=2 && p%5!=3)) continue;
        ++ps;
        const Wide P=p,p3=P*P*P;
        std::vector<int> inv(p),root(p,-1);
        root[0]=0; inv[1]=1;
        for(int j=1;j<=p/2;++j) root[1LL*j*j%p]=j;
        for(int j=2;j<p;++j) inv[j]=p-1LL*(p/j)*inv[p%j]%p;
        for(int a:primes) {
            if(2*Wide(a)*a>=P*P) break;
            if(a<=11 || Wide(a)*a*a<=P*P) continue;
            ++as;
            const Wide A=Wide(a)*(a-1);
            const int d=mod((12-A)*(12-A)-48*A*(a-1),p), s=root[d];
            if(s<0) continue;
            const int denominator=inv[mod(2*A,p)];
            for(int r : {s,-s}) {
                const int b=mod(Wide(mod(A-12+r,p))*denominator,p);
                ++bmod;
                if(b>a && prime[b]) {
                    ++bsmall;
                    const Wide u=Wide(a)*b,t=a+b-1;
                    const Wide G=A*b*(b-1)+12*t;
                    if(G%p3==0) {
                        ++bpair;
                        const Wide num=u*(p-1)-G/p3, den=P*t-u;
                        if(den>0 && num%den==0) {
                            ++qinteger;
                            const Wide q=num/den;
                            if(q>=11 && q<a && 2*q<p && P*P<q*q*q && q%8==3 &&
                                q%5==2 && p%3!=q%3 && prime[static_cast<int>(q)] && u<P*q) {
                                ++qsurv;
                                const Wide N=p3*p*q+12;
                                if(N%u==0) {
                                    const Wide c=N/u;
                                    const Wide L=(P*P+p+1)*(q+1)+2*p3;
                                    const Wide M=p3*(p+q-1)+(a+b+c)-1;
                                    if(c>p3 && 2*(a+b+c)==L && u+(a+b)*c==M) {
                                        ++cmom;
                                        std::cout<<"Moment survivor p="<<p<<" q="<<static_cast<int>(q)
                                                 <<" a="<<a<<" b="<<b<<"\n";
                                    }
                                }
                            }
                        }
                    }
                }
                if(!s) break;
            }
        }
    }
    std::cout<<ps<<" p, "<<as<<" a, "<<bmod<<" quadratic candidates mod p, "<<bsmall
             <<" ordered prime b, "<<bpair<<" pairs mod p^3, "<<qinteger<<" integral q, "
             <<qsurv<<" admissible q, "<<cmom<<" moment survivors\n";
}
