#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

// Recompute the per-direction mass upper bound by enumerating the
// allowable opposite swaps directly. No concavity or binary search is used.
using number = std::int64_t;
using Table = std::vector<number>;
constexpr number scale = 1000000000000LL;

number certificate(int p, number penalty) {
    const int choices = p - 2;
    const int reserved = p - 2 + 6;
    const int limit = 17 * p * p * p;
    std::vector<bool> composite(limit + 1, false);
    for (int i = 2; i <= limit / i; ++i)
        if (!composite[i])
            for (int j = i * i; j <= limit; j += i) composite[j] = true;
    assert(!composite[p]);
    std::vector<int> order(p);
    std::vector<Table> prefix(p, Table(1,0));
    for (int r=1; r<p; ++r) {
        int value = 1;
        for (int j=1;j<p;++j) {
            value = value*r%p*r%p;
            if (j%2==0 && value==1) { order[r]=j; break; }
        }
        assert(order[r]>0);
    }
    for (int q=3;q<=limit;q+=2) {
        if (composite[q] || q==p) continue;
        int r=q%p;
        if ((int)prefix[r].size() <= order[r]*(choices+1)-1+reserved)
            prefix[r].push_back(prefix[r].back() + (scale+q-1)/q);
    }
    std::vector<Table> F(p);
    for (int r=1;r<p;r++) {
        int hi=order[r]*(choices+1)-1;
        assert((int)prefix[r].size()==hi+reserved+1);
        for (int j=0;j<=hi;++j) {
            number value=prefix[r][j];
            for(int h=1;h<=reserved;++h)
                value=std::max(value,prefix[r][j+h]-penalty*h);
            F[r].push_back(value);
        }
    }
    number total=penalty*(choices+reserved);
    std::vector<bool> seen(p);
    for (int r=1;r<=p/2;++r) {
        if(seen[r]) continue;
        int v=1;
        while ((v*r)%p!=1) ++v;
        v=std::min(v,p-v);
        seen[r]=seen[v]=true;
        number best=0;
        int d=order[r];
        if(r==v) {
            for(int a=0;a<=choices;a++) for(int b=0;b<=choices-a;b++) {
                int heavy=a+d*(b+1)-1;
                number sum=std::max(F[r][a]+F[p-r][heavy], F[p-r][a]+F[r][heavy]);
                best=std::max(best,sum-penalty*(a+b));
            }
        } else {
            auto side=[&](int dir,int excess,int cap) {
                number score=0;
                for(int s=0;s<=cap;s++) {
                    number value=std::max(F[dir][s]+F[p-dir][s+excess],
                        F[p-dir][s]+F[dir][s+excess]);
                    score=std::max(score,value-penalty*s);
                }
                return score;
            };
            for (int a=0;a<=choices;a++) for (int b=0;b+a<=choices;b++) {
                int cap=choices-a-b, high=a+d*(b+1)-1;
                number sum=std::max(side(r,high,cap)+side(v,a,cap),
                    side(v,high,cap)+side(r,a,cap));
                best=std::max(best,sum-penalty*(a+b));
            }
        }
        total+=best;
    }
    return total;
}
int main() {
    for(int p: {67,139,157}) {
        number L=p<=139?500000000:450000000;
        number n=certificate(p,L);
        std::cout << p << " " << L << " " << n << std::endl;
        assert(n<2*scale);
    }
}
