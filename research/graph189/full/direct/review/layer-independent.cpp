// Checks large-order graphs with root degree a and all other vertices of degree >= k.
// Enumerates a multiset of (third-layer load, anchor mask) columns subject to
// additive anchor costs. Geometry of the remaining vertices is checked by
// interval branch-and-bound with independent lower and upper BFS.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <tuple>
#include <vector>
#include <unistd.h>
using namespace std;
using Bits=unsigned int;
constexpr int MAX=29;
using Rows=array<Bits,MAX>;
int k,a,n,b,shape,threshold;
vector<pair<int,int>> pairs;
int ach[6], w[6], masks[6], perms[120][32], au[120], nau;
int costcol[6][32][6];
long long profiles=0,cases=0, nodes=0, surviving=0;
set<vector<int>> distinct_profiles;
inline Bits bit(int i){return Bits(1)<<i;}
inline int countbits(Bits b){return __builtin_popcount(b);}
inline int lsb(Bits b){return __builtin_ctz(b);}
void set_edge(Rows&g,int u,int v){g[u]|=bit(v);g[v]|=bit(u);}
void del_edge(Rows&g,int u,int v){g[u]&=~bit(v);g[v]&=~bit(u);}
Bits expand(const Rows&g,Bits set){
 Bits answer=0;
 while(set){int p=lsb(set);set&=set-1;answer|=g[p];}
 return answer;
}
bool bad(const Rows&lo,const Rows&hi){
 Bits all=bit(n)-1;
 for(int v=0;v<n;++v){
   if(countbits(hi[v])<(v==0?a:k))return true;
   Bits lower2=expand(lo,lo[v])&~(hi[v]|bit(v));
   Bits sphere=bit(v),seen=sphere;
   for(int pass=1;pass<=3;++pass){sphere=expand(hi,sphere)&~seen;seen|=sphere;}
   Bits far=all^seen;
   if(countbits(lower2|far)>k)return true;
   if(far & ~expand(hi,sphere))return true;
 }
 return false;
}
void verify(Rows lo,Rows hi){
 if((++nodes&8191)==0 && (access("../PAUSE",F_OK)==0||access("../HALT",F_OK)==0))exit(100);
 do {
  if(bad(lo,hi))return;
  bool changed=false;
  for(int i=0;i<n;++i)if(countbits(hi[i])==(i==0?a:k)){
    Bits unfilled=hi[i]^lo[i];
    while(unfilled){int j=lsb(unfilled);unfilled&=unfilled-1;set_edge(lo,i,j);changed=true;}
  }
  if(changed)continue;
  vector<tuple<int,int,int>> undecided;
  for(int i=0;i<n;++i)for(int j=0;j<i;++j)if((hi[i]^lo[i])&bit(j)){
    int score=3*min(countbits(hi[i]),countbits(hi[j]))-countbits(lo[i]|lo[j]);
    undecided.emplace_back(score,i,j);
  }
  sort(undecided.begin(),undecided.end());
  if(undecided.empty()){++surviving;return;}
  Rows forced{}, forbidden{};
  for(auto [rank,i,j]:undecided){
    del_edge(hi,i,j);
    bool needed=bad(lo,hi);set_edge(hi,i,j);
    if(needed){set_edge(forced,i,j);changed=true;}
    set_edge(lo,i,j);bool impossible=bad(lo,hi);del_edge(lo,i,j);
    if(impossible){set_edge(forbidden,i,j);changed=true;}
    if(needed&&impossible)return;
  }
  if(changed){for(int i=0;i<n;++i){lo[i]|=forced[i];hi[i]&=~forbidden[i];}continue;}
  auto [rank,i,j]=undecided.front();
  Rows alternative=hi;del_edge(alternative,i,j);
  verify(lo,alternative);set_edge(lo,i,j);verify(lo,hi);return;
 }while(true);
}
void evaluate(int c){
 vector<int> orig;
 for(int j=0;j<b;++j)orig.push_back(w[j]*32+masks[j]);
 sort(orig.begin(),orig.end());
 for(int t=0;t<nau;++t){vector<int>x;for(int j=0;j<b;++j)x.push_back(w[j]*32+perms[au[t]][masks[j]]);sort(x.begin(),x.end());if(x<orig)return;}
 if(!distinct_profiles.insert(orig).second)return;
 ++profiles;
 for(int d=max(0,3*k+2-a-b-c);d+b<=k;++d){
  ++cases;
  n=1+a+b+c+d;
  Rows lo{},hi{};
  vector<int>L(n);for(int i=0;i<n;++i)L[i]=i==0?0:i<=a?1:i<=a+b?2:i<=a+b+c?3:4;
  for(int i=0;i<n;++i)for(int j=0;j<i;++j)if(L[i]-L[j]<=1)set_edge(hi,i,j);
  for(int j=1;j<=a;++j)set_edge(lo,0,j);
  for(auto [i,j]:pairs){if(ach[i]&bit(j))set_edge(lo,i+1,j+1);else del_edge(hi,i+1,j+1);}
  int next=a+b+1;
  for(int j=0;j<b;++j){
   for(int i=0;i<a;++i){if(masks[j]&bit(i))set_edge(lo,i+1,j+1+a);else del_edge(hi,i+1,j+1+a);}
   for(int t=0;t<w[j];++t)set_edge(lo,a+1+j,next++);
  }
  verify(lo,hi);
 }
}
void columns(int j,int maxw,int c,array<int,5>cost,array<int,5>hits){
 if(j==b){
  if(c<threshold)return;
  for(int i=0;i<a;++i)if(1+countbits(ach[i])+hits[i]<k)return;
  evaluate(c);return;
 }
 for(int v=maxw;v>=0;--v){
  if(c+(b-j)*v<threshold)break;
  w[j]=v;
  for(int m=j&&v==w[j-1]?masks[j-1]:1;m<1<<a;++m){
   auto cc=cost,hh=hits;bool ok=true;
   for(int i=0;i<a;++i){
    cc[i]+=costcol[v][m][i];hh[i]+=(m>>i)&1;
    if(cc[i]>k || 1+countbits(ach[i])+hh[i]+b-j-1<k){ok=false;break;}
   }
   if(ok){masks[j]=m;columns(j+1,v,c+v,cc,hh);}
  }
 }
}
int main(int argc,char**argv){
 k=atoi(argv[1]);a=atoi(argv[2]);threshold=2*k+2-a;
 for(int i=0;i<a;++i)for(int j=i+1;j<a;++j)pairs.emplace_back(i,j);
 vector<int> perm(a);iota(perm.begin(),perm.end(),0);int num=0;
 do{for(int m=0;m<1<<a;++m){int image=0;for(int i=0;i<a;++i)if(m&bit(i))image|=bit(perm[i]);perms[num][m]=image;}++num;}while(next_permutation(perm.begin(),perm.end()));
 for(int shape=0;shape<1<<pairs.size();++shape){
  if(access("../PAUSE",F_OK)==0||access("../HALT",F_OK)==0)return 100;
  fill(ach,ach+6,0);for(int p=0;p<(int)pairs.size();++p)if(shape&bit(p)){auto[i,j]=pairs[p];ach[i]|=bit(j);ach[j]|=bit(i);}
  bool canonical=true;nau=0;
  for(int t=0;t<num;++t){int image=0;for(int j=0;j<(int)pairs.size();++j){auto[u,v]=pairs[j];int pm=perms[t][bit(u)|bit(v)];int p=lsb(pm),q=lsb(pm&(pm-1));if(ach[p]&bit(q))image|=bit(j);}
   if(image<shape){canonical=false;break;}if(image==shape)au[nau++]=t;
  }
  if(!canonical)continue;
  distinct_profiles.clear();
  for(int v=0;v<=k;++v)for(int m=1;m<1<<a;++m)for(int i=0;i<a;++i)costcol[v][m][i]=(m&bit(i))?v:((m&ach[i])!=0);
  for(b=1;b<=k;++b){array<int,5>initial{},hits{};for(int i=0;i<a;++i)initial[i]=a-1-countbits(ach[i]);columns(0,k,0,initial,hits);}
 }
 cout<<"k "<<k<<" a "<<a<<" profiles "<<profiles<<" refined "<<cases<<" dfs "<<nodes<<" qualifying "<<surviving<<endl;
 return surviving!=0;
}
