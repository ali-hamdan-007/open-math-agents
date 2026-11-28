#include <algorithm>
#include <array>
#include <cassert>
#include <cstdio>
#include <functional>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
using Graph = array<int,32>;
using Profile = array<int,5>;
int wt(int x) { return __builtin_popcount(unsigned(x)); }
int ball2(const Graph& g,int i) {
 int nbr=g[i], united=0;
 for(int n=nbr;n;n&=n-1) united |= g[__builtin_ctz(unsigned(n))];
 return united & ~(nbr|(1<<i));
}
void edge(Graph& g,int a,int b) {g[a]|=1<<b; g[b]|=1<<a;}
void topology(Graph& g,int first,int count,int topologybits){
 for(int i=0;i<count;i++)for(int j=0;j<i;j++){
  if(topologybits&1)edge(g,first+i,first+j);
  topologybits>>=1;
 }
}
long long boundaries[14]={},degrees[14]={},masks[14]={},conn[14]={},maxbound=0;
void core(const Graph& shell, const array<int,16>& cap, int h){
 // Enumerate independent multiplicities for every NONEMPTY port subset.
 vector<int> rows;
 array<int,16> use{};
 function<void(int,int)> search=[&](int mask,int left){
  if(!left){
   Graph g=shell;
   for(int i=0;i<h;i++)for(int p=0;p<4;p++)if(rows[i]>>p&1)edge(g,12+i,8+p);
   for(int i=0;i<12;i++)if(wt(ball2(g,i))>6 || (i>=8&&wt(g[i])<6))return;
   array<int,4> spare{};
   for(int p=0;p<4;p++)spare[p]=6-wt(ball2(g,8+p));
   vector<int> mand(h);
   for(int i=0;i<h;i++)for(int p=0;p<4;p++)if(ball2(g,8+p)&(1<<(12+i)))mand[i]|=1<<p;
   int obligated=0;
   for(int i=0;i<h;i++)if(wt(rows[i])==1&&!mand[i])++obligated;
   if(obligated>accumulate(spare.begin(),spare.end(),0))return;
   masks[h]++;
   vector<int> z(h);
   function<void(int)> paint=[&](int i){
    if(i<h){
     int optional=15 & ~(rows[i]|mand[i]);
     for(int extra=optional;;extra=(extra-1)&optional){
      int b=extra|mand[i];
      bool ok=wt(rows[i])>1||b;
      if(i&&rows[i]==rows[i-1]&&b<z[i-1])ok=false;
      for(int p=0;p<4;p++)if((extra>>p&1)&&!spare[p])ok=false;
      if(ok){
       z[i]=b;
       for(int p=0;p<4;p++)spare[p]-=extra>>p&1;
       paint(i+1);
       for(int p=0;p<4;p++)spare[p]+=extra>>p&1;
      }
      if(!extra)break;
     }
     return;
    }
    boundaries[h]++;
    Graph allowed=g;
    for(int i=0;i<h;i++)for(int j=0;j<i;j++){
     bool ok=true;
     for(int p=0;p<4;p++){
      if((rows[i]>>p&1)&&!((rows[j]|z[j])>>p&1))ok=false;
      if((rows[j]>>p&1)&&!((rows[i]|z[i])>>p&1))ok=false;
     }
     if(ok)edge(allowed,12+i,12+j);
    }
    for(int i=0;i<h;i++)if(wt(allowed[12+i])<6)return;
    degrees[h]++;
    int live=1<<8,old=0;
    while(live!=old){
      old=live;
      for(int q=8;q<h+12;q++)if(old&(1<<q))live|=allowed[q]&~255;
    }
    if(wt(live)==h+4)conn[h]++;
    return;
   };
   paint(0);
   return;
  }
  if(mask>15)return;
  int limit=left;
  for(int s=1;s<16;s++)if(mask&s)limit=min(limit,cap[s]-use[s]);
  for(int k=0;k<=limit;k++){
   search(mask+1,left-k);
   if(k<limit){
    rows.push_back(mask);
    for(int s=1;s<16;s++)if(mask&s)use[s]++;
   }
  }
  rows.resize(rows.size()-limit);
  for(int s=1;s<16;s++)if(mask&s)use[s]-=limit;
 };
 search(1,h);
}
int main(){
 // Skeleton ordering: z=0; anchors 1..5; complete K=6,7; ports 8..11.
 // The labels of anchors are eliminated by a sorted incidence list. Drop a
 // port-renaming orbit by inserting all its sorted images into seen.
 set<Profile> seen;
 int profiles=0;
 for(int a=0;a<15;a++)for(int b=a;b<15;b++)for(int c=b;c<15;c++)for(int d=c;d<15;d++)for(int e=d;e<15;e++){
  Profile v{a,b,c,d,e};
  if((a|b|c|d|e)!=15||seen.count(v))continue;
  ++profiles;
  array<int,4> perm{0,1,2,3};
  do{
   Profile z{};
   for(int i=0;i<5;i++)for(int p=0;p<4;p++)if(v[i]>>p&1)z[i]|=1<<perm[p];
   sort(z.begin(),z.end());seen.insert(z);
  }while(next_permutation(perm.begin(),perm.end()));
  Graph base{};edge(base,6,7);
  for(int i=0;i<5;i++){
   edge(base,0,i+1);edge(base,6,i+1);edge(base,7,i+1);
   for(int p=0;p<4;p++)if(v[i]>>p&1)edge(base,i+1,8+p);
  }
  for(int gt=0;gt<1024;gt++){
   Graph ar=base;topology(ar,1,5,gt);
   bool low=false;for(int i=1;i<=5;i++)if(wt(ar[i])<6)low=true;
   if(low)continue;
   for(int pt=0;pt<64;pt++){
    Graph g=ar;topology(g,8,4,pt);
    array<int,16> cap;cap.fill(20);cap[0]=0;
    array<int,4> single{5,5,5,5}, free{};
    bool ok=true;
    for(int i=0;i<5;i++){
     int available=min(5,6-wt(ball2(g,1+i)));
     if(available<0){ok=false;break;}
     cap[v[i]]=min(cap[v[i]],available);
     for(int p=0;p<4;p++)if(v[i]>>p&1)single[p]=min(single[p],available);
    }
    if(!ok)continue;
    int maxi=0, singles=0, sumcap=0;
    for(int p=0;p<4;p++){
     free[p]=6-wt(ball2(g,8+p));
     if(free[p]<0||wt(g[8+p])+single[p]<6){ok=false;break;}
     cap[1<<p]=min(cap[1<<p],single[p]);
     int ord=((g[8+p]>>8)&15)|(1<<p);
     cap[ord]=min(cap[ord],single[p]+free[p]);
     sumcap+=single[p];maxi+=free[p];
     if(single[p]+free[p]>=6)singles+=single[p];
    }
    if(!ok)continue;
    int limit=(sumcap+min(maxi,singles))/2;
    // Relax union size by every single set covering the requested subset,
    // then every split into two proper parts, by increasing subset cardinality.
    for(int s=1;s<16;s++)for(int t=1;t<16;t++)if((s&t)==s)cap[s]=min(cap[s],cap[t]);
    for(int sz=2;sz<=4;sz++)for(int s=1;s<16;s++)if(wt(s)==sz)
      for(int t=1;t<s;t++)if((t&s)==t)cap[s]=min(cap[s],cap[t]+cap[s^t]);
    limit=min(limit,cap[15]);maxbound=max(maxbound,(long long)limit);
    assert(limit<=13);
    for(int h=9;h<=limit;h++)core(g,cap,h);
   }
  }
 }
 printf("profiles %d max bound %lld\n",profiles,maxbound);
 for(int h=9;h<=13;h++)printf("h=%d mask=%lld boundary=%lld degree=%lld connected=%lld\n",h,masks[h],boundaries[h],degrees[h],conn[h]);
}
