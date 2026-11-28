#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdint>
#include <functional>
#include <vector>
using namespace std;
using Five = array<int,5>;
int k=7; long long masks_by_h[32]={}, types_by_h[32]={}, degree_by_h[32]={}, connected_by_h[32]={};
int W[32], caphist[17]={}, nc=0;
long long num[32]={};
vector<array<int,5>> topology[6];
int transformed[24][16];
void profile(Five A){
 int all=0;
 for (auto a:A) all|=a;
 if(all!=15)return;
 for(auto& perm:transformed){
  Five t;
  for(int i=0;i<5;i++)t[i]=perm[A[i]];
  sort(t.begin(),t.end());
  if(t<A)return;
 }
 nc++;
 int T[4]={};
 for(int i=0;i<5;i++)for(int p=0;p<4;p++)if(A[i]>>p&1)T[p]|=1<<i;
 for(auto const& G:topology[5]){
  bool good=true;
  int U[5],E[5];
  for(int i=0;i<5;i++){
   if(W[A[i]]+W[G[i]]<3){good=false;break;}
   U[i]=0;
   for(int j=0;j<5;j++)if(G[i]>>j&1)U[i]|=A[j];
  }
  if(!good)continue;
  int AA[4]={};
  for(int p=0;p<4;p++)for(int i=0;i<5;i++)if(T[p]>>i&1)AA[p]|=G[i];
  for(auto const& F:topology[4]){
   int BC[4],SC[4]={k-1,k-1,k-1,k-1},dc[4],Lower[4], AC[16];fill(AC,AC+16,100); AC[0]=0;
   bool ok=true;
   for(int i=0;i<5;i++){
    int ports=U[i];for(int p=0;p<4;p++)if(A[i]>>p&1)ports|=F[p];
    E[i]=min(k-1,k-4+W[G[i]]-W[ports&~A[i]]);
    if(E[i]<0){ok=false;break;}
    AC[A[i]]=min(AC[A[i]],E[i]);
    for(int p=0;p<4;p++)if(A[i]>>p&1)SC[p]=min(SC[p],E[i]);
   }
   if(!ok)continue;
   int capsum=0,bsum=0;
   for(int p=0;p<4;p++){
    Lower[p]=max(0,k-W[T[p]]-W[F[p]]);
    if(SC[p]<Lower[p]){ok=false;break;}
    int anchor=AA[p],port=0;
    for(int q=0;q<4;q++){
     if(F[p]>>q&1){anchor|=T[q];port|=F[q];}
     if(T[p]&T[q])port|=1<<q;
    }
    dc[p]=W[port&~F[p]&~(1<<p)];
    BC[p]=3-W[anchor&~T[p]]-dc[p];
    if(BC[p]<0){ok=false;break;}
    capsum+=SC[p];bsum+=BC[p];
    AC[1<<p]=min(AC[1<<p],SC[p]);
    AC[(1<<p)|F[p]]=min(AC[(1<<p)|F[p]],SC[p]+BC[p]);
   }
   if(!ok)continue;
   for(int s=15;s>=1;s--)for(int i=0;i<4;i++)if(s>>i&1)AC[s^(1<<i)]=min(AC[s^(1<<i)],AC[s]);
   for(int s=1;s<=15;s++)for(int j=(s-1)&s;j;j=(j-1)&s)AC[s]=min(AC[s],AC[j]+AC[s^j]);
   int bound=min(AC[15],(capsum+bsum)/2);
   if(bound>=2*k-3){
    int priv=0;
    for(int p=0;p<4;p++)if(SC[p]+BC[p]>=k)priv+=SC[p];
    bound=min(bound,(capsum+priv)/2);
   }
   num[bound]++;
   if(bound<2*k-3)continue;
   for(int h=2*k-3;h<=bound;h++){
    int M[32]={}, Z[32]={}, used[16]={};
    function<void(int,int)> mrec=[&](int pos,int start){
     if(pos<h){
      for(int m=start;m<16;m++){
       bool ok=true;for(int s=1;s<16;s++)if((s&m)&&used[s]>=AC[s])ok=false;
       if(!ok)continue;
       M[pos]=m;for(int s=1;s<16;s++)if(s&m)used[s]++;
       mrec(pos+1,m);
       for(int s=1;s<16;s++)if(s&m)used[s]--;
      }
      return;
     }
     for(int p=0;p<4;p++)if(used[1<<p]<Lower[p])return;
     int slots[4], mandatory[32]={}, loc[4]={};
     for(int p=0;p<4;p++){
      int common=0;for(int i=0;i<h;i++)if(M[i]>>p&1)common|=M[i];
      for(int q=0;q<4;q++){if(F[p]>>q&1)common|=F[q];if(T[p]&T[q])common|=1<<q;}
      slots[p]=BC[p]+dc[p]-W[common&~F[p]&~(1<<p)];
      for(int i=0;i<h;i++)if(!(M[i]>>p&1)&&(M[i]&F[p])){mandatory[i]|=1<<p;loc[p]++;}
      if(loc[p]>slots[p])return;
     }
     int privatecount=0,slotsum=0;
     for(int i=0;i<h;i++)if(W[M[i]]==1)privatecount++;
     for(int p=0;p<4;p++)slotsum+=slots[p];
     if(privatecount>slotsum)return;
     masks_by_h[h]++;
     function<void(int)> zrec=[&](int idx){
      if(idx<h){
       for(int z=(idx&&M[idx]==M[idx-1]?Z[idx-1]:0);z<16;z++){
        if((M[idx]&z)||(mandatory[idx]&~z)||(W[M[idx]]==1&&!z))continue;
        bool ok=true;for(int p=0;p<4;p++)if((z>>p&1)&&slots[p]<=0)ok=false;
        if(!ok)continue;
        Z[idx]=z;for(int p=0;p<4;p++)slots[p]-=z>>p&1;
        zrec(idx+1);
        for(int p=0;p<4;p++)slots[p]+=z>>p&1;
       }
       return;
      }
      types_by_h[h]++;
      int graph[32]={};
      for(int i=0;i<h;i++)for(int j=0;j<i;j++)
       if(!(M[i]&~(M[j]|Z[j]))&&!(M[j]&~(M[i]|Z[i]))){graph[i]|=1<<j;graph[j]|=1<<i;}
      for(int i=0;i<h;i++)if(__builtin_popcount((unsigned)graph[i])+W[M[i]]<k)return;
      degree_by_h[h]++;
      int seen=1;
      for(int step=0;step<h+4;step++){
       for(int p=0;p<4;p++)if(seen>>p&1)seen|=F[p];
       for(int i=0;i<h;i++){
        if(M[i]&seen)seen|=1<<(4+i);
        if(seen>>(4+i)&1){seen|=M[i];seen|=graph[i]<<4;}
       }
      }
      if(seen!=(1<<(h+4))-1)return;
      connected_by_h[h]++;
      if(connected_by_h[h]>2)return;
      printf("A");for(int i=0;i<5;i++)printf(" %x",A[i]);
      printf(" AG");for(int i=0;i<5;i++)printf(" %x",G[i]);
      printf(" PG");for(int i=0;i<4;i++)printf(" %x",F[i]);
      printf(" core");for(int i=0;i<h;i++)printf(" %x/%x/%x",M[i],Z[i],graph[i]);puts("");
     };
     zrec(0);
    };
    mrec(0,1);
   }
  }
 }
}
int main(int argc,char** argv){if(argc>1)k=atoi(argv[1]);
 for(int i=0;i<32;i++)W[i]=__builtin_popcount(i);
 for(int n:{4,5})for(int mask=0;mask<(1<<(n*(n-1)/2));mask++){
  array<int,5> P={};
  int b=0;
  for(int p=0;p<n;p++)for(int q=p+1;q<n;q++,b++)if(mask>>b&1){P[p]|=1<<q;P[q]|=1<<p;}
  topology[n].push_back(P);
 }
 array<int,4> perm={0,1,2,3};int it=0;
 do{for(int t=0;t<16;t++)for(int p=0;p<4;p++)if(t>>p&1)transformed[it][t]|=1<<perm[p];it++;}while(next_permutation(perm.begin(),perm.end()));
 for(int a=0;a<15;a++)for(int b=a;b<15;b++)for(int c=b;c<15;c++)for(int d=c;d<15;d++)for(int e=d;e<15;e++)profile({a,b,c,d,e});
 for(int h=2*k-3;h<=2*k+4;h++)printf("h=%d mask=%lld boundary=%lld min_degree=%lld connected=%lld\n",h,masks_by_h[h],types_by_h[h],degree_by_h[h],connected_by_h[h]);
 printf("Incidence representatives %d\n",nc);for(int i=0;i<=2*k+4;i++)printf("%d %lld\n",i,num[i]);
}
