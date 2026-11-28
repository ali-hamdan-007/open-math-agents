#include <algorithm>
#include <array>
#include <cstdio>
#include <functional>
#include <vector>
using namespace std;
using Five=array<int,5>;
int pop(int n){return __builtin_popcount((unsigned)n);}
int reached[3], amiss[5], Aport[3], Slo[3], Sbound[3], Ubound[8], Uused[8], UcapA[5], bport[3];
int M[16], Z[16], FZ[3], h;
long long c[7][16]={};
Five A,G,P;
vector<Five> graphs(int n){
 vector<Five> ans;
 for(int k=0;k<1<<(n*(n-1)/2);k++){
  Five m{};int e=0;
  for(int i=0;i<n;i++)for(int j=0;j<i;j++,e++)if(k>>e&1){m[i]|=1<<j;m[j]|=1<<i;}
  ans.push_back(m);
 }
 return ans;
}
void remote(){
 ++c[2][h];
 int slots[3], mandatory[16]={}, privreq[16]={};
 for(int a=0;a<5;a++){
  int far=0;for(int f=0;f<3;f++)if(!(A[a]&FZ[f]))far++;
  if(Uused[A[a]]+far>UcapA[a])return;
 }
 for(int p=0;p<3;p++){
  int shared=0, fs=0, demand=0;
  for(int i=0;i<h;i++)if(M[i]>>p&1)shared|=M[i];
  for(int f=0;f<3;f++)fs+=FZ[f]>>p&1;
  slots[p]=bport[p]-fs-pop(shared&~(reached[p]|P[p]|(1<<p)));
  for(int i=0;i<h;i++){
   if(!(M[i]>>p&1)&&(M[i]&P[p])){mandatory[i]|=1<<p;demand++;}
   if(M[i]==(1<<p)&&Uused[1<<p]+fs<6)privreq[i]=1;
  }
  if(slots[p]<demand)return;
 }
 ++c[3][h];
 function<void(int)> zrec=[&](int pos){
  if(pos<h){
   int lo=pos&&M[pos-1]==M[pos]?Z[pos-1]:0;
   for(int z=lo;z<8;z++){
    if((M[pos]&z)||(mandatory[pos]&~z)||(!z&&privreq[pos]))continue;
    bool ok=true;for(int p=0;p<3;p++)if((z>>p&1)&&slots[p]<=0)ok=false;
    if(!ok)continue;
    Z[pos]=z;for(int p=0;p<3;p++)slots[p]-=z>>p&1;
    zrec(pos+1);
    for(int p=0;p<3;p++)slots[p]+=z>>p&1;
   }
   return;
  }
  ++c[4][h];
  int ged[16]={}, fedge[3]={};
  for(int i=0;i<h;i++){
   int deg=pop(M[i]);
   for(int f=0;f<3;f++)if(!(M[i]&~FZ[f])){fedge[f]|=1<<i;deg++;}
   for(int j=0;j<h;j++)if(i!=j&&!(M[i]&~(M[j]|Z[j]))&&!(M[j]&~(M[i]|Z[i]))){ged[i]|=1<<j;deg++;}
   if(deg<6)return;
  }
  for(int f=0;f<3;f++)if(pop(fedge[f])+2<6)return;
  ++c[5][h];
  for(int f=0;f<3;f++){
   int realized=0;for(int i=0;i<h;i++)if(fedge[f]>>i&1)realized|=M[i];
   if(realized!=FZ[f])return;
  }
  ++c[6][h];
 };
 zrec(0);
}
void route(int pos,int lo){
 if(pos<h){
  for(int m=lo;m<8;m++){
   bool ok=true;for(int s=1;s<8;s++)if((s&m)&&Uused[s]>=Ubound[s])ok=false;
   if(!ok)continue;
   M[pos]=m;for(int s=1;s<8;s++)if(s&m)Uused[s]++;
   route(pos+1,m);
   for(int s=1;s<8;s++)if(s&m)Uused[s]--;
  }
  return;
 }
 for(int p=0;p<3;p++)if(Uused[1<<p]<Slo[p])return;
 ++c[1][h];
 vector<int> possible;
 for(int z=1;z<8;z++){
  int core=0;for(int i=0;i<h;i++)if(!(M[i]&~z))core++;
  if(core>=4)possible.push_back(z);
 }
 for(int f:possible)for(int g:possible)if(g>=f)for(int j:possible)if(j>=g){
  FZ[0]=f;FZ[1]=g;FZ[2]=j;remote();
 }
}
int main(){
 auto GA=graphs(5), GP=graphs(3);
 for(int a=1;a<7;a++)for(int b=a;b<7;b++)for(int d=b;d<7;d++)for(int e=d;e<7;e++)for(int f=e;f<7;f++){
  A={a,b,d,e,f};if((a|b|d|e|f)!=7)continue;
  bool canon=true;array<int,3> per={0,1,2};
  do{Five M{};for(int i=0;i<5;i++)for(int p=0;p<3;p++)if(A[i]>>p&1)M[i]|=1<<per[p];sort(M.begin(),M.end());if(M<A)canon=false;}while(next_permutation(per.begin(),per.end()));
  if(!canon)continue;
  fill(Aport,Aport+3,0);
  for(int p=0;p<3;p++)for(int i=0;i<5;i++)if(A[i]>>p&1)Aport[p]|=1<<i;
  for(auto& ag:GA){G=ag;
   bool good=true;for(int i=0;i<5;i++)if(pop(A[i])+pop(G[i])<5)good=false;
   if(!good)continue;
   for(auto& pg:GP){P=pg;
    fill(Ubound,Ubound+8,40);Ubound[0]=0;
    for(int i=0;i<5;i++){
     int near=0;for(int j=0;j<5;j++)if(G[i]>>j&1)near|=A[j];for(int p=0;p<3;p++)if(A[i]>>p&1)near|=P[p];
     UcapA[i]=6-(4-pop(G[i]))-pop(near&~A[i]);
     Ubound[A[i]]=min(Ubound[A[i]],min(5,UcapA[i]));
    }
    bool accepted=true;
    for(int p=0;p<3;p++){
     int a2=0,p2=0;
     for(int i=0;i<5;i++)if(Aport[p]>>i&1){a2|=G[i];p2|=A[i];}
     for(int q=0;q<3;q++)if(P[p]>>q&1){a2|=Aport[q];p2|=P[q];}
     reached[p]=p2&~(P[p]|(1<<p));
     bport[p]=5-pop(a2&~Aport[p])-pop(reached[p]);
     Slo[p]=max(0,6-pop(Aport[p])-pop(P[p]));
     int upper=5;for(int i=0;i<5;i++)if(A[i]>>p&1)upper=min(upper,Ubound[A[i]]);
     Ubound[1<<p]=min(Ubound[1<<p],upper);
     Ubound[(1<<p)|P[p]]=min(Ubound[(1<<p)|P[p]],upper+bport[p]);
     if(bport[p]<0||Slo[p]>upper)accepted=false;
    }
    if(!accepted)continue;
    for(int s=7;s>0;s--)for(int p=0;p<3;p++)if(s>>p&1)Ubound[s^(1<<p)]=min(Ubound[s^(1<<p)],Ubound[s]);
    for(int s=1;s<8;s++)for(int v=(s-1)&s;v;v=(v-1)&s)Ubound[s]=min(Ubound[s],Ubound[v]+Ubound[s^v]);
    for(h=9;h<=Ubound[7];h++){c[0][h]++;route(0,1);}
   }
  }
 }
 for(h=9;h<=15;h++){printf("%d",h);for(int j=0;j<7;j++)printf(" %lld",c[j][h]);puts("");}
}
