#include <array>
#include <iostream>
#include <vector>
#include <algorithm>
#include <iomanip>
#include <sstream>
#include <cstdlib>
#include <cmath>

using namespace std;
using U=unsigned long long;
struct M {
  U lo,mid,hi;
  M(U v=0,U m=0,U h=0):lo(v),mid(m),hi(h){}
  explicit operator bool() const {return lo||mid||hi;}
  explicit operator U() const {return lo;}
  explicit operator int() const {return int(lo);}
  bool operator==(M b) const {return lo==b.lo&&mid==b.mid&&hi==b.hi;}
  bool operator!=(M b) const {return !(*this==b);}
  M operator|(M b) const {return {lo|b.lo,mid|b.mid,hi|b.hi};}
  M operator&(M b) const {return {lo&b.lo,mid&b.mid,hi&b.hi};}
  M operator^(M b) const {return {lo^b.lo,mid^b.mid,hi^b.hi};}
  M operator~() const {return {~lo,~mid,~hi};}
  M operator-(int) const {return {lo-1,mid-(lo==0),hi-(lo==0&&mid==0)};}
  M operator<<(int k) const {
    if(k>=128)return {0,0,lo<<(k-128)};
    if(k>=64)return M(0,lo,mid)<<(k-64);
    if(k==0)return *this;
    return {lo<<k,(mid<<k)|(lo>>(64-k)),(hi<<k)|(mid>>(64-k))};
  }
  M operator>>(int k) const {
    if(k>=128)return {hi>>(k-128),0,0};
    if(k>=64)return M(mid,hi,0)>>(k-64);
    if(k==0)return *this;
    return {(lo>>k)|(mid<<(64-k)),(mid>>k)|(hi<<(64-k)),hi>>k};
  }
  M& operator&=(M b){return *this=*this&b;}
  M& operator|=(M b){return *this=*this|b;}
  M& operator>>=(int k){return *this=*this>>k;}
};
int N;
M full;
struct AP {int a,d; M mask;};
vector<AP> aps;
M bans[160][160], unit[160];
vector<int> rs;
long long calls=0;
int bestdepth=0;
bool emit;
struct Tape {vector<unsigned short> ops; vector<int> gates;};
int lemmas = 0;
int bit(M value) {
  int offset=0;
  while (static_cast<unsigned long long>(value)==0){value >>= 64;offset+=64;}
  return offset+__builtin_ctzll(static_cast<unsigned long long>(value));
}
string maskHex(M a) {
  string out;
  do {out += "0123456789abcdef"[int(a & 15)]; a >>= 4;} while (a!=0);
  reverse(out.begin(),out.end());
  return out;
}
void output(Tape &t, M a) {
  cout << "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 150000000 in\nlemma v" << lemmas << " : Bad ([";
  for(int j=int(rs.size())-1; j>=0; --j) cout<<rs[j]<<(j ? "," : "");
  cout<<"],0x"<<maskHex(a)<<") := certify 0x1";
  for(auto it=t.ops.rbegin();it!=t.ops.rend();++it) cout<<hex<<setw(4)<<setfill('0')<<*it;
  cout<<dec<<" #[";
  for(size_t g=0;g<t.gates.size();++g) cout<<(g ? "," : "")<<"⟨_,v"<<t.gates[g]<<"⟩";
  cout<<"] (by decide +kernel)\n";
  lemmas++;
}
M place(M a, int p) {
  for (int q : rs) a &= ~bans[p][q];
  return a;
}
bool search(M a, M free, int depth, Tape &t) {
  if(++calls>=100000){cerr<<"cap reached\n";exit(3);}
  if(calls%1000000==0) cerr<<calls<<" nodes, depth "<<bestdepth<<", lemmas "<<lemmas<<"\n";
  bestdepth=max(bestdepth,depth);
  Tape fresh;
  Tape &w = t.ops.size() >= 450 ? fresh : t;
  M best = 0;
  int count = 14;
  M blue = full ^ a;
  // Probe all steps at once for impossible and forced windows.
  for(int d=1;d<=13;++d){
    M b2=blue&(blue>>d);
    M b4=b2&(b2>>(2*d));
    M b8=b4&(b4>>(4*d));
    M b12=(b8&(b4>>(8*d)))&(blue>>(12*d));
    if (b12!=0) {
      if(emit) w.ops.push_back(256+d*160+bit(b12));
      goto done;
    }
    M c=free&a;
    M u2=(c&(blue>>d))|(blue&(c>>d));
    M u4=(u2&(b2>>(2*d)))|(b2&(u2>>(2*d)));
    M u8=(u4&(b4>>(4*d)))|(b4&(u4>>(4*d)));
    M u12=(((u8&(b4>>(8*d)))|(b8&(u4>>(8*d))))&(blue>>(12*d)))|((b8&(b4>>(8*d)))&(c>>(12*d)));
    if (u12!=0) {
      int start=bit(u12);
      M rest=0;
      for(int i=0;i<13;++i)rest|=unit[start+i*d];
      rest&=a;
      int p=bit(rest);
      M next=place(a,p);
      if(emit) w.ops.push_back(256+d*160+start);
      rs.push_back(p);
      bool result=search(next,free&~unit[p],depth+1,w);
      rs.pop_back();
      if(result) return true;
      goto done;
    }
  }
  for(auto &ap: aps) {
    if ((ap.mask & a & ~free)!=0) continue;
    M rem=ap.mask & a;
    int k=0;
    for (M bits=rem;bits!=0;bits&=bits-1) if(++k>=count)break;
    if(k<count) {
      best=rem; count=k;
      if(k<=2)break;
    }
  }
  if (!best) {
    for(int q:rs)cerr<<q<<" ";
    cerr<<"witness\n";
    return true;
  }
  {
    int p=bit(best), score=-1;
    M pnext=0;
    for(M rem=best;rem!=0;rem&=rem-1){
      int q=bit(rem);
      M next=place(a,q);
      int sel=0;
      for(M bits=a^next;bits!=0;bits&=bits-1)++sel;
      sel=sel*8-abs(q-67);
      if(sel>score || !pnext){p=q;score=sel;pnext=next;}
    }
    if(emit) w.ops.push_back(p);
    rs.push_back(p);
    bool result=search(pnext,free&~unit[p],depth+1,w);
    rs.pop_back();
    if (result || search(a&~unit[p],free,depth+1,w)) return true;
  }
done:
  if(emit && &w==&fresh){
    int ref=lemmas;
    output(w,a);
    t.ops.push_back(3000+t.gates.size());
    t.gates.push_back(ref);
  }
  return false;
}
int main(int argc,char**argv) {
  N=atoi(argv[2]);
  int offset=atoi(argv[3]);
  full=(M(1)<<N)-1;
  for(int q=0;q<N;++q)unit[q]=M(1)<<q;
  for(int d=1;d<=13;++d)for(int a=0;a+12*d<N;++a){
    AP ap{a,d,0};
    for(int t=0;t<13;++t)ap.mask|=unit[a+t*d];
    aps.push_back(ap);
  }
  for(int p=0;p<N;++p)for(int q=0;q<N;++q)if(p!=q){
    for(int k : {2*p-q,2*q-p,(p+q)%2==0?(p+q)/2:-1})if(0<=k&&k<N)bans[p][q]|=unit[k];
  }
  emit = argc>4;
  M a=full, free=full;
  string seed=argv[1];
  for (int j=0;j<(int)seed.size();++j){
    int p=offset+j;
    if(seed[j]=='0') a&=~unit[p];
    if(seed[j]=='1'){
      if(!(a&unit[p])){cerr<<"seed forces triple\n";return 4;}
      a=place(a,p);
      rs.push_back(p);
    }
  }
  for(int q:rs) free&=~unit[q];
  Tape t;
  bool sat=search(a,free,0,t);
  if(emit && !sat)output(t,a);
  cerr<<"sat="<<sat<<", calls="<<calls<<", depth="<<bestdepth<<", lemmas="<<lemmas<<"\n";
}
