// Extended integer checker for the quadratic-order degree windows.
// The moderate certificate catalogue retains its historical standalone enumerator.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
using Row = uint32_t;
using Graph = vector<Row>;
int countBits(Row a) {return __builtin_popcount(a);}
Row bit(int x) {return Row(1)<<x;}
void connect(Graph &g,int x,int y) {g[x]|=bit(y);g[y]|=bit(x);}
vector<int> verts(Row r) {vector<int> a;while(r){a.push_back(__builtin_ctz(r));r&=r-1;}return a;}
uint64_t canon(const Graph &g) {
  const int n=g.size(); map<vector<int>,vector<int>> groups;
  for(int v=0;v<n;v++){
    vector<int> key{countBits(g[v])};
    vector<int> around;
    for(int w:verts(g[v])) around.push_back(10*countBits(g[w])+countBits(g[w]&g[v]));
    sort(around.begin(),around.end());
    key.insert(key.end(),around.begin(),around.end());groups[key].push_back(v);
  }
  vector<vector<int>> choices;vector<bool> twin;
  for(auto &[key,group]:groups){
    bool twins=true;
    for(int a:group)for(int b:group) if((g[a]^g[b])&~(bit(a)|bit(b)))twins=false;
    choices.push_back(group);twin.push_back(twins);
  }
  uint64_t best=UINT64_MAX; vector<int> order;
  function<void(int)> permute=[&](int i){
    if(i==(int)choices.size()){
      uint64_t e=0;int pos=0;
      for(int a=0;a<n;a++)for(int b=0;b<a;b++,pos++)if(g[order[a]]&bit(order[b]))e|=(uint64_t(1)<<pos);
      best=min(best,e);return;
    }
    auto c=choices[i];
    do{for(auto v:c)order.push_back(v);permute(i+1);order.resize(order.size()-c.size());}
    while(!twin[i] && next_permutation(c.begin(),c.end()));
  };
  permute(0);return best;
}
bool spanningLength(const Graph &g,Row allowed,int need){
  set<pair<int,Row>> dead;
  function<bool(int,Row,int)> go=[&](int v,Row used,int length){
    if(length>=need)return true;
    if(dead.count({v,used}))return false;
    Row add=g[v]&allowed&~used;
    while(add){int w=__builtin_ctz(add);add&=add-1;if(go(w,used|bit(w),length+1))return true;}
    dead.insert({v,used});return false;
  };
  for(int v:verts(allowed))if(go(v,bit(v),1))return true;
  return false;
}
bool connected(const Graph &g,Row allowed) {
  Row reached=allowed&-allowed, last=0;
  while(reached!=last){Row add=0;last=reached;for(int v:verts(reached))add|=g[v];reached|=allowed&add;}
  return reached==allowed;
}
struct Totals{unsigned long long patterns=0,raw=0,extensions=0,survive=0;};
// After deleting the path vertex t and z, certify three actual components.
// The two outer components have Hamilton cycles by the Dirac inequality;
// the middle has distinct t/z contacts since deleting their sole common
// contact would disconnect G. Joining the three paths uses at least two
// middle vertices and both separator vertices.
bool routedThree(const Graph &lower,const Graph &upper,int k){
  const int n=upper.size(),z=n-1,h=(k+1)/2;
  const int delta=max(2,n-1-k-(k+1)*(k+1)/4);
  for(int t=0;t<z;t++){
    Row left=(bit(n)-1)^bit(t)^bit(z);
    vector<Row> parts;
    while(left){
      Row seen=left&-left,old=0;
      while(seen!=old){
        old=seen;for(int x:verts(old))seen|=upper[x]&left;
      }
      if(!connected(lower,seen))break;
      parts.push_back(seen);
      left&=~seen;
    }
    if(left||parts.size()!=3)continue;
    for(int middle=0;middle<3;middle++){
      int a=countBits(parts[(middle+1)%3]),b=countBits(parts[(middle+2)%3]);
      if(countBits(parts[middle])>=2 && min(a,b)>=3 && max(a,b)<=2*(delta-2)
          && a+b+4>=n-h-1)return true;
    }
  }
  return false;
}
void complete(Graph fixed,int p,int k,Totals &tot,bool saturatedShell=false){
  int n=fixed.size(),h=(k+1)/2;Row all=bit(n)-1,root=bit(n-1);
  auto tooLong=[&](const Graph &g){return spanningLength(g,all,n-h-1)||spanningLength(g,all^root,p+1);};
  if(spanningLength(fixed,all,n-h-1)){++tot.raw;return;}
  vector<pair<int,int>> free;
  for(int u=0;u<n;u++)for(int v=u+1;v<n;v++)
    if(!(fixed[u]&bit(v)) && (v<p||v==n-1))free.push_back({u,v});
  for(;;){
    if(tooLong(fixed)){++tot.extensions;return;}
    Graph possible=fixed;vector<pair<int,int>> keep;
    for(auto [u,v]:free)if(!(fixed[u]&bit(v))){
      Graph trial=fixed;connect(trial,u,v);
      if(!tooLong(trial)){connect(possible,u,v);keep.push_back({u,v});}
    }
    vector<bool> saturated(n);
    for(int v=0;v<n;v++){
      int floor=v==n-1?max(2,n-1-k-(k+1)*(k+1)/4):k;
      if(countBits(possible[v])<floor || !connected(possible,all^bit(v))){++tot.extensions;return;}
      saturated[v]=countBits(possible[v])==floor;
      Row two=0;for(int w:verts(fixed[v]))two|=fixed[w];
      if(countBits(two&~possible[v]&~bit(v))>k){++tot.extensions;return;}
    }
    if(count_if(fixed.begin(),fixed.end(),[&](Row row){return countBits(row)<=k;})<2){
      ++tot.extensions;return;
    }
    bool added=false;
    // Every actual graph survives every single vertex deletion. An edge
    // whose deletion destroys this property in the upper graph is mandatory.
    for(auto [i,j]:keep){
      Graph trial=possible;
      trial[i]^=bit(j);trial[j]^=bit(i);
      bool necessary=false;
      for(int d=0;d<n&&!necessary;d++)necessary=!connected(trial,all^bit(d));
      if(necessary){connect(fixed,i,j);added=true;}
    }
    // With k provable distance-two witnesses, the component of v after
    // deleting them from the mandatory graph lies in its closed neighborhood.
    if(saturatedShell){
      for(int v=0;v<n;v++){
        Row two=0;for(int w:verts(fixed[v]))two|=fixed[w];
        Row shell=two&~possible[v]&~bit(v);
        if(countBits(shell)!=k)continue;
        Row seen=bit(v),previous=0;
        while(previous!=seen){
          previous=seen;
          for(int w:verts(previous))seen|=fixed[w]&~shell;
        }
        Row forced=seen&~bit(v)&~fixed[v];
        if(forced&~possible[v]){++tot.extensions;return;}
        for(int w:verts(forced)){connect(fixed,v,w);added=true;}
      }
    }
    for(auto [u,v]:keep)if(saturated[u]||saturated[v]){connect(fixed,u,v);added=true;}
    if(!added){
      if(routedThree(fixed,possible,k)){++tot.extensions;return;}
      ++tot.survive;return;
    }
    free=keep;
  }
}
void check(const Graph &e,int p,int k,Totals &tot,bool saturatedShell=false){
  const int b=e.size(),n=b+p+1;
  vector<vector<int>> len(b,vector<int>(b));
  for(int v=0;v<b;v++){
    function<void(int,Row)> walk=[&](int w,Row seen){
      len[v][w]=max(len[v][w],countBits(seen));
      for(int u:verts(e[w]&~seen))walk(u,seen|bit(u));
    };walk(v,bit(v));
  }
  vector<vector<Row>> candidates(b); vector<int> order(b);iota(order.begin(),order.end(),0);
  for(int v=0;v<b;v++){
    int q=countBits(e[v]),tail=*max_element(len[v].begin(),len[v].end());
    int slots=max(0,p-2*tail);
    for(Row raw=0;raw<bit(slots);raw++){
      int a=countBits(raw);
      if((raw&(raw>>1))||q+a<k-1||a>(q?q+1:k-1))continue;
      candidates[v].push_back(raw<<tail);
    }
    if(candidates[v].empty())return;
  }
  stable_sort(order.begin(),order.end(),[&](int x,int y){return candidates[x].size()<candidates[y].size();});
  vector<Row> marks(b);
  function<void(int)> choose=[&](int level){
    if(level<b){
      int v=order[level];
      for(Row mark:candidates[v]){
        bool ok=true;
        for(int ix=0;ix<level&&ok;ix++){
          int u=order[ix],rad=len[u][v];
          for(int d=1;d<=rad;d++)if((mark<<d|mark>>d)&marks[u])ok=false;
          if(e[u]&bit(v)){
            int a=countBits(mark)+countBits(marks[u]);
            if(a+abs(countBits(e[u])-countBits(e[v]))>k)ok=false;
          }
        }
        if(ok){marks[v]=mark;choose(level+1);}
      }
      return;
    }
    Graph first(n);
    for(int j=1;j<p;j++)connect(first,j-1,j);
    for(int v=0;v<b;v++){
      bool touches=false;for(int u=0;u<b;u++)if(len[v][u]&&marks[u])touches=true;
      if(!touches)return;
      for(int u:verts(marks[v]))connect(first,p+v,u);
      for(int u:verts(e[v]))connect(first,p+v,p+u);
      if(countBits(marks[v])+countBits(e[v])==k-1)connect(first,p+v,n-1);
    }
    // All direct edges between P and an exterior vertex, and all exterior edges, are specified.
    for(int v=p;v<p+b;v++){
      Row two=0;for(int u:verts(first[v]))two|=first[u];
      Row exact=two&~first[v]&~bit(v)&(bit(p+b)-1);
      if(countBits(exact)>k)return;
    }
    ++tot.patterns;complete(first,p,k,tot,saturatedShell);
  };
  choose(0);
}
