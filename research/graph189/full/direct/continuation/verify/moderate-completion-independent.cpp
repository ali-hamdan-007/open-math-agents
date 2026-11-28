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
uint32_t canon(const Graph &g) {
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
  uint32_t best=UINT32_MAX; vector<int> order;
  function<void(int)> permute=[&](int i){
    if(i==(int)choices.size()){
      uint32_t e=0;int pos=0;
      for(int a=0;a<n;a++)for(int b=0;b<a;b++,pos++)if(g[order[a]]&bit(order[b]))e|=bit(pos);
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
void complete(Graph fixed,int p,int k,Totals &tot){
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
      int floor=v==n-1?2:k;
      if(countBits(possible[v])<floor || !connected(possible,all^bit(v))){++tot.extensions;return;}
      saturated[v]=countBits(possible[v])==floor;
      Row two=0;for(int w:verts(fixed[v]))two|=fixed[w];
      if(countBits(two&~possible[v]&~bit(v))>k){++tot.extensions;return;}
    }
    bool added=false;
    for(auto [u,v]:keep)if(saturated[u]||saturated[v]){connect(fixed,u,v);added=true;}
    if(!added){++tot.survive;return;}
    free=keep;
  }
}
void check(const Graph &e,int p,int k,Totals &tot){
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
    ++tot.patterns;complete(first,p,k,tot);
  };
  choose(0);
}
int main(int argc,char **argv){
  Graph path(6),star(6);
  for(int i=1;i<6;i++){connect(path,i-1,i);connect(star,0,i);}
  assert(spanningLength(path,63,6));
  assert(!spanningLength(path,63^bit(2),4));
  assert(spanningLength(star,63,3));
  assert(!spanningLength(star,63,4));
  assert(connected(star,63^bit(1)) && !connected(star,63^bit(0)));
  assert(canon(path)!=canon(star));
  Graph relabeled(6);int label[]={4,2,5,0,3,1};
  for(int i=1;i<6;i++)connect(relabeled,label[i-1],label[i]);
  assert(canon(relabeled)==canon(path));
  cout<<"path, cut, and relabeling controls passed"<<endl;
  int maxk=argc>1?atoi(argv[1]):6;
  vector<Totals> totals(maxk+1);vector<Graph> collection(1);
  const int known[]={1,1,2,4,11,34,156,1044,12346};
  for(int b=1;b<=maxk+2;b++){
    map<uint32_t,Graph> next;
    for(const auto& previous:collection)for(Row nbors=0;nbors<bit(b-1);nbors++){
      Graph g=previous;g.push_back(0);
      for(int x:verts(nbors))connect(g,b-1,x);
      uint32_t id=canon(g);if(!next.count(id))next.emplace(id,move(g));
    }
    assert((int)next.size()==known[b]);
    collection.clear();for(auto &[id,g]:next)collection.push_back(move(g));
    for(int k=3;k<=maxk;k++)if((k+1)/2+1<=b && b<=k+2){
      for(const Graph& e:collection){
        int iso=0;bool ok=true;
        for(Row r:e){int q=countBits(r);if(q==0)iso++;else if(q<(k+1)/2-1)ok=false;}
        if(!ok||iso>1)continue;
        for(int p=2*k-1;p+b+1<=3*k+2;p++)if(p+b+1>=2*k+3)check(e,p,k,totals[k]);
      }
      cout<<"b "<<b<<" k "<<k<<" accumulated "<<totals[k].patterns<<endl;
    }
  }
  for(int k=3;k<=maxk;k++){auto t=totals[k];
    cout<<"k "<<k<<" patterns "<<t.patterns<<" immediate "<<t.raw<<" propagation "<<t.extensions<<" remaining "<<t.survive<<endl;}
}
