// Verify remaining graph orders for specified small degrees after the quadratic bound.
// Input limit 11 permits an injective 64-bit encoding of a labelled exterior graph.
#include "degree-window-engine.cpp"

bool possibleAttachment(const Graph &g,int cap){
  if(int(g.size())<=cap)return true;
  function<bool(int,Row,int)> exceeds=[&](int v,Row used,int length){
    if(length>cap)return true;
    for(int w:verts(g[v]&~used))if(exceeds(w,used|bit(w),length+1))return true;
    return false;
  };
  for(unsigned i=0;i<g.size();i++)if(!exceeds(i,bit(i),1))return true;
  return false;
}

map<pair<int,int>,vector<Graph>> table;
const vector<Graph>& componentTypes(int size,int cap){
  auto key=make_pair(size,cap);
  if(table.count(key))return table.at(key);
  auto &out=table[key];
  if(size==1){out.push_back({0});return out;}
  set<uint64_t> seen;
  for(const Graph &old:componentTypes(size-1,cap)){
    for(Row row=1;row<bit(size-1);row++){
      Graph candidate=old;candidate.push_back(0);
      for(int j:verts(row))connect(candidate,size-1,j);
      if(possibleAttachment(candidate,cap)&&seen.insert(canon(candidate)).second)
        out.push_back(move(candidate));
    }
  }
  return out;
}

int main(int argc,char**argv){
  if(argc!=4)return 2;
  int k=atoi(argv[1]),first=atoi(argv[2]),last=atoi(argv[3]),h=(k+1)/2;
  if(k<3||last<first||last-2*k>11||last>30)return 2;
  bool solved=true;
  for(int n=first;n<=last;n++){
    Totals total;
    for(int b=h+1;b<=n-2*k;b++){
      int p=n-b-1,cap=(p-1)/2;
      vector<Graph> blocks;
      for(int size=1;size<=b;size++){
        if(size>1&&size<h)continue;
        for(const auto&g:componentTypes(size,cap)){
          bool ok=true;
          for(Row r:g)if(size>1&&countBits(r)<h-1)ok=false;
          if(ok)blocks.push_back(g);
        }
      }
      int checked=0;
      function<void(size_t,Graph)> join=[&](size_t i,Graph assembled){
        if(int(assembled.size())==b){
          ++checked;check(assembled,p,k,total,true);return;
        }
        for(size_t j=i;j<blocks.size();j++){
          auto &g=blocks[j];
          if(assembled.size()+g.size()>size_t(b))break;
          Graph combined=assembled;
          for(Row r:g)combined.push_back(r<<assembled.size());
          join(j+(g.size()==1),move(combined));
        }
      };
      join(0,{});
      cout<<"n "<<n<<" p "<<p<<" b "<<b<<" exteriors "<<checked<<endl;
    }
    cout<<"k "<<k<<" n "<<n<<" patterns "<<total.patterns<<" direct "<<total.raw
        <<" propagation "<<total.extensions<<" left "<<total.survive<<endl;
    solved &= (total.survive==0);
  }
  return solved?0:1;
}
