// Exhaustive rooted incidence and partial-graph verifier. Compile with C++17.
// Usage: ./layer_order even_cap root_degree
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <numeric>
#include <set>
#include <string>
#include <utility>
#include <vector>
#include <unistd.h>

using Mask = std::uint32_t;
using Graph = std::vector<Mask>;
using Pair = std::pair<int,int>;
int cap, root_degree, columns, anchor_edges, max_third;
std::vector<Mask> anchor_neighbors, support;
std::vector<int> allocated;
std::vector<Pair> anchor_pairs;
std::vector<std::vector<int>> automorphisms;
std::set<std::string> profile_keys;
long long candidates, classes, nodes, solutions;
int count_bits(Mask mask) { return __builtin_popcount(mask); }
int first(Mask mask) { return __builtin_ctz(mask); }
Mask bit(int index) { return Mask(1) << index; }
void check_live() {
    if (access("../PAUSE", F_OK)==0 || access("../HALT", F_OK)==0) std::exit(100);
}
void set_edge(Graph& graph, int i, int j, bool present) {
    if (present) { graph[i] |= bit(j); graph[j] |= bit(i); }
    else { graph[i] &= ~bit(j); graph[j] &= ~bit(i); }
}
Mask neighbors(const Graph& graph, Mask set) {
    Mask answer=0;
    for (;set;set&=set-1) answer |= graph[first(set)];
    return answer;
}
// lower ⊆ actual ⊆ upper. Actual diameter at most four, all nonroots high.
bool impossible(const Graph& lower, const Graph& upper) {
    const int n=lower.size();
    const Mask all=bit(n)-1;
    for (int x=0;x<n;++x) {
        if (count_bits(upper[x]) < (x==0 ? root_degree : cap)) return true;
        Mask two=neighbors(lower,lower[x]) & ~(upper[x]|bit(x));
        Mask ball2=bit(x)|upper[x]|neighbors(upper,upper[x]);
        Mask ball3=ball2|neighbors(upper,ball2 & ~(upper[x]|bit(x)));
        Mask far=all & ~ball3;
        if (count_bits(two|far)>cap) return true;
        for (Mask left=far;left;left&=left-1) {
            if (!(upper[first(left)]&ball3)) return true;
        }
    }
    return false;
}
void search(Graph lower, Graph upper) {
    if ((++nodes & 1023)==0) check_live();
    const int n=lower.size();
    for (;;) {
        if (impossible(lower,upper)) return;
        bool changed=false;
        for (int i=0;i<n;++i) {
            if (count_bits(upper[i])==(i==0 ? root_degree : cap)) {
                for (Mask s=upper[i]&~lower[i];s;s&=s-1) {
                    set_edge(lower,i,first(s),true);
                    changed=true;
                }
            }
        }
        if (changed) continue;
        int best=-1000;
        Pair branch={-1,-1};
        for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) {
            if (!(upper[i]&bit(j)) || (lower[i]&bit(j))) continue;
            set_edge(upper,i,j,false);
            bool necessary=impossible(lower,upper);
            set_edge(upper,i,j,true);
            if (necessary) {
                set_edge(lower,i,j,true);
                changed=true;
                continue;
            }
            set_edge(lower,i,j,true);
            bool excluded=impossible(lower,upper);
            set_edge(lower,i,j,false);
            if (excluded) {
                set_edge(upper,i,j,false);
                changed=true;
                continue;
            }
            int score=count_bits(lower[i]^lower[j])-count_bits(upper[i])-count_bits(upper[j]);
            if (score>best) { best=score; branch={i,j}; }
        }
        if (changed) continue;
        if (branch.first<0) {
            ++solutions;
            std::printf("completion n=%d rows",n);
            for (Mask row:lower) std::printf(" %x",row);
            std::puts("");
            std::fflush(stdout);
            return;
        }
        auto [i,j]=branch;
        Graph present=lower;
        set_edge(present,i,j,true);
        search(present,upper);
        set_edge(upper,i,j,false);
        search(lower,upper);
        return;
    }
}
Mask relabel(Mask subset, const std::vector<int>& perm) {
    Mask answer=0;
    for (;subset;subset&=subset-1) answer |= bit(perm[first(subset)]);
    return answer;
}
std::string profile_key() {
    std::string smallest;
    for (auto& perm : automorphisms) {
        std::vector<int> items;
        for (int j=0;j<columns;++j) items.push_back(relabel(support[j],perm)*8+allocated[j]);
        std::sort(items.begin(),items.end());
        std::string word;
        for (int code:items) { word.push_back(char(code>>8)); word.push_back(char(code&255)); }
        if (smallest.empty() || word<smallest) smallest=word;
    }
    return smallest;
}
void evaluate(int third) {
    max_third=std::max(max_third,third);
    int min_fourth=std::max(0,3*cap+3-(1+root_degree+columns+third));
    if (min_fourth>cap-columns) return;
    ++candidates;
    if (!profile_keys.insert(profile_key()).second) return;
    for (int fourth=min_fourth;fourth<=cap-columns;++fourth) {
        int n=1+root_degree+columns+third+fourth;
        if (n>=31) { std::fprintf(stderr,"mask too short\n"); std::exit(2); }
        Graph lower(n),upper(n);
        auto layer=[&](int i){ return i==0 ? 0 : i<=root_degree ? 1 : i<=root_degree+columns ? 2 : i<=root_degree+columns+third ? 3 : 4; };
        for (int i=0;i<n;++i) for (int j=i+1;j<n;++j) {
            if (std::abs(layer(i)-layer(j))<=1) set_edge(upper,i,j,true);
        }
        for (int i=0;i<root_degree;++i) {
            set_edge(lower,0,1+i,true);
            for (int j=i+1;j<root_degree;++j) {
                if (anchor_neighbors[i]&bit(j)) set_edge(lower,i+1,j+1,true);
                else set_edge(upper,i+1,j+1,false);
            }
            for (int j=0;j<columns;++j) {
                if (support[j]&bit(i)) set_edge(lower,1+i,1+root_degree+j,true);
                else set_edge(upper,1+i,1+root_degree+j,false);
            }
        }
        int vertex=1+root_degree+columns;
        for (int j=0;j<columns;++j) for (int t=0;t<allocated[j];++t) {
            set_edge(lower,1+root_degree+j,vertex++,true);
        }
        ++classes;
        search(lower,upper);
    }
}
void allocate(int col,int total,std::vector<int>& remaining) {
    if (col==columns) { evaluate(total); return; }
    int limit=cap;
    for (Mask s=support[col];s;s&=s-1) limit=std::min(limit,remaining[first(s)]);
    for (int value=0;value<=limit;++value) {
        allocated[col]=value;
        for (Mask s=support[col];s;s&=s-1) remaining[first(s)]-=value;
        allocate(col+1,total+value,remaining);
        for (Mask s=support[col];s;s&=s-1) remaining[first(s)]+=value;
    }
}
void choose_columns(int col,Mask minimum) {
    if (col<columns) {
        for (Mask m=minimum;m<bit(root_degree);++m) {
            support[col]=m;
            choose_columns(col+1,m);
        }
        return;
    }
    Graph rows(root_degree);
    for (int j=0;j<columns;++j) for (Mask s=support[j];s;s&=s-1) rows[first(s)]|=bit(j);
    std::vector<int> remaining(root_degree);
    for (int i=0;i<root_degree;++i) {
        int anchor_degree=count_bits(anchor_neighbors[i]);
        if (1+anchor_degree+count_bits(rows[i])<cap) return;
        int missed=count_bits(neighbors(rows,anchor_neighbors[i])&~rows[i]);
        remaining[i]=cap-(root_degree-1-anchor_degree)-missed;
        if (remaining[i]<0) return;
    }
    allocate(0,0,remaining);
}
// Visit one anchor graph per permutation class; record its stabilizer.
bool canonical_anchors() {
    std::vector<int> perm(root_degree);
    std::iota(perm.begin(),perm.end(),0);
    automorphisms.clear();
    do {
        int code=0;
        for (int i=0;i<(int)anchor_pairs.size();++i) {
            auto [a,b]=anchor_pairs[i];
            if (anchor_neighbors[perm[a]]&bit(perm[b])) code|=bit(i);
        }
        if (code<anchor_edges) return false;
        if (code==anchor_edges) automorphisms.push_back(perm);
    } while (std::next_permutation(perm.begin(),perm.end()));
    return true;
}
int main(int argc,char** argv) {
    if (argc!=3) { std::fprintf(stderr,"usage: layer_order cap root_degree\n"); return 2; }
    cap=std::atoi(argv[1]);
    root_degree=std::atoi(argv[2]);
    if (cap<3 || cap>6 || root_degree<3 || root_degree>cap) return 2;
    anchor_neighbors.resize(root_degree);
    for(int i=0;i<root_degree;++i) for(int j=i+1;j<root_degree;++j) anchor_pairs.emplace_back(i,j);
    for (columns=1;columns<=cap;++columns) {
        max_third=-1;
        candidates=classes=nodes=solutions=0;
        support.resize(columns);
        allocated.resize(columns);
        for (anchor_edges=0;anchor_edges<(1<<anchor_pairs.size());++anchor_edges) {
            check_live();
            std::fill(anchor_neighbors.begin(),anchor_neighbors.end(),0);
            for (int i=0;i<(int)anchor_pairs.size();++i) if(anchor_edges&bit(i)) {
                auto [a,b]=anchor_pairs[i];
                set_edge(anchor_neighbors,a,b,true);
            }
            if (!canonical_anchors()) continue;
            profile_keys.clear();
            if (std::getenv("PROFILE_PROGRESS")) { std::fprintf(stderr,"b=%d edges=%d nodes=%lld classes=%lld\n",columns,anchor_edges,nodes,classes); }
            choose_columns(0,1);
        }
        std::printf("k=%d a=%d b=%d max-third=%d candidates=%lld classes=%lld nodes=%lld completions=%lld\n",cap,root_degree,columns,max_third,candidates,classes,nodes,solutions);
        std::fflush(stdout);
    }
}
