// Enumerate necessary shell and core conditions for degree-five (a,s)=(4,4).
// Build: c++ -std=c++17 -O3 four-port-census.cpp -o four-port-census
// Run: ./four-port-census 6  (also accepts 7, 8, and 9)
#include <algorithm>
#include <array>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <numeric>
#include <vector>

using Four = std::array<int, 4>;
using Five = std::array<int, 5>;
using Bounds = std::array<int, 16>;

int count(int bits) { return __builtin_popcount(static_cast<unsigned>(bits)); }
bool has(int bits, int index) { return (bits & (1 << index)) != 0; }

std::vector<Five> small_graphs(int order) {
    std::vector<Five> graphs;
    int edges = order * (order - 1) / 2;
    for (int bits = 0; bits < (1 << edges); ++bits) {
        Five adjacency{};
        int edge = 0;
        for (int i = 0; i < order; ++i) {
            for (int j = 0; j < i; ++j, ++edge) {
                if (has(bits, edge)) {
                    adjacency[i] |= 1 << j;
                    adjacency[j] |= 1 << i;
                }
            }
        }
        graphs.push_back(adjacency);
    }
    return graphs;
}

std::vector<Bounds> port_relabelings() {
    std::vector<Bounds> images;
    Four permutation{0, 1, 2, 3};
    do {
        Bounds image{};
        for (int mask = 0; mask < 16; ++mask) {
            for (int p = 0; p < 4; ++p) {
                if (has(mask, p)) image[mask] |= 1 << permutation[p];
            }
        }
        images.push_back(image);
    } while (std::next_permutation(permutation.begin(), permutation.end()));
    return images;
}

struct Counts {
    int shells = 0;
    int masks = 0;
    int types = 0;
    int degree = 0;
    int connected = 0;
};

struct Census {
    int k;
    int incidences = 0;
    std::array<Counts, 32> by_order{};
    std::vector<Five> anchor_graphs = small_graphs(5);
    std::vector<Five> port_graphs = small_graphs(4);
    std::vector<Bounds> permutations = port_relabelings();

    bool representative(const Five& incident) const {
        int covered = 0;
        for (int mask : incident) covered |= mask;
        if (covered != 15) return false;
        for (const auto& image : permutations) {
            Five relabeled;
            for (int a = 0; a < 5; ++a) relabeled[a] = image[incident[a]];
            std::sort(relabeled.begin(), relabeled.end());
            if (relabeled < incident) return false;
        }
        return true;
    }

    void check_core(const std::vector<int>& masks, const std::vector<int>& witnesses,
                    const Five& port_graph, Counts& result) const {
        ++result.types;
        int h = masks.size();
        std::vector<int> neighbors(h + 4);
        for (int p = 0; p < 4; ++p) neighbors[p] = port_graph[p];
        for (int i = 0; i < h; ++i) {
            int x = i + 4;
            neighbors[x] = masks[i];
            for (int p = 0; p < 4; ++p) {
                if (has(masks[i], p)) neighbors[p] |= 1 << x;
            }
            for (int j = 0; j < i; ++j) {
                bool forward = (masks[i] & ~(masks[j] | witnesses[j])) == 0;
                bool reverse = (masks[j] & ~(masks[i] | witnesses[i])) == 0;
                if (forward && reverse) {
                    neighbors[x] |= 1 << (j + 4);
                    neighbors[j + 4] |= 1 << x;
                }
            }
        }
        for (int x = 4; x < h + 4; ++x) {
            if (count(neighbors[x]) < k) return;
        }
        ++result.degree;
        int reached = 1, previous = 0;
        while (reached != previous) {
            previous = reached;
            for (int x = 0; x < h + 4; ++x) {
                if (has(reached, x)) reached |= neighbors[x];
            }
        }
        if (count(reached) == h + 4) ++result.connected;
    }

    void enumerate_witnesses(const std::vector<int>& masks, const Five& port_graph,
                             const Four& shell_two_ports, Four slots, Counts& result) const {
        int h = masks.size();
        std::vector<int> mandatory(h);
        for (int p = 0; p < 4; ++p) {
            int shared = 0, required = 0;
            for (int i = 0; i < h; ++i) {
                if (has(masks[i], p)) shared |= masks[i];
                else if (masks[i] & port_graph[p]) {
                    mandatory[i] |= 1 << p;
                    ++required;
                }
            }
            int newly_two = shared & ~(shell_two_ports[p] | port_graph[p] | (1 << p));
            slots[p] -= count(newly_two);
            if (required > slots[p]) return;
        }
        int private_count = std::count_if(masks.begin(), masks.end(),
                                         [](int mask) { return count(mask) == 1; });
        if (private_count > std::accumulate(slots.begin(), slots.end(), 0)) return;
        ++result.masks;

        std::vector<int> witnesses(h);
        std::function<void(int)> visit = [&](int i) {
            if (i == h) {
                check_core(masks, witnesses, port_graph, result);
                return;
            }
            int start = (i != 0 && masks[i] == masks[i-1]) ? witnesses[i-1] : 0;
            for (int set = start; set < 16; ++set) {
                if ((set & masks[i]) || (mandatory[i] & ~set)) continue;
                if (!set && count(masks[i]) == 1) continue;
                bool fits = true;
                for (int p = 0; p < 4; ++p) {
                    if (has(set, p) && slots[p] == 0) fits = false;
                }
                if (!fits) continue;
                witnesses[i] = set;
                for (int p = 0; p < 4; ++p) if (has(set, p)) --slots[p];
                visit(i + 1);
                for (int p = 0; p < 4; ++p) if (has(set, p)) ++slots[p];
            }
        };
        visit(0);
    }

    void enumerate_masks(int h, const Bounds& cap, const Four& lower, const Five& port_graph,
                         const Four& shell_two_ports, const Four& slots) {
        std::vector<int> masks(h);
        Bounds used{};
        std::function<void(int,int)> visit = [&](int i, int start) {
            if (i == h) {
                for (int p = 0; p < 4; ++p) if (used[1 << p] < lower[p]) return;
                enumerate_witnesses(masks, port_graph, shell_two_ports, slots, by_order[h]);
                return;
            }
            for (int mask = start; mask < 16; ++mask) {
                bool fits = true;
                for (int set = 1; set < 16; ++set) {
                    if ((mask & set) && used[set] == cap[set]) fits = false;
                }
                if (!fits) continue;
                masks[i] = mask;
                for (int set = 1; set < 16; ++set) if (mask & set) ++used[set];
                visit(i + 1, mask);
                for (int set = 1; set < 16; ++set) if (mask & set) --used[set];
            }
        };
        visit(0, 1);
    }

    void check_shell(const Five& incident, const Four& anchors_of_port, const Five& anchors,
                     const Five& ports, const Five& via_anchors, const Four& near_anchors) {
        Bounds cap;
        cap.fill(100);
        cap[0] = 0;
        Four single, lower, slots, two_ports;
        single.fill(k - 1);
        for (int a = 0; a < 5; ++a) {
            int reached = via_anchors[a];
            for (int p = 0; p < 4; ++p) if (has(incident[a], p)) reached |= ports[p];
            int missed_anchors = 4 - count(anchors[a]);
            int missed_ports = count(reached & ~incident[a]);
            int limit = std::min(k - 1, k - missed_anchors - missed_ports);
            if (limit < 0) return;
            cap[incident[a]] = std::min(cap[incident[a]], limit);
            for (int p = 0; p < 4; ++p) {
                if (has(incident[a], p)) single[p] = std::min(single[p], limit);
            }
        }
        for (int p = 0; p < 4; ++p) {
            lower[p] = std::max(0, k - count(anchors_of_port[p]) - count(ports[p]));
            if (lower[p] > single[p]) return;
            int seen_anchors = near_anchors[p], seen_ports = 0;
            for (int q = 0; q < 4; ++q) {
                if (has(ports[p], q)) {
                    seen_anchors |= anchors_of_port[q];
                    seen_ports |= ports[q];
                }
                if (anchors_of_port[p] & anchors_of_port[q]) seen_ports |= 1 << q;
            }
            two_ports[p] = seen_ports & ~(ports[p] | (1 << p));
            slots[p] = 3 - count(seen_anchors & ~anchors_of_port[p]) - count(two_ports[p]);
            if (slots[p] < 0) return;
            int neighborhood = ports[p] | (1 << p);
            cap[1 << p] = std::min(cap[1 << p], single[p]);
            cap[neighborhood] = std::min(cap[neighborhood], single[p] + slots[p]);
        }
        for (int set = 15; set >= 1; --set) {
            for (int p = 0; p < 4; ++p) if (has(set, p)) {
                int smaller = set ^ (1 << p);
                cap[smaller] = std::min(cap[smaller], cap[set]);
            }
        }
        for (int set = 1; set < 16; ++set) {
            for (int part = (set - 1) & set; part; part = (part - 1) & set) {
                cap[set] = std::min(cap[set], cap[part] + cap[set ^ part]);
            }
        }
        int max_private = 0;
        for (int p = 0; p < 4; ++p) {
            if (single[p] + slots[p] >= k) max_private += single[p];
        }
        max_private = std::min(max_private, std::accumulate(slots.begin(), slots.end(), 0));
        int maximum = std::min(cap[15], (std::accumulate(single.begin(), single.end(), 0)
                                         + max_private) / 2);
        if (maximum < 2*k - 3) return;
        ++by_order[maximum].shells;
        for (int h = 2*k - 3; h <= maximum; ++h) {
            enumerate_masks(h, cap, lower, ports, two_ports, slots);
        }
    }

    void check_incidence(const Five& incident) {
        if (!representative(incident)) return;
        ++incidences;
        Four anchors_of_port{};
        for (int a = 0; a < 5; ++a) {
            for (int p = 0; p < 4; ++p) if (has(incident[a], p)) anchors_of_port[p] |= 1 << a;
        }
        for (const auto& anchors : anchor_graphs) {
            bool degrees_ok = true;
            Five via_anchors{};
            Four near_anchors{};
            for (int a = 0; a < 5; ++a) {
                if (count(anchors[a]) + count(incident[a]) < 3) degrees_ok = false;
                for (int j = 0; j < 5; ++j) if (has(anchors[a], j)) via_anchors[a] |= incident[j];
                for (int p = 0; p < 4; ++p) if (has(incident[a], p)) near_anchors[p] |= anchors[a];
            }
            if (!degrees_ok) continue;
            for (const auto& ports : port_graphs) {
                check_shell(incident, anchors_of_port, anchors, ports, via_anchors, near_anchors);
            }
        }
    }

    void run() {
        Five incident{};
        std::function<void(int,int)> visit = [&](int a, int start) {
            if (a == 5) {
                check_incidence(incident);
                return;
            }
            for (int mask = start; mask < 15; ++mask) {
                incident[a] = mask;
                visit(a + 1, mask);
            }
        };
        visit(0, 0);
        std::cout << "Incidence representatives " << incidences
                  << "\nh  shells(max=h)  masks  types  degree  connected\n";
        for (int h = 2*k - 3; h <= 2*k + 4; ++h) {
            const auto& row = by_order[h];
            std::cout << h << " " << row.shells << " " << row.masks << " " << row.types
                      << " " << row.degree << " " << row.connected << "\n";
        }
    }
};

int main(int argc, char** argv) {
    if (argc != 2 || argv[1][0] < '6' || argv[1][0] > '9' || argv[1][1] != '\0') {
        std::cerr << "Specify one of 6, 7, 8, 9.\n";
        return EXIT_FAILURE;
    }
    Census census{argv[1][0] - '0'};
    census.run();
}
