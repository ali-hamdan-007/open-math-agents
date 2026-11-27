#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

namespace {

using Mask = std::uint64_t;
constexpr int capacity = 64;

constexpr Mask bit(int vertex) { return Mask{1} << vertex; }

template <typename Function>
void for_each_vertex(Mask vertices, Function function) {
    while (vertices) {
        function(std::countr_zero(vertices));
        vertices &= vertices - 1;
    }
}

struct Graph {
    int order = 0;
    std::array<Mask, capacity> neighbors{};

    Mask vertices() const { return bit(order) - 1; }

    void add_edge(int x, int y) {
        neighbors[x] |= bit(y);
        neighbors[y] |= bit(x);
    }

    int add_vertex(Mask adjacent) {
        if (order >= capacity - 1) throw std::runtime_error("graph capacity exceeded");
        const int vertex = order++;
        for_each_vertex(adjacent, [&](int other) { add_edge(vertex, other); });
        return vertex;
    }

    bool has_square() const {
        for (int x = 0; x < order; ++x)
            for (int y = 0; y < x; ++y)
                if (std::popcount(neighbors[x] & neighbors[y]) > 1) return true;
        return false;
    }

    bool path_from(int endpoint, int requested_order, Mask forbidden) const {
        if (requested_order == 1) return true;
        for (Mask next = neighbors[endpoint] & ~forbidden; next; next &= next - 1) {
            const int vertex = std::countr_zero(next);
            if (path_from(vertex, requested_order - 1,
                          forbidden | bit(vertex) | neighbors[endpoint]))
                return true;
        }
        return false;
    }

    bool has_induced_p8() const {
        for (int x = 0; x < order; ++x)
            if (path_from(x, 8, bit(x))) return true;
        return false;
    }

    bool admissible() const { return !has_square() && !has_induced_p8(); }

    std::array<int, capacity> distances_through_three(int source) const {
        std::array<int, capacity> distances;
        distances.fill(4);
        distances[source] = 0;
        Mask frontier = bit(source);
        Mask seen = frontier;
        for (int distance = 1; distance <= 3; ++distance) {
            Mask next = 0;
            for_each_vertex(frontier, [&](int v) { next |= neighbors[v]; });
            frontier = next & ~seen;
            seen |= frontier;
            for_each_vertex(frontier, [&](int v) { distances[v] = distance; });
        }
        return distances;
    }
};

Graph cycle(int order) {
    Graph graph;
    graph.order = order;
    for (int x = 0; x < order; ++x) graph.add_edge(x, (x + 1) % order);
    return graph;
}

std::vector<Mask> possible_contacts(const Graph& core) {
    std::vector<Mask> contacts;
    for (Mask mask = 1; mask <= core.vertices(); ++mask) {
        Graph extended = core;
        extended.add_vertex(mask);
        if (extended.admissible()) contacts.push_back(mask);
    }
    return contacts;
}

void require(bool fact, const char* failure) {
    if (!fact) throw std::runtime_error(failure);
}

void check_six_cycle_with_leaves() {
    Graph core = cycle(6);
    for (int vertex = 0; vertex < 6; ++vertex) core.add_vertex(bit(vertex));

    std::vector<Mask> contacts = possible_contacts(core);
    std::vector<Mask> expected;
    std::vector<Mask> bridges;
    for (int v = 0; v < 6; ++v) {
        expected.push_back(bit(v));
        expected.push_back(bit(v) | bit((v + 1) % 6));
        expected.push_back(bit(v) | bit(6 + v));
    }
    for (int v = 0; v < 3; ++v) {
        const Mask opposite = bit(v) | bit(v + 3);
        for (Mask leaves : {Mask{0}, bit(v + 6), bit(v + 9), bit(v + 6) | bit(v + 9)}) {
            bridges.push_back(opposite | leaves);
            expected.push_back(opposite | leaves);
        }
    }
    std::sort(expected.begin(), expected.end());
    require(contacts == expected, "unexpected C6-ciliate contact patterns");

    for (Mask left : contacts) {
        const bool bridge = std::find(bridges.begin(), bridges.end(), left) != bridges.end();
        Graph extended = core;
        const int x = extended.add_vertex(left);
        if (bridge) {
            require(extended.path_from(x, 5, bit(x)), "bridge lacks its five-vertex path");
        } else {
            extended.add_vertex(bit(x));
            require(!extended.admissible(), "a nonbridge can touch a vertex two layers out");
        }

        for (Mask right : contacts) {
            Graph adjacent = core;
            const int v = adjacent.add_vertex(left);
            adjacent.add_vertex(right | bit(v));
            require((left & right) || !adjacent.admissible(),
                    "an edge between outside vertices has no common core neighbor");
        }
    }

    for (Mask left : bridges) {
        for (Mask right : bridges) {
            Graph extended = core;
            const int x = extended.add_vertex(left);
            const int y = extended.add_vertex(right);
            Graph adjacent = extended;
            adjacent.add_edge(x, y);
            require(!adjacent.admissible(), "two distinct bridges can be adjacent");
            Graph path = extended;
            const int first = path.add_vertex(bit(x));
            path.add_vertex(bit(first) | bit(y));
            require(!path.admissible(), "a three-edge chordless link between bridges is allowed");
        }
    }

    std::cout << "C6 ciliate: " << contacts.size() << " contact patterns, "
              << bridges.size() << " bridge patterns; all tests passed\n";
}

std::vector<Graph> eight_cycle_boundaries(const Graph& core) {
    const std::vector<Mask> types = possible_contacts(core);
    require(types.size() == 32, "unexpected C8 contact count");
    for (Mask mask : types) {
        require(std::popcount(mask) >= 2, "a direct outside vertex has fewer than two contacts");
        Graph extended = core;
        const int x = extended.add_vertex(mask);
        require(extended.path_from(x, 4, bit(x)), "an outside vertex lacks its four-vertex path");
    }

    std::vector<Graph> boundaries;
    auto extend = [&](auto& self, const Graph& current, std::size_t first_type) -> void {
        boundaries.push_back(current);
        for (std::size_t next_type = first_type; next_type < types.size(); ++next_type) {
            const Mask mask = types[next_type];
            Mask possible_edges = 0;
            for (int v = core.order; v < current.order; ++v) {
                Graph pair = core;
                const int old = pair.add_vertex(current.neighbors[v] & core.vertices());
                pair.add_vertex(mask | bit(old));
                if (pair.admissible()) possible_edges |= bit(v);
            }
            for (Mask edges = possible_edges;; edges = (edges - 1) & possible_edges) {
                Graph extended = current;
                extended.add_vertex(mask | edges);
                if (extended.admissible()) self(self, extended, next_type + 1);
                if (!edges) break;
            }
        }
    };
    extend(extend, core, 0);
    return boundaries;
}

using Witnesses = std::vector<std::pair<int, int>>;

struct WitnessSearch {
    int states = 0;
    int largest_order = 0;

    void eliminate(const Graph& graph, const Witnesses& witnesses) {
        ++states;
        largest_order = std::max(largest_order, graph.order);

        int center = -1;
        int best_score = 10000;
        std::array<int, capacity> center_distances{};
        for (int u = 0; u < graph.order; ++u) {
            const auto distances = graph.distances_through_three(u);
            for (const auto& [source, far] : witnesses)
                if (source == u && distances[far] < 4) return;

            int sum = 0;
            bool is_center = true;
            for (int v = 0; v < graph.order; ++v) {
                if (distances[v] == 4) is_center = false;
                if (v >= 8) sum += distances[v];
            }
            if (is_center && sum < best_score) {
                center = u;
                center_distances = distances;
                best_score = sum;
            }
        }
        require(center >= 0, "the recursion found an admissible graph of radius at least four");
        require(graph.order <= 35, "witness recursion exceeded replay limit");

        for (int length = 1; length <= 3; ++length) {
            Mask eligible = 0;
            for (int v = 8; v < graph.order; ++v)
                if (center_distances[v] >= 4 - length) eligible |= bit(v);

            auto add_paths = [&](auto& self, Mask remaining, Mask adjacent) -> void {
                if (adjacent) {
                    Graph extended = graph;
                    int tip = extended.add_vertex(adjacent);
                    for (int i = 1; i < length; ++i) tip = extended.add_vertex(bit(tip));
                    if (!extended.has_induced_p8()) {
                        Witnesses next = witnesses;
                        next.emplace_back(center, tip);
                        eliminate(extended, next);
                    }
                }
                while (remaining) {
                    const int v = std::countr_zero(remaining);
                    remaining &= remaining - 1;
                    Mask compatible = remaining;
                    for_each_vertex(remaining, [&](int w) {
                        if (graph.neighbors[v] & graph.neighbors[w]) compatible &= ~bit(w);
                    });
                    self(self, compatible, adjacent | bit(v));
                }
            };
            add_paths(add_paths, eligible, 0);
        }
    }
};

void check_eight_cycle() {
    const Graph core = cycle(8);
    const auto boundaries = eight_cycle_boundaries(core);
    require(boundaries.size() == 790, "unexpected C8 boundary count");
    WitnessSearch check;
    for (const Graph& graph : boundaries)
        if (graph.order > core.order) check.eliminate(graph, {});
    std::cout << "C8: " << boundaries.size() << " boundary graphs, " << check.states
              << " witness states of order at most " << check.largest_order << "; all eliminated\n";
}

}  // namespace

int main() {
    try {
        check_six_cycle_with_leaves();
        check_eight_cycle();
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
