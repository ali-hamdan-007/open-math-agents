// Split-independent exact screen for the first 58 primes plus at most four new primes.
// Build: c++ -O3 -std=c++17 prime307_support_mitm.cpp -o prime307_support_mitm
// Run:   ./prime307_support_mitm 50000
//
// In any all-prime completion, let A,B be the products on the two sides.
// Reducedness gives the total cofactor sum A^2+B^2 and support product D=AB.
// For any odd prime p in the support, only D/p survives in the cofactor sum
// modulo p, and exactly one side product is divisible by p. Hence D/p is a
// nonzero square modulo p. Every tested residue below is exact.
//
// Pair-pair matches are checked without assuming the pairs use distinct
// primes. Zero matches in this superset proves zero actual support candidates.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
#include <vector>

using Mask = std::uint64_t;

std::vector<unsigned> primes_through(unsigned limit) {
    std::vector<bool> prime(limit + 1, true);
    prime[0] = prime[1] = false;
    for (unsigned p = 2; p <= limit / p; ++p) {
        if (prime[p]) {
            for (unsigned n = p * p; n <= limit; n += p) {
                prime[n] = false;
            }
        }
    }
    std::vector<unsigned> primes;
    for (unsigned p = 2; p <= limit; ++p) {
        if (prime[p]) {
            primes.push_back(p);
        }
    }
    return primes;
}

struct CharacterData {
    Mask target = 0;
    std::vector<Mask> tail_masks;
};

CharacterData character_data(const std::vector<unsigned>& base,
                             const std::vector<unsigned>& tails) {
    CharacterData result;
    result.tail_masks.resize(tails.size());
    for (unsigned j = 1; j < base.size(); ++j) {
        const unsigned p = base[j];
        const Mask bit = Mask{1} << (j - 1);
        std::vector<bool> square(p, false);
        for (unsigned k = 1; k < p; ++k) {
            square[k * k % p] = true;
        }
        unsigned cofactor = 1;
        for (unsigned q : base) {
            if (q != p) {
                cofactor = cofactor * (q % p) % p;
            }
        }
        if (!square[cofactor]) {
            result.target |= bit;
        }
        for (std::size_t i = 0; i < tails.size(); ++i) {
            if (!square[tails[i] % p]) {
                result.tail_masks[i] |= bit;
            }
        }
    }
    return result;
}

struct PairScan {
    std::size_t pairs = 0;
    std::size_t lower_array = 0;
    std::size_t upper_array = 0;
    std::size_t matches = 0;
    std::size_t two_tail_matches = 0;
    std::size_t three_tail_matches = 0;
};

PairScan scan_four_tails(const CharacterData& data) {
    if (data.target == 0) {
        throw std::runtime_error("The two-bank invariant needs a nonzero target.");
    }
    // The selected target bit flips under XOR by the target. Normalize one
    // bank by that XOR. Matches are now exactly intersections of two arrays.
    const Mask bit = data.target & (Mask{0} - data.target);
    const auto& masks = data.tail_masks;
    const auto n = masks.size();
    const auto pair_count = n * (n - 1) / 2;
    const auto set_count = std::count_if(masks.begin(), masks.end(),
                                         [bit](Mask x) { return (x & bit) != 0; });
    const std::size_t opposite = set_count * (n - set_count);
    std::unordered_set<Mask> triples;
    triples.reserve(n);
    for (Mask mask : masks) {
        triples.insert(mask ^ data.target);
    }
    std::size_t two = 0, three = 0;
    std::vector<Mask> same_bank, opposite_bank;
    same_bank.reserve(pair_count - opposite);
    opposite_bank.reserve(opposite);
    for (std::size_t i = 0; i < n; ++i) {
        for (std::size_t j = i + 1; j < n; ++j) {
            const Mask k = masks[i] ^ masks[j];
            two += k == data.target;
            three += triples.count(k);
            if (k & bit) {
                opposite_bank.push_back(k ^ data.target);
            } else {
                same_bank.push_back(k);
            }
        }
    }
    std::sort(same_bank.begin(), same_bank.end());
    std::sort(opposite_bank.begin(), opposite_bank.end());
    auto a = same_bank.begin(), b = opposite_bank.begin();
    std::size_t matches = 0;
    while (a != same_bank.end() && b != opposite_bank.end()) {
        if (*a < *b) {
            ++a;
        } else if (*b < *a) {
            ++b;
        } else {
            ++matches;
            ++a;
            ++b;
        }
    }
    return {pair_count, same_bank.size(), opposite_bank.size(), matches, two, three};
}

int main(int argc, char** argv) {
    const auto limit = argc == 2 ? std::stoul(argv[1]) : 50000UL;
    if (limit < 283 || limit > 100000) {
        throw std::runtime_error("Choose a cap from 283 through 100000.");
    }
    const auto primes = primes_through(static_cast<unsigned>(limit));
    const std::vector<unsigned> base(primes.begin(), primes.begin() + 58);
    const std::vector<unsigned> tails(primes.begin() + 58, primes.end());
    if (base.front() != 2 || base.back() != 271) {
        throw std::logic_error("Unexpected fixed prime support.");
    }
    const auto data = character_data(base, tails);
    const auto result = scan_four_tails(data);
    const auto one = std::count(data.tail_masks.begin(), data.tail_masks.end(), data.target);
    std::cout << "Tail cap: " << limit
              << "\nOdd base congruences: " << base.size() - 1
              << "\nCandidate tail primes: " << tails.size()
              << "\nUnordered tail pairs: " << result.pairs
              << "\nSame-bit bank: " << result.lower_array
              << "\nOpposite-bit bank: " << result.upper_array
              << "\nOne-tail mask matches: " << one
              << "\nTwo-tail mask matches: " << result.two_tail_matches
              << "\nThree-tail mask matches: " << result.three_tail_matches
              << "\nNormalized pair-mask matches: " << result.matches << '\n';
    if (one != 0 || result.two_tail_matches != 0 || result.three_tail_matches != 0 || result.matches != 0) {
        std::cerr << "The residue screen leaves unresolved masks.\n";
        return EXIT_FAILURE;
    }
    std::cout << "No support extension with at most four new primes satisfies the base square conditions.\n";
}
