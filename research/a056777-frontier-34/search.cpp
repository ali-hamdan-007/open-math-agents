#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <map>
#include <string>
#include <vector>

struct Factorization {
    std::string shape;
    uint64_t sigma = 1;
    std::string expanded;
};

struct Counts {
    uint64_t candidates = 0;
    uint64_t phi_only = 0;
    uint64_t sigma_only = 0;
    uint64_t both = 0;
    uint32_t first_phi = 0;
    uint32_t first_sigma = 0;
    uint32_t first_both = 0;
};

Factorization factorize(uint32_t n, const std::vector<uint32_t>& least_prime) {
    std::string exponents;
    std::string expanded;
    uint64_t sigma = 1;
    while (n > 1) {
        const uint32_t p = least_prime[n];
        unsigned exponent = 0;
        uint64_t power = 1;
        uint64_t local_sigma = 1;
        do {
            n /= p;
            ++exponent;
            power *= p;
            local_sigma += power;
        } while (n % p == 0);
        sigma *= local_sigma;
        exponents += char('0' + exponent);
        if (!expanded.empty()) expanded += '*';
        expanded += std::to_string(p);
        if (exponent > 1) expanded += '^' + std::to_string(exponent);
    }
    std::sort(exponents.begin(), exponents.end(), std::greater<>());
    return {exponents, sigma, expanded};
}

void record(Counts& counts, uint32_t n, bool phi, bool sigma) {
    ++counts.candidates;
    if (phi && sigma) {
        ++counts.both;
        if (counts.first_both == 0) counts.first_both = n;
    } else if (phi) {
        ++counts.phi_only;
        if (counts.first_phi == 0) counts.first_phi = n;
    } else if (sigma) {
        ++counts.sigma_only;
        if (counts.first_sigma == 0) counts.first_sigma = n;
    }
}

int main(int argc, char** argv) {
    constexpr uint32_t gap = 12;
    uint32_t limit = 10000000;
    if (argc == 2) {
        char* tail = nullptr;
        const unsigned long parsed = std::strtoul(argv[1], &tail, 10);
        if (tail == argv[1] || *tail != '\0' || parsed < 2 ||
            parsed > std::numeric_limits<uint32_t>::max() - gap - 1) return 2;
        limit = static_cast<uint32_t>(parsed);
    } else if (argc != 1) {
        return 2;
    }
    const uint32_t end = limit + gap;
    std::vector<uint32_t> least_prime(end + 1);
    std::vector<uint32_t> phi(end + 1);
    std::vector<uint8_t> omega(end + 1);
    std::vector<uint32_t> primes;
    phi[1] = 1;
    for (uint32_t i = 2; i <= end; ++i) {
        if (least_prime[i] == 0) {
            least_prime[i] = i;
            phi[i] = i - 1;
            omega[i] = 1;
            primes.push_back(i);
        }
        for (uint32_t p : primes) {
            const uint64_t composite = uint64_t(i) * p;
            if (composite > end) break;
            least_prime[composite] = p;
            omega[composite] = omega[i] + 1;
            if (p == least_prime[i]) {
                phi[composite] = phi[i] * p;
                break;
            }
            phi[composite] = phi[i] * (p - 1);
        }
    }

    std::map<std::string, Counts> table;
    std::vector<uint32_t> survivors;
    for (uint32_t n = 2; n <= limit; ++n) {
        const uint32_t m = n + gap;
        if (!((omega[n] == 3 && omega[m] == 4) ||
              (omega[n] == 4 && omega[m] == 3))) continue;
        const auto fn = factorize(n, least_prime);
        const auto fm = factorize(m, least_prime);
        const bool phi_shift = phi[m] == phi[n] + gap;
        const bool sigma_shift = fm.sigma == fn.sigma + gap;
        record(table[std::to_string(omega[n]) + "->" + std::to_string(omega[m])],
               n, phi_shift, sigma_shift);
        record(table[fn.shape + "->" + fm.shape], n, phi_shift, sigma_shift);
        if (phi_shift || sigma_shift) survivors.push_back(n);
    }
    std::cout << "n range [2," << limit << "], inclusive; gap " << gap << '\n';
    std::cout << "shape,candidates,phi_only,sigma_only,both,neither,first_phi_only,first_sigma_only,first_both\n";
    for (const auto& [shape, counts] : table) {
        const uint64_t neither = counts.candidates - counts.phi_only - counts.sigma_only - counts.both;
        std::cout << shape << ',' << counts.candidates << ',' << counts.phi_only << ','
                  << counts.sigma_only << ',' << counts.both << ',' << neither << ','
                  << counts.first_phi << ',' << counts.first_sigma << ',' << counts.first_both << '\n';
    }
    for (uint32_t n : survivors) {
        const uint32_t m = n + gap;
        const auto fn = factorize(n, least_prime);
        const auto fm = factorize(m, least_prime);
        std::cout << "example " << n << '=' << fn.expanded << ", " << m << '=' << fm.expanded
                  << "; phi " << phi[n] << ',' << phi[m] << "; sigma " << fn.sigma << ','
                  << fm.sigma << '\n';
    }
}
