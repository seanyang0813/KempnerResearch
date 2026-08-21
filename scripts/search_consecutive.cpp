#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <string>
#include <tuple>
#include <vector>

struct Metrics {
  std::uint32_t s = 1;
  std::uint32_t largest_prime = 1;
  std::uint32_t max_exponent = 0;
};

static std::uint64_t valuation_factorial(std::uint64_t m, std::uint64_t p) {
  std::uint64_t result = 0;
  while (m != 0) {
    m /= p;
    result += m;
  }
  return result;
}

static std::uint32_t kempner_prime_power(std::uint32_t p, std::uint32_t a) {
  std::uint64_t lo = 1;
  std::uint64_t hi = static_cast<std::uint64_t>(p) * a;
  while (lo < hi) {
    const std::uint64_t mid = lo + (hi - lo) / 2;
    if (valuation_factorial(mid, p) >= a) {
      hi = mid;
    } else {
      lo = mid + 1;
    }
  }
  return static_cast<std::uint32_t>(lo);
}

static Metrics metrics(std::uint32_t n, const std::vector<std::uint32_t>& spf) {
  Metrics out;
  while (n > 1) {
    const std::uint32_t p = spf[n];
    std::uint32_t a = 0;
    do {
      n /= p;
      ++a;
    } while (n > 1 && spf[n] == p);
    out.s = std::max(out.s, kempner_prime_power(p, a));
    out.largest_prime = std::max(out.largest_prime, p);
    out.max_exponent = std::max(out.max_exponent, a);
  }
  return out;
}

int main(int argc, char** argv) {
  std::uint32_t limit = 20'000'000;
  if (argc == 3 && std::string(argv[1]) == "--limit") {
    const unsigned long parsed = std::strtoul(argv[2], nullptr, 10);
    if (parsed < 2 || parsed > std::numeric_limits<std::uint32_t>::max() - 1) {
      std::cerr << "limit must lie in [2, 2^32-2]\n";
      return 2;
    }
    limit = static_cast<std::uint32_t>(parsed);
  } else if (argc != 1) {
    std::cerr << "usage: search_consecutive [--limit N]\n";
    return 2;
  }

  std::vector<std::uint32_t> spf(static_cast<std::size_t>(limit) + 2);
  for (std::uint32_t i = 0; i <= limit + 1; ++i) spf[i] = i;
  for (std::uint32_t i = 2; static_cast<std::uint64_t>(i) * i <= limit + 1; ++i) {
    if (spf[i] != i) continue;
    for (std::uint64_t j = static_cast<std::uint64_t>(i) * i; j <= limit + 1; j += i) {
      if (spf[j] == j) spf[j] = i;
    }
  }

  std::uint64_t equalities = 0;
  std::uint64_t obstruction_survivors = 0;
  std::vector<std::tuple<std::uint32_t, Metrics, Metrics>> first_survivors;
  Metrics left = metrics(1, spf);
  for (std::uint32_t n = 1; n <= limit; ++n) {
    const Metrics right = metrics(n + 1, spf);
    if (left.s == right.s) {
      ++equalities;
      std::cout << "EQUALITY n=" << n << " S=" << left.s << '\n';
    }
    const std::uint64_t A = left.max_exponent;
    const std::uint64_t B = right.max_exponent;
    const std::uint64_t sharp_bound = A * B - std::min(A, B);
    if (std::max(left.largest_prime, right.largest_prime) <= sharp_bound) {
      ++obstruction_survivors;
      if (first_survivors.size() < 32) first_survivors.emplace_back(n, left, right);
    }
    left = right;
  }

  std::cout << "limit=" << limit << '\n';
  std::cout << "tutescu_equalities=" << equalities << '\n';
  std::cout << "sharp_obstruction_survivors=" << obstruction_survivors << '\n';
  std::cout << "first_survivors:";
  for (const auto& [n, x, y] : first_survivors) {
    std::cout << ' ' << n << "[P=" << x.largest_prime << ',' << y.largest_prime
              << ";E=" << x.max_exponent << ',' << y.max_exponent
              << ";S=" << x.s << ',' << y.s << ']';
  }
  std::cout << '\n';
  return equalities == 0 ? 0 : 1;
}
