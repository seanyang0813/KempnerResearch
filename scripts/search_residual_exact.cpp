// Exact residual-pair search for consecutive Kempner fibers.
//
// Let M > 1 and F = (M-1)!.  If S(n) = S(n+1) = M, define the exact
// last-step residuals
//
//   r = n     / gcd(n, F),
//   s = (n+1) / gcd(n+1, F).
//
// Then r,s > 1, gcd(r,s)=1, rs | M, and there are A,B,L with
//
//   n=rA, n+1=sB, ABL=F, sB-rA=1.
//
// For every p|r, A contains exactly v_p(F) copies of p; for every p|s,
// B contains exactly v_p(F) copies.  All remaining prime powers of F are
// assigned to A, B, or L, and A and B have disjoint support.  Conversely,
// these conditions produce a common Kempner fiber at M.  This program
// enumerates residual pairs exactly and searches the remaining finite
// allocation problem by a compact modular meet in the middle.
//
// A search reported complete=true has enumerated every divisor allocation
// in its explicitly printed domain.  --force-single-prime=P is a domain
// restriction, not a theorem: it searches the two cases where P (whose
// exponent in F must be one) occurs on exactly one neighbor.  At M=130,
// P=127 is justified only after importing the external complete B=113
// smooth-neighbor certificate.

#include <algorithm>
#include <bit>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <optional>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using u64 = std::uint64_t;
using u128 = unsigned __int128;
using i128 = __int128;

namespace {

// A deliberately small unsigned big integer.  Search arithmetic is modulo a
// 64-bit sieve; this class is used only to reconstruct and verify the rare
// sieve matches.  Base 2^32 schoolbook operations are ample for factorials in
// the intended exact-value range and avoid a nonstandard build dependency.
class BigNat {
  public:
    BigNat() = default;
    BigNat(u64 value) {
        if (value) limbs_.push_back(static_cast<std::uint32_t>(value));
        if (value >> 32U) limbs_.push_back(static_cast<std::uint32_t>(value >> 32U));
    }

    bool is_zero() const { return limbs_.empty(); }

    friend bool operator==(const BigNat& a, const BigNat& b) {
        return a.limbs_ == b.limbs_;
    }
    friend bool operator!=(const BigNat& a, const BigNat& b) { return !(a == b); }
    friend bool operator<(const BigNat& a, const BigNat& b) {
        if (a.limbs_.size() != b.limbs_.size()) return a.limbs_.size() < b.limbs_.size();
        for (std::size_t i = a.limbs_.size(); i > 0; --i) {
            if (a.limbs_[i - 1] != b.limbs_[i - 1]) {
                return a.limbs_[i - 1] < b.limbs_[i - 1];
            }
        }
        return false;
    }
    friend bool operator>=(const BigNat& a, const BigNat& b) { return !(a < b); }

    BigNat& operator+=(u64 addend) {
        u128 carry = addend;
        std::size_t i = 0;
        while (carry) {
            if (i == limbs_.size()) limbs_.push_back(0);
            const u128 current = static_cast<u128>(limbs_[i])
                               + static_cast<std::uint32_t>(carry);
            limbs_[i] = static_cast<std::uint32_t>(current);
            carry = (carry >> 32U) + (current >> 32U);
            ++i;
        }
        return *this;
    }

    BigNat& operator*=(u64 factor) {
        if (factor == 0 || is_zero()) {
            limbs_.clear();
            return *this;
        }
        u128 carry = 0;
        for (auto& limb : limbs_) {
            const u128 current = static_cast<u128>(limb) * factor + carry;
            limb = static_cast<std::uint32_t>(current);
            carry = current >> 32U;
        }
        while (carry) {
            limbs_.push_back(static_cast<std::uint32_t>(carry));
            carry >>= 32U;
        }
        return *this;
    }

    BigNat& operator*=(const BigNat& factor) {
        if (is_zero() || factor.is_zero()) {
            limbs_.clear();
            return *this;
        }
        std::vector<std::uint32_t> product(limbs_.size() + factor.limbs_.size() + 1, 0);
        for (std::size_t i = 0; i < limbs_.size(); ++i) {
            u128 carry = 0;
            for (std::size_t j = 0; j < factor.limbs_.size(); ++j) {
                const std::size_t k = i + j;
                const u128 current = static_cast<u128>(product[k])
                                   + static_cast<u128>(limbs_[i]) * factor.limbs_[j]
                                   + carry;
                product[k] = static_cast<std::uint32_t>(current);
                carry = current >> 32U;
            }
            std::size_t k = i + factor.limbs_.size();
            while (carry) {
                const u128 current = static_cast<u128>(product[k])
                                   + static_cast<std::uint32_t>(carry);
                product[k] = static_cast<std::uint32_t>(current);
                carry = (carry >> 32U) + (current >> 32U);
                ++k;
            }
        }
        limbs_ = std::move(product);
        trim();
        return *this;
    }

    BigNat& operator/=(u64 divisor) {
        if (!divisor) throw std::domain_error("division by zero");
        u128 remainder = 0;
        for (std::size_t i = limbs_.size(); i > 0; --i) {
            const u128 current = (remainder << 32U) | limbs_[i - 1];
            limbs_[i - 1] = static_cast<std::uint32_t>(current / divisor);
            remainder = current % divisor;
        }
        trim();
        return *this;
    }

    u64 mod_small(u64 divisor) const {
        if (!divisor) throw std::domain_error("modulo by zero");
        u128 remainder = 0;
        for (std::size_t i = limbs_.size(); i > 0; --i) {
            remainder = ((remainder << 32U) | limbs_[i - 1]) % divisor;
        }
        return static_cast<u64>(remainder);
    }

    u64 divide_small(u64 divisor) {
        const u64 remainder = mod_small(divisor);
        *this /= divisor;
        return remainder;
    }

    std::size_t bit_length() const {
        if (is_zero()) return 0;
        return 32U * (limbs_.size() - 1)
             + (32U - std::countl_zero(limbs_.back()));
    }

    bool bit(std::size_t index) const {
        const std::size_t limb = index / 32U;
        return limb < limbs_.size() && ((limbs_[limb] >> (index % 32U)) & 1U);
    }

    void set_bit(std::size_t index) {
        const std::size_t limb = index / 32U;
        if (limbs_.size() <= limb) limbs_.resize(limb + 1, 0);
        limbs_[limb] |= std::uint32_t{1} << (index % 32U);
    }

    void shift_left_one() {
        u64 carry = 0;
        for (auto& limb : limbs_) {
            const u64 current = (static_cast<u64>(limb) << 1U) | carry;
            limb = static_cast<std::uint32_t>(current);
            carry = current >> 32U;
        }
        if (carry) limbs_.push_back(static_cast<std::uint32_t>(carry));
    }

    void subtract(const BigNat& other) {
        if (*this < other) throw std::logic_error("negative BigNat subtraction");
        u64 borrow = 0;
        for (std::size_t i = 0; i < limbs_.size(); ++i) {
            const u64 subtrahend = (i < other.limbs_.size() ? other.limbs_[i] : 0) + borrow;
            const u64 current = limbs_[i];
            limbs_[i] = static_cast<std::uint32_t>(current - subtrahend);
            borrow = current < subtrahend;
        }
        if (borrow) throw std::logic_error("BigNat borrow escaped");
        trim();
    }

    static std::pair<BigNat, BigNat> divmod(const BigNat& numerator,
                                             const BigNat& denominator) {
        if (denominator.is_zero()) throw std::domain_error("division by zero");
        BigNat quotient;
        BigNat remainder;
        for (std::size_t i = numerator.bit_length(); i > 0; --i) {
            remainder.shift_left_one();
            if (numerator.bit(i - 1)) remainder += 1;
            if (remainder >= denominator) {
                remainder.subtract(denominator);
                quotient.set_bit(i - 1);
            }
        }
        return {quotient, remainder};
    }

    std::string str() const {
        if (is_zero()) return "0";
        BigNat copy = *this;
        std::vector<std::uint32_t> chunks;
        while (!copy.is_zero()) {
            chunks.push_back(static_cast<std::uint32_t>(copy.divide_small(1'000'000'000)));
        }
        std::string result = std::to_string(chunks.back());
        for (std::size_t i = chunks.size() - 1; i > 0; --i) {
            const std::string chunk = std::to_string(chunks[i - 1]);
            result.append(9 - chunk.size(), '0');
            result += chunk;
        }
        return result;
    }

    friend BigNat operator*(BigNat left, const BigNat& right) { left *= right; return left; }
    friend BigNat operator*(BigNat left, u64 right) { left *= right; return left; }
    friend BigNat operator+(BigNat left, u64 right) { left += right; return left; }
    friend BigNat operator/(const BigNat& left, const BigNat& right) {
        return divmod(left, right).first;
    }
    friend BigNat operator%(const BigNat& left, const BigNat& right) {
        return divmod(left, right).second;
    }
    friend u64 operator%(const BigNat& left, u64 right) { return left.mod_small(right); }
    friend std::ostream& operator<<(std::ostream& out, const BigNat& value) {
        return out << value.str();
    }

  private:
    void trim() {
        while (!limbs_.empty() && limbs_.back() == 0) limbs_.pop_back();
    }
    std::vector<std::uint32_t> limbs_;
};

using cpp_int = BigNat;

struct PrimePower {
    u64 prime;
    unsigned exponent;
};

struct ResidualPair {
    u64 left;
    u64 right;
};

struct Options {
    unsigned value = 130;
    u64 force_single_prime = 0;
    bool full_residual_support = false;
    bool dry_run = false;
    bool self_test = false;
    u64 max_table_entries = 100'000'000;
    std::optional<ResidualPair> only_pair;
};

u64 checked_mul(u64 a, u64 b, const char* context) {
    if (a != 0 && b > std::numeric_limits<u64>::max() / a) {
        throw std::overflow_error(context);
    }
    return a * b;
}

cpp_int pow_big(u64 base, unsigned exponent) {
    cpp_int result = 1;
    cpp_int factor = base;
    while (exponent) {
        if (exponent & 1U) result *= factor;
        exponent >>= 1U;
        if (exponent) factor *= factor;
    }
    return result;
}

u64 mul_mod(u64 a, u64 b, u64 modulus) {
    return static_cast<u64>((static_cast<u128>(a) * b) % modulus);
}

u64 pow_mod(u64 base, unsigned exponent, u64 modulus) {
    u64 result = 1 % modulus;
    while (exponent) {
        if (exponent & 1U) result = mul_mod(result, base, modulus);
        exponent >>= 1U;
        if (exponent) base = mul_mod(base, base, modulus);
    }
    return result;
}

u64 inverse_mod(u64 value, u64 modulus) {
    i128 old_r = value;
    i128 r = modulus;
    i128 old_s = 1;
    i128 s = 0;
    while (r != 0) {
        const i128 quotient = old_r / r;
        const i128 next_r = old_r - quotient * r;
        old_r = r;
        r = next_r;
        const i128 next_s = old_s - quotient * s;
        old_s = s;
        s = next_s;
    }
    if (old_r != 1) throw std::logic_error("nonunit in modular inverse");
    old_s %= static_cast<i128>(modulus);
    if (old_s < 0) old_s += modulus;
    return static_cast<u64>(old_s);
}

u64 splitmix64(u64 value) {
    value += 0x9e3779b97f4a7c15ULL;
    value = (value ^ (value >> 30U)) * 0xbf58476d1ce4e5b9ULL;
    value = (value ^ (value >> 27U)) * 0x94d049bb133111ebULL;
    return value ^ (value >> 31U);
}

std::vector<unsigned> primes_through(unsigned limit) {
    std::vector<bool> prime(limit + 1, true);
    prime[0] = false;
    if (limit >= 1) prime[1] = false;
    for (unsigned p = 2; static_cast<u64>(p) * p <= limit; ++p) {
        if (!prime[p]) continue;
        for (unsigned multiple = p * p; multiple <= limit; multiple += p) {
            prime[multiple] = false;
        }
    }
    std::vector<unsigned> result;
    for (unsigned p = 2; p <= limit; ++p) if (prime[p]) result.push_back(p);
    return result;
}

unsigned valuation_factorial(unsigned n, unsigned p) {
    unsigned result = 0;
    while (n) {
        n /= p;
        result += n;
    }
    return result;
}

std::vector<PrimePower> factor_small(unsigned value,
                                     const std::vector<unsigned>& primes) {
    std::vector<PrimePower> factors;
    unsigned remainder = value;
    for (unsigned p : primes) {
        if (static_cast<u64>(p) * p > remainder) break;
        if (remainder % p) continue;
        unsigned exponent = 0;
        do {
            remainder /= p;
            ++exponent;
        } while (remainder % p == 0);
        factors.push_back({p, exponent});
    }
    if (remainder > 1) factors.push_back({remainder, 1});
    return factors;
}

unsigned valuation(u64 value, u64 prime) {
    unsigned exponent = 0;
    while (value % prime == 0) {
        value /= prime;
        ++exponent;
    }
    return exponent;
}

bool support_contains(u64 value, u64 prime) {
    return value % prime == 0;
}

void enumerate_residual_pairs_rec(
    const std::vector<PrimePower>& factors,
    std::size_t index,
    u64 left,
    u64 right,
    bool full_support,
    std::vector<ResidualPair>& output) {
    if (index == factors.size()) {
        if (left > 1 && right > 1) output.push_back({left, right});
        return;
    }
    const auto [prime, exponent] = factors[index];
    if (!full_support) {
        enumerate_residual_pairs_rec(
            factors, index + 1, left, right, full_support, output);
    }
    u64 power = 1;
    for (unsigned e = 1; e <= exponent; ++e) {
        power = checked_mul(power, prime, "residual overflow");
        enumerate_residual_pairs_rec(
            factors, index + 1, checked_mul(left, power, "residual overflow"),
            right, full_support, output);
        enumerate_residual_pairs_rec(
            factors, index + 1, left,
            checked_mul(right, power, "residual overflow"), full_support,
            output);
    }
}

bool is_c_ge_two_pair(unsigned value,
                      const std::vector<PrimePower>& value_factors,
                      const ResidualPair& residual) {
    for (const auto& p : value_factors) {
        if (!support_contains(residual.left, p.prime)) continue;
        for (const auto& q : value_factors) {
            if (!support_contains(residual.right, q.prime)) continue;
            if (value / (p.prime * q.prime) >= 2) return true;
        }
    }
    return false;
}

u64 divisor_count(const std::vector<PrimePower>& items) {
    u64 result = 1;
    for (const auto& item : items) {
        result = checked_mul(result, item.exponent + 1,
                             "divisor-count overflow");
    }
    return result;
}

std::pair<std::vector<PrimePower>, std::vector<PrimePower>> split_items(
    const std::vector<PrimePower>& items) {
    std::vector<PrimePower> ordered = items;
    std::stable_sort(ordered.begin(), ordered.end(), [](const auto& a, const auto& b) {
        return a.exponent > b.exponent;
    });
    std::vector<PrimePower> left;
    std::vector<PrimePower> right;
    long double left_weight = 0;
    long double right_weight = 0;
    for (const auto& item : ordered) {
        const long double weight = std::log(static_cast<long double>(item.exponent + 1));
        if (left_weight <= right_weight) {
            left.push_back(item);
            left_weight += weight;
        } else {
            right.push_back(item);
            right_weight += weight;
        }
    }
    return {left, right};
}

// Iterate all mixed-radix exponent vectors.  The callback receives the unique
// mixed-radix code, the represented product modulo modulus, and its inverse.
template <class Callback>
void enumerate_residues(const std::vector<PrimePower>& items,
                        u64 modulus,
                        Callback&& callback) {
    struct State {
        unsigned digit;
        unsigned cap;
        u64 prime;
        u64 prime_inverse;
        u64 reset_product;
        u64 reset_inverse;
    };
    std::vector<State> states;
    states.reserve(items.size());
    for (const auto& item : items) {
        const u64 prime = item.prime % modulus;
        const u64 prime_inverse = inverse_mod(prime, modulus);
        states.push_back({
            0,
            item.exponent,
            prime,
            prime_inverse,
            pow_mod(prime_inverse, item.exponent, modulus),
            pow_mod(prime, item.exponent, modulus),
        });
    }

    const u64 count = divisor_count(items);
    u64 residue = 1 % modulus;
    u64 inverse = 1 % modulus;
    callback(0, residue, inverse);
    for (u64 code = 1; code < count; ++code) {
        std::size_t index = states.size();
        while (index > 0) {
            --index;
            auto& state = states[index];
            if (state.digit < state.cap) {
                ++state.digit;
                residue = mul_mod(residue, state.prime, modulus);
                inverse = mul_mod(inverse, state.prime_inverse, modulus);
                break;
            }
            state.digit = 0;
            residue = mul_mod(residue, state.reset_product, modulus);
            inverse = mul_mod(inverse, state.reset_inverse, modulus);
        }
        callback(code, residue, inverse);
    }
}

std::vector<unsigned> decode_exponents(const std::vector<PrimePower>& items,
                                       u64 code) {
    std::vector<unsigned> exponents(items.size());
    for (std::size_t reverse = items.size(); reverse > 0; --reverse) {
        const std::size_t index = reverse - 1;
        const u64 radix = items[index].exponent + 1;
        exponents[index] = static_cast<unsigned>(code % radix);
        code /= radix;
    }
    if (code != 0) throw std::logic_error("mixed-radix decode overflow");
    return exponents;
}

u64 residue_from_code(const std::vector<PrimePower>& items,
                      u64 code,
                      u64 modulus) {
    const auto exponents = decode_exponents(items, code);
    u64 result = 1 % modulus;
    for (std::size_t i = 0; i < items.size(); ++i) {
        result = mul_mod(result,
                         pow_mod(items[i].prime % modulus, exponents[i], modulus),
                         modulus);
    }
    return result;
}

cpp_int big_from_code(const std::vector<PrimePower>& items, u64 code) {
    const auto exponents = decode_exponents(items, code);
    cpp_int result = 1;
    for (std::size_t i = 0; i < items.size(); ++i) {
        result *= pow_big(items[i].prime, exponents[i]);
    }
    return result;
}

std::vector<unsigned> combined_exponents(
    const std::vector<PrimePower>& first,
    u64 first_code,
    const std::vector<PrimePower>& second,
    u64 second_code,
    const std::vector<PrimePower>& all_items) {
    const auto first_exponents = decode_exponents(first, first_code);
    const auto second_exponents = decode_exponents(second, second_code);
    std::vector<unsigned> result(all_items.size(), 0);
    for (std::size_t i = 0; i < all_items.size(); ++i) {
        for (std::size_t j = 0; j < first.size(); ++j) {
            if (first[j].prime == all_items[i].prime) result[i] = first_exponents[j];
        }
        for (std::size_t j = 0; j < second.size(); ++j) {
            if (second[j].prime == all_items[i].prime) result[i] = second_exponents[j];
        }
    }
    return result;
}

class CompactResidueTable {
  public:
    CompactResidueTable(u64 entries,
                        const std::vector<PrimePower>& indexed_items,
                        u64 modulus)
        : entries_(entries), items_(indexed_items), modulus_(modulus) {
        if (entries_ >= std::numeric_limits<std::uint32_t>::max()) {
            throw std::overflow_error("too many table entries for compact code");
        }
        u64 wanted = entries_ + entries_ / 2 + 1; // load <= 2/3
        capacity_ = 1;
        while (capacity_ < wanted) {
            if (capacity_ > (u64{1} << 62)) throw std::overflow_error("hash capacity");
            capacity_ <<= 1U;
        }
        codes_.assign(capacity_, 0);
        fingerprints_.assign(capacity_, 0);
        position_mask_ = capacity_ - 1;
    }

    u64 capacity() const { return capacity_; }

    void insert(u64 residue, u64 code) {
        const u64 hash = splitmix64(residue);
        u64 position = hash & position_mask_;
        while (codes_[position] != 0) position = (position + 1) & position_mask_;
        codes_[position] = static_cast<std::uint32_t>(code + 1);
        fingerprints_[position] = static_cast<std::uint16_t>(hash >> 48U);
    }

    template <class Callback>
    void for_each_match(u64 residue, Callback&& callback) const {
        const u64 hash = splitmix64(residue);
        const auto fingerprint = static_cast<std::uint16_t>(hash >> 48U);
        u64 position = hash & position_mask_;
        while (codes_[position] != 0) {
            if (fingerprints_[position] == fingerprint) {
                const u64 code = static_cast<u64>(codes_[position]) - 1;
                if (residue_from_code(items_, code, modulus_) == residue) {
                    callback(code);
                }
            }
            position = (position + 1) & position_mask_;
        }
    }

  private:
    u64 entries_;
    const std::vector<PrimePower>& items_;
    u64 modulus_;
    u64 capacity_ = 0;
    u64 position_mask_ = 0;
    std::vector<std::uint32_t> codes_;
    std::vector<std::uint16_t> fingerprints_;
};

cpp_int factorial(unsigned n) {
    cpp_int result = 1;
    for (unsigned k = 2; k <= n; ++k) result *= k;
    return result;
}

std::vector<PrimePower> core_factorization(
    u64 residual,
    const std::vector<PrimePower>& value_factors,
    const std::vector<PrimePower>& previous_caps) {
    std::vector<PrimePower> result;
    for (const auto& factor : value_factors) {
        const unsigned delta = valuation(residual, factor.prime);
        if (!delta) continue;
        unsigned previous = 0;
        for (const auto& cap : previous_caps) {
            if (cap.prime == factor.prime) {
                previous = cap.exponent;
                break;
            }
        }
        result.push_back({factor.prime, previous + delta});
    }
    return result;
}

cpp_int factorization_value(const std::vector<PrimePower>& factors) {
    cpp_int result = 1;
    for (const auto& factor : factors) result *= pow_big(factor.prime, factor.exponent);
    return result;
}

u64 largest_u64_divisor(const std::vector<PrimePower>& factors) {
    // Greedily take prime factors while staying at or below 2^63.  Maximality is
    // unnecessary: every returned value divides the exact right core.
    constexpr u64 limit = u64{1} << 63U;
    u64 result = 1;
    bool progress = true;
    while (progress) {
        progress = false;
        for (const auto& factor : factors) {
            unsigned already = valuation(result, factor.prime);
            if (already >= factor.exponent) continue;
            if (result <= limit / factor.prime) {
                result *= factor.prime;
                progress = true;
            }
        }
    }
    return result;
}

struct BranchStats {
    u64 sieve_matches = 0;
    u64 full_congruence_matches = 0;
    u64 exact_smooth_matches = 0;
};

bool divides(const cpp_int& divisor, const cpp_int& value) {
    return value % divisor == 0;
}

bool check_exact_candidate(
    const cpp_int& small_core,
    const cpp_int& large_core,
    bool small_core_on_n,
    const std::vector<PrimePower>& free_items,
    const std::vector<PrimePower>& table_items,
    u64 table_code,
    const std::vector<PrimePower>& probe_items,
    u64 probe_code,
    const cpp_int& previous_factorial,
    const cpp_int& current_factorial,
    BranchStats& stats,
    bool emit_candidate = true) {
    const cpp_int z = big_from_code(table_items, table_code)
                    * big_from_code(probe_items, probe_code);
    const cpp_int small_value = small_core * z;
    cpp_int numerator = small_value;
    if (small_core_on_n) {
        numerator += 1;
    } else {
        if (numerator == 0) return false;
        numerator.subtract(cpp_int(1));
    }
    if (numerator % large_core != 0) return false;
    ++stats.full_congruence_matches;
    cpp_int w = numerator / large_core;

    const auto z_exponents = combined_exponents(
        table_items, table_code, probe_items, probe_code, free_items);
    cpp_int remainder = w;
    for (std::size_t i = 0; i < free_items.size(); ++i) {
        unsigned exponent = 0;
        const u64 prime = free_items[i].prime;
        while (remainder % prime == 0) {
            remainder /= prime;
            ++exponent;
            if (exponent > free_items[i].exponent) return false;
        }
        if (exponent && z_exponents[i]) return false;
    }
    if (remainder != 1) return false;

    const cpp_int n = small_core_on_n ? small_value : large_core * w;
    const cpp_int n_plus_one = small_core_on_n ? large_core * w : small_value;
    if (n_plus_one != n + 1) throw std::logic_error("adjacency reconstruction");
    if (!divides(n, current_factorial) || !divides(n_plus_one, current_factorial)) {
        throw std::logic_error("candidate does not divide M!");
    }
    if (divides(n, previous_factorial) || divides(n_plus_one, previous_factorial)) {
        throw std::logic_error("candidate enters before M");
    }
    if (!divides(n * n_plus_one, current_factorial)) {
        throw std::logic_error("candidate product does not divide M!");
    }
    ++stats.exact_smooth_matches;
    if (emit_candidate) {
        std::cout << "candidate.n=" << n << "\n";
        std::cout << "candidate.n_plus_one=" << n_plus_one << "\n";
    }
    return true;
}

void search_group(
    const Options& options,
    const ResidualPair& residual_group,
    const std::vector<PrimePower>& value_factors,
    const std::vector<PrimePower>& previous_caps,
    const cpp_int& previous_factorial,
    const cpp_int& current_factorial,
    bool& global_complete,
    u64& total_candidates) {
    auto first_core_factors = core_factorization(
        residual_group.left, value_factors, previous_caps);
    auto second_core_factors = core_factorization(
        residual_group.right, value_factors, previous_caps);
    cpp_int first_core = factorization_value(first_core_factors);
    cpp_int second_core = factorization_value(second_core_factors);
    u64 small_residual = residual_group.left;
    u64 large_residual = residual_group.right;
    std::vector<PrimePower> small_core_factors = first_core_factors;
    std::vector<PrimePower> large_core_factors = second_core_factors;
    cpp_int base_small_core = first_core;
    cpp_int base_large_core = second_core;
    if (base_large_core < base_small_core) {
        std::swap(small_residual, large_residual);
        std::swap(small_core_factors, large_core_factors);
        std::swap(base_small_core, base_large_core);
    }

    std::vector<PrimePower> free_items;
    for (const auto& cap : previous_caps) {
        if (support_contains(residual_group.left, cap.prime)
            || support_contains(residual_group.right, cap.prime)) continue;
        if (cap.prime == options.force_single_prime) continue;
        free_items.push_back(cap);
    }

    auto [first_half, second_half] = split_items(free_items);
    u64 first_count = divisor_count(first_half);
    u64 second_count = divisor_count(second_half);
    std::vector<PrimePower> table_items = first_half;
    std::vector<PrimePower> probe_items = second_half;
    u64 table_count = first_count;
    u64 probe_count = second_count;
    if (table_count > probe_count) {
        std::swap(table_items, probe_items);
        std::swap(table_count, probe_count);
    }

    const u64 sieve_modulus = largest_u64_divisor(large_core_factors);
    if (sieve_modulus <= 1) throw std::logic_error("trivial sieve modulus");

    std::cout << "group.begin residuals=" << residual_group.left << ","
              << residual_group.right
              << " small_residual=" << small_residual
              << " large_residual=" << large_residual
              << " free_divisors=" << divisor_count(free_items)
              << " table_entries=" << table_count
              << " probe_entries=" << probe_count
              << " sieve_modulus=" << sieve_modulus << "\n";

    if (options.dry_run || table_count > options.max_table_entries) {
        global_complete = false;
        std::cout << "group.skipped reason="
                  << (options.dry_run ? "dry_run" : "table_entry_limit") << "\n";
        return;
    }

    CompactResidueTable table(table_count, table_items, sieve_modulus);
    std::cout << "group.hash_capacity=" << table.capacity() << "\n";
    enumerate_residues(table_items, sieve_modulus,
        [&](u64 code, u64 residue, u64) { table.insert(residue, code); });

    struct OrientationBranch {
        const char* name;
        cpp_int small_core;
        cpp_int large_core;
        bool small_core_on_n;
        u64 target;
        BranchStats stats;
    };
    std::vector<OrientationBranch> branches;
    auto signed_target = [&](const cpp_int& small_core, bool positive) {
        const u64 inverse = inverse_mod(small_core % sieve_modulus,
                                        sieve_modulus);
        return positive ? inverse : (sieve_modulus - inverse) % sieve_modulus;
    };
    if (options.force_single_prime) {
        const cpp_int forced = options.force_single_prime;
        const cpp_int forced_small = base_small_core * forced;
        const cpp_int forced_large = base_large_core * forced;
        branches.push_back({"small_on_n_forced_small", forced_small,
                            base_large_core, true,
                            signed_target(forced_small, false), {}});
        branches.push_back({"small_on_n_forced_large", base_small_core,
                            forced_large, true,
                            signed_target(base_small_core, false), {}});
        branches.push_back({"large_on_n_forced_small", forced_small,
                            base_large_core, false,
                            signed_target(forced_small, true), {}});
        branches.push_back({"large_on_n_forced_large", base_small_core,
                            forced_large, false,
                            signed_target(base_small_core, true), {}});
    } else {
        branches.push_back({"small_on_n", base_small_core, base_large_core,
                            true, signed_target(base_small_core, false), {}});
        branches.push_back({"large_on_n", base_small_core, base_large_core,
                            false, signed_target(base_small_core, true), {}});
    }

    enumerate_residues(probe_items, sieve_modulus,
        [&](u64 probe_code, u64, u64 probe_inverse) {
            for (auto& branch : branches) {
                const u64 required = mul_mod(branch.target, probe_inverse,
                                             sieve_modulus);
                table.for_each_match(required, [&](u64 table_code) {
                    ++branch.stats.sieve_matches;
                    check_exact_candidate(
                        branch.small_core, branch.large_core,
                        branch.small_core_on_n, free_items,
                        table_items, table_code, probe_items, probe_code,
                        previous_factorial, current_factorial, branch.stats);
                });
            }
        });

    for (const auto& branch : branches) {
        total_candidates += branch.stats.exact_smooth_matches;
        std::cout << "group.branch name=" << branch.name
                  << " sieve_matches=" << branch.stats.sieve_matches
                  << " full_congruence_matches="
                  << branch.stats.full_congruence_matches
                  << " exact_smooth_matches="
                  << branch.stats.exact_smooth_matches << "\n";
    }
    std::cout << "group.end residuals=" << residual_group.left << ","
              << residual_group.right << "\n";
}

void require_test(bool condition, const char* message) {
    if (!condition) throw std::logic_error(std::string("self-test failed: ") + message);
}

void run_self_tests() {
    cpp_int two_to_128 = 1;
    for (unsigned i = 0; i < 128; ++i) two_to_128 *= 2;
    require_test(two_to_128.str() == "340282366920938463463374607431768211456",
                 "BigNat power/decimal conversion");
    cpp_int three_to_80 = 1;
    for (unsigned i = 0; i < 80; ++i) three_to_80 *= 3;
    const cpp_int product = two_to_128 * three_to_80;
    const auto [quotient, remainder] = cpp_int::divmod(product, two_to_128);
    require_test(remainder == 0 && quotient == three_to_80,
                 "BigNat multiplication/division");
    require_test(factorial(10).str() == "3628800", "BigNat factorial");

    const std::vector<PrimePower> enumeration_items{{2, 3}, {3, 2}, {5, 1}};
    u64 enumerated = 0;
    enumerate_residues(enumeration_items, 49,
        [&](u64 code, u64 residue, u64 inverse) {
            require_test(code == enumerated, "mixed-radix code order");
            require_test(residue == residue_from_code(enumeration_items, code, 49),
                         "mixed-radix residue");
            require_test(mul_mod(residue, inverse, 49) == 1,
                         "incremental modular inverse");
            ++enumerated;
        });
    require_test(enumerated == divisor_count(enumeration_items),
                 "mixed-radix enumeration count");

    const std::vector<PrimePower> table_items{{2, 3}, {3, 2}};
    CompactResidueTable duplicate_table(divisor_count(table_items), table_items, 25);
    enumerate_residues(table_items, 25,
        [&](u64 code, u64 residue, u64) { duplicate_table.insert(residue, code); });
    for (u64 residue = 0; residue < 25; ++residue) {
        std::vector<u64> expected;
        std::vector<u64> actual;
        for (u64 code = 0; code < divisor_count(table_items); ++code) {
            if (residue_from_code(table_items, code, 25) == residue) {
                expected.push_back(code);
            }
        }
        duplicate_table.for_each_match(residue,
            [&](u64 code) { actual.push_back(code); });
        std::sort(expected.begin(), expected.end());
        std::sort(actual.begin(), actual.end());
        require_test(actual == expected, "duplicate-preserving residue table");
    }

    const std::vector<PrimePower> join_left{{2, 3}, {5, 1}};
    const std::vector<PrimePower> join_right{{3, 2}, {7, 1}};
    constexpr u64 join_modulus = 121;
    const std::vector<u64> targets{1, 17, 120};
    CompactResidueTable join_table(divisor_count(join_left), join_left,
                                   join_modulus);
    enumerate_residues(join_left, join_modulus,
        [&](u64 code, u64 residue, u64) { join_table.insert(residue, code); });
    std::vector<std::tuple<u64, u64, u64>> actual_join;
    enumerate_residues(join_right, join_modulus,
        [&](u64 right_code, u64, u64 right_inverse) {
            for (u64 target : targets) {
                const u64 required = mul_mod(target, right_inverse, join_modulus);
                join_table.for_each_match(required, [&](u64 left_code) {
                    actual_join.emplace_back(target, left_code, right_code);
                });
            }
        });
    std::vector<std::tuple<u64, u64, u64>> expected_join;
    for (u64 left_code = 0; left_code < divisor_count(join_left); ++left_code) {
        const u64 left_residue = residue_from_code(join_left, left_code, join_modulus);
        for (u64 right_code = 0; right_code < divisor_count(join_right); ++right_code) {
            const u64 right_residue = residue_from_code(join_right, right_code,
                                                        join_modulus);
            for (u64 target : targets) {
                if (mul_mod(left_residue, right_residue, join_modulus) == target) {
                    expected_join.emplace_back(target, left_code, right_code);
                }
            }
        }
    }
    std::sort(actual_join.begin(), actual_join.end());
    std::sort(expected_join.begin(), expected_join.end());
    require_test(actual_join == expected_join, "MITM join versus naive product scan");

    const std::vector<PrimePower> no_items;
    BranchStats positive_stats;
    require_test(check_exact_candidate(2, 3, true, no_items, no_items, 0,
                                       no_items, 0, 1, 6, positive_stats, false),
                 "exact checker plus-one orientation");
    BranchStats negative_stats;
    require_test(check_exact_candidate(4, 3, false, no_items, no_items, 0,
                                       no_items, 0, 1, 12, negative_stats, false),
                 "exact checker minus-one orientation");
    require_test(positive_stats.exact_smooth_matches == 1
                 && negative_stats.exact_smooth_matches == 1,
                 "exact checker acceptance counters");

    std::cout << "self_test=passed\n";
}

u64 parse_u64(const std::string& text, const char* option) {
    std::size_t consumed = 0;
    const unsigned long long value = std::stoull(text, &consumed);
    if (consumed != text.size()) throw std::invalid_argument(option);
    return static_cast<u64>(value);
}

Options parse_options(int argc, char** argv) {
    Options options;
    for (int i = 1; i < argc; ++i) {
        const std::string argument = argv[i];
        auto need = [&](const char* name) -> std::string {
            if (++i >= argc) throw std::invalid_argument(std::string("missing ") + name);
            return argv[i];
        };
        if (argument == "--value") {
            options.value = static_cast<unsigned>(parse_u64(need("--value"), "--value"));
        } else if (argument == "--force-single-prime") {
            options.force_single_prime = parse_u64(
                need("--force-single-prime"), "--force-single-prime");
        } else if (argument == "--full-residual-support") {
            options.full_residual_support = true;
        } else if (argument == "--dry-run") {
            options.dry_run = true;
        } else if (argument == "--self-test") {
            options.self_test = true;
        } else if (argument == "--max-table-entries") {
            options.max_table_entries = parse_u64(
                need("--max-table-entries"), "--max-table-entries");
        } else if (argument == "--pair") {
            const u64 left = parse_u64(need("--pair left"), "--pair");
            const u64 right = parse_u64(need("--pair right"), "--pair");
            options.only_pair = ResidualPair{left, right};
        } else if (argument == "--help") {
            std::cout
                << "usage: search_residual_exact [options]\n"
                << "  --value M\n"
                << "  --force-single-prime P  (requires v_P((M-1)!)=1)\n"
                << "  --full-residual-support\n"
                << "  --pair R S\n"
                << "  --max-table-entries N\n"
                << "  --dry-run\n"
                << "  --self-test\n";
            std::exit(0);
        } else {
            throw std::invalid_argument("unknown option: " + argument);
        }
    }
    if (options.value < 2) throw std::invalid_argument("value must be >= 2");
    return options;
}

} // namespace

int main(int argc, char** argv) {
    try {
        const Options options = parse_options(argc, argv);
        if (options.self_test) {
            run_self_tests();
            return 0;
        }
        const auto primes = primes_through(options.value);
        const auto value_factors = factor_small(options.value, primes);
        std::vector<PrimePower> previous_caps;
        for (unsigned p : primes) {
            if (p >= options.value) break;
            const unsigned cap = valuation_factorial(options.value - 1, p);
            if (cap) previous_caps.push_back({p, cap});
        }

        if (options.force_single_prime) {
            bool found = false;
            for (const auto& cap : previous_caps) {
                if (cap.prime == options.force_single_prime) {
                    found = true;
                    if (cap.exponent != 1) {
                        throw std::invalid_argument(
                            "forced prime must have exponent exactly one in (M-1)!");
                    }
                }
            }
            if (!found) throw std::invalid_argument("forced prime is absent from (M-1)!");
            if (options.value % options.force_single_prime == 0) {
                throw std::invalid_argument(
                    "forced prime must also have exponent one in M!");
            }
        }

        std::vector<ResidualPair> residual_pairs;
        enumerate_residual_pairs_rec(value_factors, 0, 1, 1,
                                     options.full_residual_support,
                                     residual_pairs);
        residual_pairs.erase(
            std::remove_if(residual_pairs.begin(), residual_pairs.end(),
                [&](const ResidualPair& pair) {
                    return !is_c_ge_two_pair(options.value, value_factors, pair);
                }),
            residual_pairs.end());

        std::vector<ResidualPair> residual_groups;
        for (const auto& pair : residual_pairs) {
            ResidualPair group{std::min(pair.left, pair.right),
                               std::max(pair.left, pair.right)};
            if (options.only_pair) {
                const u64 requested_left = std::min(options.only_pair->left,
                                                    options.only_pair->right);
                const u64 requested_right = std::max(options.only_pair->left,
                                                     options.only_pair->right);
                if (group.left != requested_left || group.right != requested_right) {
                    continue;
                }
            }
            residual_groups.push_back(group);
        }
        std::sort(residual_groups.begin(), residual_groups.end(),
                  [](const auto& a, const auto& b) {
                      return std::tie(a.left, a.right) < std::tie(b.left, b.right);
                  });
        residual_groups.erase(
            std::unique(residual_groups.begin(), residual_groups.end(),
                [](const auto& a, const auto& b) {
                    return a.left == b.left && a.right == b.right;
                }),
            residual_groups.end());

        if (residual_groups.empty()) {
            throw std::invalid_argument("no residual pair in requested c>=2 domain");
        }

        const cpp_int previous_factorial = factorial(options.value - 1);
        const cpp_int current_factorial = previous_factorial * options.value;
        bool complete = !options.dry_run;
        u64 candidates = 0;
        std::cout << "search=residual_pair_exact_mitm\n";
        std::cout << "value=" << options.value << "\n";
        std::cout << "c_ge_two=true\n";
        std::cout << "full_residual_support="
                  << (options.full_residual_support ? "true" : "false") << "\n";
        std::cout << "force_single_prime=" << options.force_single_prime << "\n";
        std::cout << "ordered_residual_pairs=" << residual_pairs.size() << "\n";
        std::cout << "residual_groups=" << residual_groups.size() << "\n";

        for (const auto& group : residual_groups) {
            search_group(options, group, value_factors, previous_caps,
                        previous_factorial, current_factorial,
                        complete, candidates);
        }

        std::cout << "search_complete=" << (complete ? "true" : "false") << "\n";
        std::cout << "exact_common_fiber_candidates=" << candidates << "\n";
        if (candidates) return 1;
        return complete ? 0 : 2;
    } catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << "\n";
        return 3;
    }
}
