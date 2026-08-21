#!/usr/bin/env python3
"""Verify Kempner values in Luca--Najman's complete 100-smooth-neighbor table.

The external mathematical input is the published completeness of the table of
odd x for which every prime divisor of x^2-1 is below 100.  This script checks
the table bytes, parses every entry, independently factors n=(x-1)/2 and n+1,
and recomputes their exact Kempner values by Legendre inversion.

It verifies the finite consequence "no common value m <= 100" because a
counterexample with such an m would have both n and n+1 100-smooth.  It does
not itself certify the Pell/primitive-divisor argument proving that the
published table is complete.
"""

from __future__ import annotations

import argparse
import hashlib
import pathlib
import urllib.request


DEFAULT_URL = "https://web.math.pmf.unizg.hr/~fnajman/oddsort.txt"
EXPECTED_SHA256 = "035f2e7342d11bb86d4b7dacad611e7adb5601f8e5352a1e525e0646ad0f4380"
EXPECTED_ENTRIES = 13_374


def primes_below_100() -> list[int]:
    primes: list[int] = []
    for candidate in range(2, 100):
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
    return primes


PRIMES = primes_below_100()


def factor_100_smooth(value: int) -> dict[int, int]:
    original = value
    factors: dict[int, int] = {}
    for prime in PRIMES:
        while value % prime == 0:
            factors[prime] = factors.get(prime, 0) + 1
            value //= prime
    if value != 1:
        raise ValueError(f"{original} has an unchecked prime factor {value}")
    return factors


def factorial_valuation(index: int, prime: int) -> int:
    total = 0
    while index:
        index //= prime
        total += index
    return total


def prime_power_kempner_value(prime: int, exponent: int) -> int:
    low, high = 0, prime * exponent
    while low < high:
        middle = (low + high) // 2
        if factorial_valuation(middle, prime) >= exponent:
            high = middle
        else:
            low = middle + 1
    return low


def kempner_value(factors: dict[int, int]) -> int:
    return max(
        (prime_power_kempner_value(prime, exponent)
         for prime, exponent in factors.items()),
        default=0,
    )


def load_bytes(path: pathlib.Path | None, url: str) -> bytes:
    if path is not None:
        return path.read_bytes()
    with urllib.request.urlopen(url, timeout=60) as response:
        return response.read()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", type=pathlib.Path,
                        help="use a local copy instead of downloading")
    parser.add_argument("--url", default=DEFAULT_URL)
    parser.add_argument("--skip-hash-check", action="store_true")
    args = parser.parse_args()

    payload = load_bytes(args.file, args.url)
    digest = hashlib.sha256(payload).hexdigest()
    if not args.skip_hash_check and digest != EXPECTED_SHA256:
        raise SystemExit(
            f"unexpected SHA-256 {digest}; expected {EXPECTED_SHA256}"
        )

    values = [int(line) for line in payload.splitlines() if line.strip()]
    if len(values) != EXPECTED_ENTRIES:
        raise SystemExit(
            f"unexpected entry count {len(values)}; expected {EXPECTED_ENTRIES}"
        )
    if len(set(values)) != len(values):
        raise SystemExit("duplicate table entries")
    if any(value <= 0 or value % 2 == 0 for value in values):
        raise SystemExit("table contains a nonpositive or even entry")

    equal_pairs: list[tuple[int, int, int]] = []
    at_most_100_pairs = 0
    maximum_kempner_value = 0
    for odd_x in values:
        n = (odd_x - 1) // 2
        left = kempner_value(factor_100_smooth(n))
        right = kempner_value(factor_100_smooth(n + 1))
        maximum_kempner_value = max(maximum_kempner_value, left, right)
        if left == right:
            equal_pairs.append((n, n + 1, left))
            if left <= 100:
                at_most_100_pairs += 1

    print(f"sha256={digest}")
    print(f"entries={len(values)}")
    print(f"maximum_odd_x={max(values)}")
    print(f"maximum_recomputed_kempner_value={maximum_kempner_value}")
    print(f"equal_kempner_pairs={len(equal_pairs)}")
    print(f"equal_kempner_pairs_with_value_at_most_100={at_most_100_pairs}")
    if equal_pairs:
        print(f"first_equal_pairs={equal_pairs[:10]}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
