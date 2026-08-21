#!/usr/bin/env python3
"""Verify Kempner values in the complete 113-smooth-neighbor artifact.

The pinned input is Daniel Berger's public list of integers ``n`` for which
both ``n`` and ``n + 1`` are 113-smooth.  This script checks the artifact
bytes and shape, independently factors both neighbors over the primes at most
113, and recomputes their exact Kempner values by Legendre inversion.

It verifies that no consecutive 113-smooth pair has equal Kempner values.
Consequently there is no Tutescu counterexample with common value ``m < 127``:
there is no prime strictly between 113 and 127, so every divisor of ``m!`` in
that range is 113-smooth.  The script does not itself certify the
Størmer/Lehmer exhaustive-Pell argument used to produce a complete list; that
remains an explicitly external mathematical and computational input.
"""

from __future__ import annotations

import argparse
import hashlib
import pathlib
import urllib.request


SOURCE_COMMIT = "6fc4c364ee995a6aef5f788e29cdfc307d37f9a5"
DEFAULT_URL = (
    "https://raw.githubusercontent.com/db711/infrastructure/"
    f"{SOURCE_COMMIT}/data/twin_smooths_113_sorted_full.txt"
)
EXPECTED_SHA256 = "9ad599518af925638f1c72e6bdcc3cfd7a3c26554a6cca3c44930689bee7f43d"
EXPECTED_ENTRIES = 33_233
EXPECTED_MAXIMUM = 19_316_158_377_073_923_834_000
SMOOTHNESS_BOUND = 113
FIRST_PRIME_ABOVE_BOUND = 127


def primes_at_most(bound: int) -> list[int]:
    primes: list[int] = []
    for candidate in range(2, bound + 1):
        if all(candidate % prime for prime in primes if prime * prime <= candidate):
            primes.append(candidate)
    return primes


PRIMES = primes_at_most(SMOOTHNESS_BOUND)


def factor_smooth(value: int) -> dict[int, int]:
    original = value
    factors: dict[int, int] = {}
    for prime in PRIMES:
        while value % prime == 0:
            factors[prime] = factors.get(prime, 0) + 1
            value //= prime
    if value != 1:
        raise ValueError(
            f"{original} has a prime factor above {SMOOTHNESS_BOUND}: {value}"
        )
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
        (
            prime_power_kempner_value(prime, exponent)
            for prime, exponent in factors.items()
        ),
        default=0,
    )


def load_bytes(path: pathlib.Path | None, url: str) -> bytes:
    if path is not None:
        return path.read_bytes()
    with urllib.request.urlopen(url, timeout=60) as response:
        return response.read()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--file", type=pathlib.Path, help="use a local copy instead of downloading"
    )
    parser.add_argument("--url", default=DEFAULT_URL)
    parser.add_argument("--skip-hash-check", action="store_true")
    args = parser.parse_args()

    if primes_at_most(FIRST_PRIME_ABOVE_BOUND) != PRIMES + [
        FIRST_PRIME_ABOVE_BOUND
    ]:
        raise AssertionError("unexpected prime gap above the smoothness bound")

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
    if any(value <= 0 for value in values):
        raise SystemExit("table contains a nonpositive entry")
    if any(left >= right for left, right in zip(values, values[1:])):
        raise SystemExit("table is not strictly increasing")
    if values[-1] != EXPECTED_MAXIMUM:
        raise SystemExit(
            f"unexpected maximum {values[-1]}; expected {EXPECTED_MAXIMUM}"
        )

    equal_pairs: list[tuple[int, int, int]] = []
    maximum_kempner_value = 0
    closest_gap: tuple[int, int, int, int] | None = None
    for n in values:
        left = kempner_value(factor_smooth(n))
        right = kempner_value(factor_smooth(n + 1))
        maximum_kempner_value = max(maximum_kempner_value, left, right)
        gap = abs(left - right)
        if closest_gap is None or gap < closest_gap[0]:
            closest_gap = (gap, n, left, right)
        if left == right:
            equal_pairs.append((n, n + 1, left))

    print(f"source_commit={SOURCE_COMMIT}")
    print(f"sha256={digest}")
    print(f"entries={len(values)}")
    print(f"maximum_n={values[-1]}")
    print(f"maximum_recomputed_kempner_value={maximum_kempner_value}")
    print(f"equal_kempner_pairs={len(equal_pairs)}")
    print(f"closest_kempner_gap={closest_gap}")
    print(f"excluded_common_values_below={FIRST_PRIME_ABOVE_BOUND}")
    if equal_pairs:
        print(f"first_equal_pairs={equal_pairs[:10]}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
