#!/usr/bin/env python3
"""Exhaustively audit all activating-prime pairs for common values m <= M."""

from __future__ import annotations

import argparse


def valuation_factorial(n: int, p: int) -> int:
    total = 0
    while n:
        n //= p
        total += n
    return total


def sieve_spf(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    for p in range(2, int(limit**0.5) + 1):
        if spf[p] != p:
            continue
        for k in range(p * p, limit + 1, p):
            if spf[k] == k:
                spf[k] = p
    return spf


def factor(n: int, spf: list[int]) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    while n > 1:
        p = spf[n]
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        result.append((p, a))
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-value", type=int, default=1_000_000)
    args = parser.parse_args()
    maximum = args.max_value
    spf = sieve_spf(maximum)

    configurations = 0
    sharp = 0
    violations: list[tuple[int, int, int, int, int]] = []
    sharp_misclassified: list[tuple[int, int, int, int, int]] = []
    for m in range(2, maximum + 1):
        factors = factor(m, spf)
        activations: dict[int, range] = {}
        for p, jump in factors:
            old = valuation_factorial(m - 1, p)
            activations[p] = range(old + 1, old + jump + 1)
        primes = sorted(activations)
        for i, p in enumerate(primes):
            for q in primes[i + 1 :]:
                r = m // (p * q)
                for a in activations[p]:
                    for b in activations[q]:
                        configurations += 1
                        if not (q * r + 1 <= a and p * r <= b):
                            violations.append((m, p, q, a, b))
                        if not (m + min(a, b) <= a * b):
                            violations.append((m, p, q, a, b))
                        is_sharp = m + min(a, b) == a * b
                        classified = r == 1 and p < q < 2 * p and a == q + 1 and b == p
                        sharp += is_sharp
                        if is_sharp != classified:
                            sharp_misclassified.append((m, p, q, a, b))

    print(f"max_value={maximum}")
    print(f"activation_pair_configurations={configurations}")
    print(f"bound_violations={len(violations)}")
    print(f"sharp_configurations={sharp}")
    print(f"sharp_classification_mismatches={len(sharp_misclassified)}")
    if violations:
        print("first_violations=", violations[:10])
    if sharp_misclassified:
        print("first_sharp_mismatches=", sharp_misclassified[:10])
    if violations or sharp_misclassified:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
