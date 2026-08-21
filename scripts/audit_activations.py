#!/usr/bin/env python3
"""Exhaustively audit all activating-prime pairs for common values m <= M.

Besides the previously formalized coprime-fiber bound, this checks the exact
activation thresholds and the oriented activation-defect identity used by the
fixed-shift research note.
"""

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
    zero_oriented_defect = 0
    maximum_c = 0
    maximum_r = 0
    maximum_s = 0
    violations: list[tuple[int, int, int, int, int]] = []
    sharp_misclassified: list[tuple[int, int, int, int, int]] = []
    controller_regime_misclassified: list[tuple[int, int, int, int, int]] = []
    for m in range(2, maximum + 1):
        factors = factor(m, spf)
        activations: dict[int, range] = {}
        jumps: dict[int, int] = {}
        for p, jump in factors:
            old = valuation_factorial(m - 1, p)
            activations[p] = range(old + 1, old + jump + 1)
            jumps[p] = jump
        primes = sorted(activations)
        for i, p in enumerate(primes):
            for q in primes[i + 1 :]:
                c = m // (p * q)
                lower_a = q * c + valuation_factorial(q * c - 1, p)
                lower_b = p * c + valuation_factorial(p * c - 1, q)
                for a in activations[p]:
                    for b in activations[q]:
                        configurations += 1
                        activation_slack_a = a - lower_a
                        activation_slack_b = b - lower_b
                        r = a - (q * c + 1)
                        s = b - p * c
                        defect = (a - 1) * b - m
                        defect_rhs = (
                            m * (c - 1) + q * c * s + p * c * r + r * s
                        )
                        maximum_c = max(maximum_c, c)
                        maximum_r = max(maximum_r, r)
                        maximum_s = max(maximum_s, s)

                        exact_bounds = lower_a <= a and lower_b <= b
                        exact_slacks = (
                            0 <= activation_slack_a < jumps[p]
                            and 0 <= activation_slack_b < jumps[q]
                        )
                        crude_bounds = q * c + 1 <= a and p * c <= b
                        defect_identity = defect == defect_rhs
                        if not (exact_bounds and exact_slacks and crude_bounds and defect_identity):
                            violations.append((m, p, q, a, b))
                        if not (m + min(a, b) <= a * b):
                            violations.append((m, p, q, a, b))
                        oriented_zero = defect == 0
                        controller_regime_is_c_one = 0 <= defect < m
                        if controller_regime_is_c_one != (c == 1):
                            controller_regime_misclassified.append((m, p, q, a, b))
                        oriented_classified = (
                            c == 1
                            and p < q < 2 * p
                            and a == q + 1
                            and b == p
                        )
                        zero_oriented_defect += oriented_zero
                        if oriented_zero != oriented_classified:
                            sharp_misclassified.append((m, p, q, a, b))
                        is_sharp = m + min(a, b) == a * b
                        classified = oriented_classified
                        sharp += is_sharp
                        if is_sharp != classified:
                            sharp_misclassified.append((m, p, q, a, b))

    print(f"max_value={maximum}")
    print(f"activation_pair_configurations={configurations}")
    print(f"bound_violations={len(violations)}")
    print(f"sharp_configurations={sharp}")
    print(f"zero_oriented_defect_configurations={zero_oriented_defect}")
    print(f"sharp_classification_mismatches={len(sharp_misclassified)}")
    print(
        "controller_defect_regime_mismatches="
        f"{len(controller_regime_misclassified)}"
    )
    print(f"maximum_c={maximum_c}")
    print(f"maximum_r={maximum_r}")
    print(f"maximum_s={maximum_s}")
    if violations:
        print("first_violations=", violations[:10])
    if sharp_misclassified:
        print("first_sharp_mismatches=", sharp_misclassified[:10])
    if controller_regime_misclassified:
        print("first_controller_regime_mismatches=", controller_regime_misclassified[:10])
    if violations or sharp_misclassified or controller_regime_misclassified:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
