#!/usr/bin/env python3
"""Audit activation-gap implications on actual fixed-shift Kempner fibers.

The scan includes non-coprime pairs.  It verifies every choice of controlling
prime power, so a pair with several controllers contributes several
configurations.  It also searches all values in the computed range, without a
gap cutoff, for the earliest actual distinct-controller collision with c > 1.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache


def valuation(n: int, p: int) -> int:
    total = 0
    while n % p == 0 and n:
        n //= p
        total += 1
    return total


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


@lru_cache(maxsize=None)
def kempner_prime_power(p: int, exponent: int) -> int:
    low = 1
    high = p * exponent
    while low < high:
        middle = (low + high) // 2
        if valuation_factorial(middle, p) >= exponent:
            high = middle
        else:
            low = middle + 1
    return low


@dataclass(frozen=True)
class Metrics:
    value: int
    max_exponent: int
    controllers: tuple[tuple[int, int], ...]


def metrics(n: int, spf: list[int]) -> Metrics:
    components: list[tuple[int, int, int]] = []
    maximum_exponent = 0
    remaining = n
    while remaining > 1:
        p = spf[remaining]
        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1
        maximum_exponent = max(maximum_exponent, exponent)
        components.append((p, exponent, kempner_prime_power(p, exponent)))
    value = max((component[2] for component in components), default=1)
    controllers = tuple(
        (p, exponent) for p, exponent, component_value in components
        if component_value == value
    )
    return Metrics(value, maximum_exponent, controllers)


def ordered_configuration(
    left: Metrics,
    right: Metrics,
    left_controller: tuple[int, int],
    right_controller: tuple[int, int],
) -> tuple[int, int, int, int, int, int]:
    left_p, left_a = left_controller
    right_p, right_a = right_controller
    if left_p < right_p:
        return left_p, right_p, left_a, right_a, left.max_exponent, right.max_exponent
    return right_p, left_p, right_a, left_a, right.max_exponent, left.max_exponent


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-x", type=int, default=300_000)
    parser.add_argument("--max-gap", type=int, default=256)
    args = parser.parse_args()
    if args.max_x < 2 or args.max_gap < 1:
        raise SystemExit("max-x must be at least 2 and max-gap must be positive")

    limit = args.max_x + args.max_gap
    spf = sieve_spf(limit)
    data = [Metrics(1, 0, ())]
    data.extend(metrics(n, spf) for n in range(1, limit + 1))

    collisions = 0
    shared_configurations = 0
    distinct_configurations = 0
    violations: list[tuple[int, int, int]] = []
    first_shared: tuple[int, ...] | None = None
    first_distinct_c_gt_one_within_gap: tuple[int, ...] | None = None

    for x in range(2, args.max_x + 1):
        left = data[x]
        for gap in range(1, args.max_gap + 1):
            y = x + gap
            right = data[y]
            if left.value != right.value:
                continue
            collisions += 1
            m = left.value
            for left_controller in left.controllers:
                for right_controller in right.controllers:
                    left_p, left_a = left_controller
                    right_p, right_a = right_controller
                    if left_p == right_p:
                        shared_configurations += 1
                        p = left_p
                        threshold = valuation_factorial(m - 1, p) + 1
                        required_power = p**threshold
                        shared_ok = gap % required_power == 0
                        size_ok = m <= p * valuation(gap, p)
                        if not (shared_ok and size_ok):
                            violations.append((x, gap, m))
                        candidate = (x, gap, m, p, left_a, right_a, threshold)
                        if first_shared is None or candidate < first_shared:
                            first_shared = candidate
                        continue

                    distinct_configurations += 1
                    p, q, a, b, A, B = ordered_configuration(
                        left, right, left_controller, right_controller
                    )
                    if m % (p * q):
                        violations.append((x, gap, m))
                        continue
                    c = m // (p * q)
                    lower_a = q * c + valuation_factorial(q * c - 1, p)
                    lower_b = p * c + valuation_factorial(p * c - 1, q)
                    r = A - (q * c + 1)
                    s = B - p * c
                    defect = (A - 1) * B - m
                    defect_rhs = m * (c - 1) + q * c * s + p * c * r + r * s
                    distinct_ok = (
                        a >= lower_a
                        and b >= lower_b
                        and r >= 0
                        and s >= 0
                        and c * m + min(A, B) <= A * B
                        and defect == defect_rhs
                    )
                    if not distinct_ok:
                        violations.append((x, gap, m))
                    if c > 1:
                        candidate = (x, gap, y, m, p, q, c, a, b, A, B, r, s)
                        if (
                            first_distinct_c_gt_one_within_gap is None
                            or candidate < first_distinct_c_gt_one_within_gap
                        ):
                            first_distinct_c_gt_one_within_gap = candidate

    # This pass has no fixed-gap cutoff.  It finds the first collision by its
    # larger member, using the earliest occurrence of each controller.
    first_by_value: dict[int, dict[int, tuple[int, int, int]]] = {}
    smallest_distinct_c_gt_one: tuple[int, ...] | None = None
    for n in range(2, limit + 1):
        current = data[n]
        m = current.value
        prior_controllers = first_by_value.setdefault(m, {})
        for q, b in current.controllers:
            for p, (prior_n, a, prior_E) in prior_controllers.items():
                if p == q or m % (p * q):
                    continue
                c = m // (p * q)
                if c <= 1:
                    continue
                if p < q:
                    ordered = (p, q, a, b, prior_E, current.max_exponent)
                else:
                    ordered = (q, p, b, a, current.max_exponent, prior_E)
                candidate = (prior_n, n, m, *ordered[:2], c, *ordered[2:])
                if smallest_distinct_c_gt_one is None or (n, prior_n) < (
                    smallest_distinct_c_gt_one[1], smallest_distinct_c_gt_one[0]
                ):
                    smallest_distinct_c_gt_one = candidate
            prior_controllers.setdefault(q, (n, b, current.max_exponent))

    print(f"max_x={args.max_x}")
    print(f"max_gap={args.max_gap}")
    print(f"fixed_gap_collisions={collisions}")
    print(f"shared_controller_configurations={shared_configurations}")
    print(f"distinct_controller_configurations={distinct_configurations}")
    print(f"theorem_violations={len(violations)}")
    print(f"first_shared_configuration={first_shared}")
    print(
        "first_distinct_c_gt_one_within_gap="
        f"{first_distinct_c_gt_one_within_gap}"
    )
    print(f"smallest_distinct_c_gt_one_by_larger_member={smallest_distinct_c_gt_one}")
    if violations:
        print(f"first_violations={violations[:10]}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
