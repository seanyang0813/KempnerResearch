#!/usr/bin/env python3
"""Exhaustively search common Kempner fibers by divisors of m!.

For consecutive positive integers x and x+1,

    S(x) = S(x+1) = m

is equivalent to x(x+1) dividing m! while neither x nor x+1 divides
(m-1)!.  It is enough to enumerate divisors x <= sqrt(m!), because the
product condition forces that inequality.
"""

from __future__ import annotations

import argparse
from math import factorial, isqrt


def primes_up_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p * p) // p + 1
            sieve[p * p : limit + 1 : p] = b"\x00" * count
    return [p for p in range(2, limit + 1) if sieve[p]]


def valuation_factorial(n: int, p: int) -> int:
    total = 0
    while n:
        n //= p
        total += n
    return total


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-value", type=int, default=30)
    args = parser.parse_args()
    if args.max_value < 2:
        raise SystemExit("max-value must be at least 2")

    primes = primes_up_to(args.max_value)
    total_divisors_scanned = 0
    total_consecutive_divisor_pairs = 0
    common_fiber_pairs: list[tuple[int, int, int]] = []
    final_values: list[tuple[int, int, int]] = []

    for m in range(2, args.max_value + 1):
        factorial_m = factorial(m)
        factorial_previous = factorial_m // m
        square_root = isqrt(factorial_m)
        factorization = [
            (p, valuation_factorial(m, p)) for p in primes if p <= m
        ]
        counts = [0, 0]

        def visit(index: int, divisor: int) -> None:
            if index == len(factorization):
                counts[0] += 1
                if divisor > 1 and factorial_m % (divisor + 1) == 0:
                    counts[1] += 1
                    if (
                        factorial_previous % divisor != 0
                        and factorial_previous % (divisor + 1) != 0
                    ):
                        common_fiber_pairs.append((m, divisor, divisor + 1))
                return

            p, exponent = factorization[index]
            candidate = divisor
            for _ in range(exponent + 1):
                if candidate > square_root:
                    break
                visit(index + 1, candidate)
                candidate *= p

        visit(0, 1)
        total_divisors_scanned += counts[0]
        total_consecutive_divisor_pairs += counts[1]
        final_values.append((m, counts[0], counts[1]))

    print(f"max_common_value={args.max_value}")
    print(f"divisors_at_most_sqrt_scanned={total_divisors_scanned}")
    print(f"consecutive_divisor_pairs={total_consecutive_divisor_pairs}")
    print(f"common_fiber_pairs={len(common_fiber_pairs)}")
    print(f"first_common_fiber_pairs={common_fiber_pairs[:10]}")
    print(f"last_five_values={final_values[-5:]}")
    if common_fiber_pairs:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
