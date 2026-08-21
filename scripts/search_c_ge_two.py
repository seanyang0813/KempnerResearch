#!/usr/bin/env python3
"""Layered exact search for Tutescu counterexamples with controller cofactor c >= 2.

For a hypothetical pair ``S(n) = S(n + 1) = m``, choose distinct activating
controller primes and order them as ``p < q``.  Write ``m = p*q*c``.  This
script exhausts every such choice with ``c >= 2`` through ``m <= M``.

For either placement of the ordered controllers, write

    n     = left_prime**left_exponent * u
    n + 1 = right_prime**right_exponent * v.

The controller exponents range over the *exact* activation intervals

    v_p((m-1)!) < exponent <= v_p(m!).

Adjacency makes the controller supports disjoint.  Hence ``u`` uses neither
controller prime and is a divisor of the corresponding part of ``m!``.  The
search enumerates these divisors exactly with a meet-in-the-middle residue
index.  It first enforces

    left_prime**left_exponent * u == -1
        (mod right_prime**right_exponent),

then reconstructs ``v`` and checks, in separate auditable layers:

* exact right-controller multiplicity and disjoint supports;
* m-smoothness of the right cofactor;
* every factorial exponent cap, equivalently ``n*(n+1) | m!``;
* the two last-step residuals and their product inside ``m``;
* the factorial-complement/discriminant square identity;
* the defining common-fiber divisibilities at ``m`` and ``m-1``.

Every layer reports its exact count and lexicographically smallest survivor.
Transition failures are also counted with their smallest witnesses.  A small
naive-divisor cross-check guards the meet-in-the-middle implementation.

No probabilistic primality test, floating-point mathematical decision, or
external package is used.  Floating point occurs only in balancing the two
meet-in-the-middle halves and cannot affect which divisors are enumerated.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from dataclasses import dataclass, field
import json
from math import gcd, isqrt, log
from time import perf_counter
from typing import Iterator


Factorization = dict[int, int]
PrimePowers = list[tuple[int, int]]


def sieve_primes(limit: int) -> tuple[list[int], list[int]]:
    """Return all primes through ``limit`` and a smallest-prime-factor table."""

    spf = list(range(limit + 1))
    if limit >= 0:
        spf[0] = 0
    if limit >= 1:
        spf[1] = 1
    for p in range(2, isqrt(limit) + 1):
        if spf[p] != p:
            continue
        for multiple in range(p * p, limit + 1, p):
            if spf[multiple] == multiple:
                spf[multiple] = p
    return [p for p in range(2, limit + 1) if spf[p] == p], spf


def factor_small(n: int, spf: list[int]) -> Factorization:
    """Factor ``n`` using an SPF table whose range contains ``n``."""

    factors: Factorization = {}
    while n > 1:
        p = spf[n]
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        factors[p] = exponent
    return factors


def valuation_factorial(n: int, p: int) -> int:
    total = 0
    while n:
        n //= p
        total += n
    return total


def enumerate_divisors(items: PrimePowers, limit: int | None = None) -> list[int]:
    """Enumerate the divisors represented by ``items``, optionally up to a limit."""

    divisors = [1]
    for p, exponent in items:
        old = divisors
        expanded: list[int] = []
        power = 1
        for _ in range(exponent + 1):
            for divisor in old:
                candidate = divisor * power
                if limit is None or candidate <= limit:
                    expanded.append(candidate)
            power *= p
        divisors = expanded
    divisors.sort()
    return divisors


def split_prime_powers(items: PrimePowers) -> tuple[PrimePowers, PrimePowers]:
    """Balance divisor counts across two exact meet-in-the-middle halves."""

    left: PrimePowers = []
    right: PrimePowers = []
    left_weight = 0.0
    right_weight = 0.0
    for item in sorted(items, key=lambda pair: pair[1], reverse=True):
        weight = log(item[1] + 1)
        if left_weight <= right_weight:
            left.append(item)
            left_weight += weight
        else:
            right.append(item)
            right_weight += weight
    return left, right


@dataclass
class DivisorResidueIndex:
    """Meet-in-the-middle representation of all divisors of prime-power items."""

    items: PrimePowers
    left_values: list[int] = field(init=False)
    right_values: list[int] = field(init=False)

    def __post_init__(self) -> None:
        left_items, right_items = split_prime_powers(self.items)
        self.left_values = enumerate_divisors(left_items)
        self.right_values = enumerate_divisors(right_items)

    @property
    def divisor_count(self) -> int:
        return len(self.left_values) * len(self.right_values)

    @property
    def materialized_half_divisors(self) -> int:
        return len(self.left_values) + len(self.right_values)

    def congruent_divisors(
        self, limit: int, multiplier: int, modulus: int
    ) -> Iterator[int]:
        """Yield all ``u <= limit`` with ``multiplier*u == -1 (mod modulus)``.

        Every prime represented by this index differs from the prime underlying
        ``modulus``, so all half-divisors are invertible modulo ``modulus``.
        Each full divisor has a unique left/right decomposition and is yielded
        exactly once.
        """

        target = (-pow(multiplier, -1, modulus)) % modulus
        buckets: dict[int, list[int]] = {}
        for right in self.right_values:
            if right > limit:
                break
            buckets.setdefault(right % modulus, []).append(right)

        for left in self.left_values:
            if left > limit:
                break
            required = (target * pow(left, -1, modulus)) % modulus
            matching = buckets.get(required)
            if not matching:
                continue
            stop = bisect_right(matching, limit // left)
            for right in matching[:stop]:
                yield left * right


def factor_over_primes(value: int, primes: list[int]) -> tuple[Factorization, int]:
    """Remove every prime in ``primes`` and return exponents plus the remainder."""

    factors: Factorization = {}
    remainder = value
    for p in primes:
        if remainder % p:
            continue
        exponent = 0
        while remainder % p == 0:
            remainder //= p
            exponent += 1
        factors[p] = exponent
        if remainder == 1:
            break
    return factors, remainder


def factor_from_items(value: int, items: PrimePowers) -> Factorization:
    """Recover a known divisor's factorization and assert representation exactness."""

    factors: Factorization = {}
    remainder = value
    for p, cap in items:
        exponent = 0
        while remainder % p == 0:
            remainder //= p
            exponent += 1
        if exponent:
            if exponent > cap:
                raise AssertionError("enumerated divisor exceeds its exponent cap")
            factors[p] = exponent
    if remainder != 1:
        raise AssertionError("enumerated divisor has an unexpected prime factor")
    return factors


def multiply_factorization(factors: Factorization) -> int:
    result = 1
    for p, exponent in factors.items():
        result *= p**exponent
    return result


def residual(
    factors: Factorization, previous_factorial_caps: Factorization
) -> tuple[int, Factorization]:
    residual_factors = {
        p: exponent - previous_factorial_caps.get(p, 0)
        for p, exponent in factors.items()
        if exponent > previous_factorial_caps.get(p, 0)
    }
    return multiply_factorization(residual_factors), residual_factors


def json_factorization(factors: Factorization) -> dict[str, int]:
    return {str(p): factors[p] for p in sorted(factors)}


def witness_key(witness: dict[str, object]) -> tuple[object, ...]:
    return (
        witness.get("m", -1),
        witness.get("n", witness.get("core_left", -1)),
        witness.get("p", -1),
        witness.get("q", -1),
        witness.get("a_p", -1),
        witness.get("a_q", -1),
        witness.get("orientation", ""),
        witness.get("u", -1),
    )


@dataclass
class Observation:
    count: int = 0
    smallest: dict[str, object] | None = None

    def add(self, witness: dict[str, object], amount: int = 1) -> None:
        self.count += amount
        if self.smallest is None or witness_key(witness) < witness_key(self.smallest):
            self.smallest = witness.copy()


LAYER_NAMES = (
    "controller_configurations",
    "oriented_size_feasible",
    "modular_adjacency",
    "exact_controller_and_disjoint",
    "right_cofactor_m_smooth",
    "full_factorial_caps",
    "residual_constraints",
    "factorial_complement_square",
    "common_kempner_fiber",
)

REJECTION_NAMES = (
    "size_or_core_product",
    "right_controller_not_exact",
    "disjoint_support",
    "right_cofactor_not_m_smooth",
    "factorial_cap_exceeded",
    "residual_constraint_failed",
    "factorial_complement_failed",
    "common_fiber_failed",
)


def base_witness(
    *,
    m: int,
    p: int,
    q: int,
    c: int,
    a_p: int,
    a_q: int,
    orientation: str,
    left_prime: int,
    left_exponent: int,
    right_prime: int,
    right_exponent: int,
) -> dict[str, object]:
    return {
        "m": m,
        "p": p,
        "q": q,
        "c": c,
        "a_p": a_p,
        "a_q": a_q,
        "orientation": orientation,
        "left_prime": left_prime,
        "left_exponent": left_exponent,
        "right_prime": right_prime,
        "right_exponent": right_exponent,
        "core_left": left_prime**left_exponent,
        "core_right": right_prime**right_exponent,
    }


def candidate_witness(base: dict[str, object], u: int) -> dict[str, object]:
    witness = base.copy()
    core_left = int(base["core_left"])
    core_right = int(base["core_right"])
    n = core_left * u
    n_plus_one = n + 1
    witness.update(
        {
            "u": u,
            "n": n,
            "n_plus_one": n_plus_one,
            "v": n_plus_one // core_right,
        }
    )
    return witness


def run_search(maximum: int, cross_check_through: int) -> None:
    started = perf_counter()
    primes, spf = sieve_primes(maximum)
    layers = {name: Observation() for name in LAYER_NAMES}
    rejections = {name: Observation() for name in REJECTION_NAMES}

    factorial_value = 1
    total_pair_indices = 0
    total_mitm_half_divisors = 0
    summed_unbounded_divisor_space = 0
    modular_searches = 0
    cross_checked_searches = 0
    unique_counterexamples: set[tuple[int, int]] = set()

    for m in range(2, maximum + 1):
        factorial_value *= m
        previous_factorial = factorial_value // m
        square_root = isqrt(factorial_value)
        m_factors = factor_small(m, spf)
        controller_primes = sorted(m_factors)
        if len(controller_primes) < 2:
            continue

        factorial_caps = {
            p: valuation_factorial(m, p) for p in primes if p <= m
        }
        primes_through_m = list(factorial_caps)
        previous_caps = {
            p: factorial_caps[p] - m_factors.get(p, 0)
            for p in factorial_caps
        }

        for p_index, p in enumerate(controller_primes):
            for q in controller_primes[p_index + 1 :]:
                c = m // (p * q)
                if c < 2:
                    continue

                other_items = [
                    (prime, exponent)
                    for prime, exponent in factorial_caps.items()
                    if prime != p and prime != q
                ]
                divisor_index = DivisorResidueIndex(other_items)
                total_pair_indices += 1
                total_mitm_half_divisors += divisor_index.materialized_half_divisors

                p_exponents = range(previous_caps[p] + 1, factorial_caps[p] + 1)
                q_exponents = range(previous_caps[q] + 1, factorial_caps[q] + 1)

                for a_p in p_exponents:
                    for a_q in q_exponents:
                        controller = {
                            "m": m,
                            "p": p,
                            "q": q,
                            "c": c,
                            "a_p": a_p,
                            "a_q": a_q,
                            "p_activation_interval": [
                                previous_caps[p] + 1,
                                factorial_caps[p],
                            ],
                            "q_activation_interval": [
                                previous_caps[q] + 1,
                                factorial_caps[q],
                            ],
                        }
                        layers["controller_configurations"].add(controller)

                        orientations = (
                            ("p_on_n", p, a_p, q, a_q),
                            ("q_on_n", q, a_q, p, a_p),
                        )
                        for (
                            orientation,
                            left_prime,
                            left_exponent,
                            right_prime,
                            right_exponent,
                        ) in orientations:
                            base = base_witness(
                                m=m,
                                p=p,
                                q=q,
                                c=c,
                                a_p=a_p,
                                a_q=a_q,
                                orientation=orientation,
                                left_prime=left_prime,
                                left_exponent=left_exponent,
                                right_prime=right_prime,
                                right_exponent=right_exponent,
                            )
                            core_left = int(base["core_left"])
                            core_right = int(base["core_right"])
                            if (
                                core_left > square_root
                                or core_left * core_right > factorial_value
                            ):
                                rejections["size_or_core_product"].add(base)
                                continue

                            layers["oriented_size_feasible"].add(base)
                            cofactor_limit = square_root // core_left
                            summed_unbounded_divisor_space += (
                                divisor_index.divisor_count
                            )
                            modular_searches += 1
                            modular_candidates = list(
                                divisor_index.congruent_divisors(
                                    cofactor_limit, core_left, core_right
                                )
                            )

                            if m <= cross_check_through:
                                expected = [
                                    u
                                    for u in enumerate_divisors(
                                        other_items, cofactor_limit
                                    )
                                    if (core_left * u + 1) % core_right == 0
                                ]
                                if sorted(modular_candidates) != expected:
                                    raise AssertionError(
                                        "meet-in-the-middle mismatch for "
                                        f"m={m}, p={p}, q={q}, "
                                        f"a_p={a_p}, a_q={a_q}, "
                                        f"orientation={orientation}"
                                    )
                                cross_checked_searches += 1

                            for u in modular_candidates:
                                witness = candidate_witness(base, u)
                                layers["modular_adjacency"].add(witness)
                                n = int(witness["n"])
                                n_plus_one = int(witness["n_plus_one"])
                                v = int(witness["v"])

                                if v % right_prime == 0:
                                    rejections["right_controller_not_exact"].add(
                                        witness
                                    )
                                    continue

                                u_factors = factor_from_items(u, other_items)
                                v_factors, v_remainder = factor_over_primes(
                                    v, primes_through_m
                                )
                                left_factors = u_factors.copy()
                                left_factors[left_prime] = left_exponent
                                right_factors = v_factors.copy()
                                right_factors[right_prime] = right_exponent

                                support_disjoint = (
                                    gcd(n, n_plus_one) == 1
                                    and not (set(left_factors) & set(right_factors))
                                    and right_factors.get(left_prime, 0) == 0
                                    and left_factors.get(right_prime, 0) == 0
                                )
                                if not support_disjoint:
                                    failed = witness.copy()
                                    failed["u_factorization"] = json_factorization(
                                        u_factors
                                    )
                                    failed["known_v_factorization"] = (
                                        json_factorization(v_factors)
                                    )
                                    rejections["disjoint_support"].add(failed)
                                    continue

                                disjoint_witness = witness.copy()
                                disjoint_witness["u_factorization"] = (
                                    json_factorization(u_factors)
                                )
                                disjoint_witness["known_v_factorization"] = (
                                    json_factorization(v_factors)
                                )
                                disjoint_witness["v_unfactored_remainder"] = v_remainder
                                layers["exact_controller_and_disjoint"].add(
                                    disjoint_witness
                                )

                                if v_remainder != 1:
                                    rejections[
                                        "right_cofactor_not_m_smooth"
                                    ].add(disjoint_witness)
                                    continue

                                smooth_witness = disjoint_witness.copy()
                                smooth_witness["v_factorization"] = (
                                    smooth_witness.pop("known_v_factorization")
                                )
                                smooth_witness.pop("v_unfactored_remainder")
                                layers["right_cofactor_m_smooth"].add(smooth_witness)

                                exponent_caps_hold = all(
                                    left_factors.get(prime, 0)
                                    + right_factors.get(prime, 0)
                                    <= cap
                                    for prime, cap in factorial_caps.items()
                                )
                                product = n * n_plus_one
                                product_divides_factorial = (
                                    factorial_value % product == 0
                                )
                                if not (
                                    exponent_caps_hold and product_divides_factorial
                                ):
                                    failed = smooth_witness.copy()
                                    failed["product_divides_factorial"] = (
                                        product_divides_factorial
                                    )
                                    rejections["factorial_cap_exceeded"].add(failed)
                                    continue

                                capped_witness = smooth_witness.copy()
                                capped_witness["factorial_complement"] = (
                                    factorial_value // product
                                )
                                layers["full_factorial_caps"].add(capped_witness)

                                left_residual, left_residual_factors = residual(
                                    left_factors, previous_caps
                                )
                                right_residual, right_residual_factors = residual(
                                    right_factors, previous_caps
                                )
                                residuals_hold = (
                                    left_residual > 1
                                    and right_residual > 1
                                    and m % left_residual == 0
                                    and m % right_residual == 0
                                    and gcd(left_residual, right_residual) == 1
                                    and m % (left_residual * right_residual) == 0
                                )
                                residual_witness = capped_witness.copy()
                                residual_witness.update(
                                    {
                                        "left_residual": left_residual,
                                        "left_residual_factorization": (
                                            json_factorization(left_residual_factors)
                                        ),
                                        "right_residual": right_residual,
                                        "right_residual_factorization": (
                                            json_factorization(right_residual_factors)
                                        ),
                                    }
                                )
                                if not residuals_hold:
                                    rejections["residual_constraint_failed"].add(
                                        residual_witness
                                    )
                                    continue
                                layers["residual_constraints"].add(residual_witness)

                                complement = factorial_value // product
                                discriminant = 4 * (factorial_value // complement) + 1
                                root = isqrt(discriminant)
                                complement_holds = (
                                    factorial_value % complement == 0
                                    and root * root == discriminant
                                    and root == 2 * n + 1
                                )
                                complement_witness = residual_witness.copy()
                                complement_witness.update(
                                    {
                                        "complement_discriminant": discriminant,
                                        "complement_square_root": root,
                                    }
                                )
                                if not complement_holds:
                                    rejections["factorial_complement_failed"].add(
                                        complement_witness
                                    )
                                    continue
                                layers["factorial_complement_square"].add(
                                    complement_witness
                                )

                                common_fiber = (
                                    factorial_value % n == 0
                                    and factorial_value % n_plus_one == 0
                                    and previous_factorial % n != 0
                                    and previous_factorial % n_plus_one != 0
                                )
                                if not common_fiber:
                                    rejections["common_fiber_failed"].add(
                                        complement_witness
                                    )
                                    continue
                                layers["common_kempner_fiber"].add(
                                    complement_witness
                                )
                                unique_counterexamples.add((m, n))

    elapsed = perf_counter() - started
    print("search=ordered_distinct_controllers_c_ge_2")
    print(f"max_common_value={maximum}")
    print("search_complete=true")
    print(f"controller_pair_indices={total_pair_indices}")
    print(f"modular_searches={modular_searches}")
    print(f"cross_checked_modular_searches={cross_checked_searches}")
    print(f"mitm_half_divisors_materialized={total_mitm_half_divisors}")
    print(
        "summed_unbounded_other_divisor_space="
        f"{summed_unbounded_divisor_space}"
    )
    print(
        "unique_common_fiber_counterexamples="
        f"{len(unique_counterexamples)}"
    )
    print(f"elapsed_seconds={elapsed:.6f}")
    print("layer_order=" + ",".join(LAYER_NAMES))
    for name in LAYER_NAMES:
        observation = layers[name]
        print(f"layer.{name}.count={observation.count}")
        print(
            f"layer.{name}.smallest="
            + json.dumps(observation.smallest, sort_keys=True)
        )
    for name in REJECTION_NAMES:
        observation = rejections[name]
        print(f"rejection.{name}.count={observation.count}")
        print(
            f"rejection.{name}.smallest="
            + json.dumps(observation.smallest, sort_keys=True)
        )

    if unique_counterexamples:
        raise SystemExit(1)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Exhaustively search c>=2 ordered-controller Tutescu candidates "
            "with exact factorial and adjacency constraints."
        )
    )
    parser.add_argument(
        "--max-value",
        type=int,
        default=48,
        help="largest common Kempner value m to search (default: 48)",
    )
    parser.add_argument(
        "--cross-check-through",
        type=int,
        default=36,
        help=(
            "compare modular MITM output with naive divisor enumeration for "
            "all relevant m through this value (default: 36)"
        ),
    )
    args = parser.parse_args()
    if args.max_value < 2:
        parser.error("--max-value must be at least 2")
    if args.cross_check_through < 0:
        parser.error("--cross-check-through must be nonnegative")
    return args


if __name__ == "__main__":
    arguments = parse_args()
    run_search(arguments.max_value, arguments.cross_check_through)
