# Exact residual certificate at common value 130

Date: 2026-08-21

This is a reproducible exact computation, not a Lean proof.  It excludes a
Tutescu counterexample with common Kempner value `130` without using the
external `B=113` smooth-neighbor table.

## Program identity

Source: `scripts/search_residual_exact.cpp`

Build command, run from `/home/seanyang/Documents/math`:

```text
g++ -O3 -std=c++20 -Wall -Wextra -o /tmp/search_residual_exact KempnerResearch/scripts/search_residual_exact.cpp
```

Compiler: `g++ (Ubuntu 11.4.0-1ubuntu1~22.04.3) 11.4.0`

```text
source SHA-256  c8696b8008f7d930c02491a2933641a55a17c0ab646a9fb656a5edeaa590e29d
binary SHA-256  4ccf54f893723f84a5340911c4022ef1c484c783fe87f9de3fa8b45ca392b4a3
```

The production source was not changed after these hashes were recorded.
The built-in deterministic checks returned `self_test=passed`.  They compare
the compact meet-in-the-middle join with a naive product scan and separately
test mixed-radix enumeration, modular inverses, duplicate residues, both
equation signs, and exact big-integer reconstruction.  A complete small
production run at `M=12` also returned `search_complete=true` and zero exact
candidates.  Independent ASan/UBSan self-tests were run against the same
source and passed.

## Why the six scans are complete

Put `F=129!`.  A hypothetical pair with `S(n)=S(n+1)=130` has exact nontrivial
last-step residuals

```text
r = n/gcd(n,F),       s = (n+1)/gcd(n+1,F).
```

They are coprime and `rs | 130`.  Conversely, after saturating in `n` every
prime in `r` and in `n+1` every prime in `s`, all remaining prime powers come
from `F` and must be assigned disjointly to the two neighbors or to the
factorial complement.  Since `130=2*5*13`, the 12 ordered residual pairs form
the following six reversal groups:

```text
{2,5}, {2,13}, {2,65}, {5,13}, {5,26}, {10,13}.
```

For each group let `Csmall < Clarge` be the two saturated residual cores.  The
two possible orders of the consecutive neighbors are exactly

```text
Csmall*z == -1 (mod Clarge),
Csmall*z == +1 (mod Clarge),
```

where `z` ranges over every divisor of the remaining factorial prime-power
budget.  The program splits that budget into two unique mixed-radix halves,
stores every residue of one half, and probes every residue of the other half.
The 64-bit sieve modulus printed below divides `Clarge`, so every exact
solution must survive the join.  Hash fingerprints are only an accelerator:
every apparent hit is redecoded and compared by its exact residue, duplicate
residues are retained, and every surviving product is reconstructed with
exact unsigned big-integer arithmetic and checked against the full core,
disjoint support, factorial caps, and entry at `130` rather than `129`.

Thus an individual run with `search_complete=true` exhausts both ordered
orientations in its displayed reversal group.  The union of the six runs
exhausts all 12 residual pairs.

## Unconditional production runs

Every command below exited `0`, printed `search_complete=true`, and printed
`exact_common_fiber_candidates=0`.  `D` is the exact number of free divisors;
`table` and `probe` are the two half counts.

| residual group | command suffix | D | table | probe | sieve modulus | orientation results | elapsed | max RSS |
|---|---|---:|---:|---:|---:|---|---:|---:|
| `{2,5}` | `--value 130 --pair 2 5 --max-table-entries 700000000` | 61,353,228,238,848,000 | 203,212,800 | 301,916,160 | 9,223,372,036,854,775,808 | `0,0` sieve hits | 53.76 s | 3,149,056 KB |
| `{2,13}` | `--value 130 --pair 2 13 --max-table-entries 700000000` | 196,330,330,364,313,600 | 330,220,800 | 594,542,592 | 9,223,372,036,854,775,808 | `1,0` sieve hits; the one hit failed the full-core congruence | 152.23 s | 3,149,056 KB |
| `{2,65}` | `--value 130 --pair 2 65 --max-table-entries 700000000` | 6,135,322,823,884,800 | 69,672,960 | 88,058,880 | 9,223,372,036,854,775,808 | `0,0` sieve hits | 16.78 s | 789,760 KB |
| `{5,13}` | `--value 130 --pair 5 13 --max-table-entries 700000000` | 785,321,321,457,254,400 | 670,924,800 | 1,170,505,728 | 7,450,580,596,923,828,125 | `0,0` sieve hits | 332.07 s | 6,294,656 KB |
| `{5,26}` | `--value 130 --pair 5 26 --max-table-entries 700000000` | 6,135,322,823,884,800 | 69,672,960 | 88,058,880 | 4,625,763,390,369,824,768 | `0,0` sieve hits | 16.70 s | 789,760 KB |
| `{10,13}` | `--value 130 --pair 10 13 --max-table-entries 700000000` | 6,135,322,823,884,800 | 69,672,960 | 88,058,880 | 8,000,000,000,000,000,000 | `0,0` sieve hits | 17.57 s | 789,760 KB |

The scans cover `1,061,410,848,532,070,400` free-divisor allocations (two
orientation equations per allocation) through `3,744,518,400` compact
half-divisor insertions/probes.  Only one allocation survived even a 63-bit
sieve target, and it failed divisibility by the exact saturated core.  No
allocation reached the later smoothness or factorial filters.

## Conclusion

There is no pair of consecutive positive integers with common Kempner value
`130`.  In particular, the first `c>=2` value left open after the external
`B=113` lower bound is eliminated here by an independent exact computation;
the computation itself does not depend on that external table.
