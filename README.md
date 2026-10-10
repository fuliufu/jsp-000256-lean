# jsp-000256-lean

Lean 4 formalization of the fundamental **Bleicher–Erdős constructive
reduction and divisor expansion framework** for **JSP-000256**
(Erdős problem #305, "Denominators of Unit Fractions").

![Lean CI](https://github.com/fuliufu/jsp-000256-lean/actions/workflows/lean.yml/badge.svg)

## Problem

> How small can the largest denominator be in a representation of a given
> positive rational number by distinct unit fractions?

Classical results (mathematical solution already established in the
literature):

- M. N. Bleicher and P. Erdős, *Denominators of Egyptian fractions*,
  J. Number Theory **8** (1976), 157–168.
- H. Yokota, *On a problem of Bleicher and Erdős*,
  J. Number Theory **30** (1988), 198–207.
- Liu & Sawhney, arXiv:2404.07113 (2024).

This repository provides a **machine-checked formalization** (Lean 4,
v4.34.1 with Mathlib) of the constructive algebraic core of that theory.

## Formalization scope

Formalized statements (all in `MyJspSolution/JSP000256.lean`, namespace
`JSP000256`, verified without `sorry` or custom axioms):

| Statement | Meaning |
|---|---|
| `IsEgyptianRep q S` | `S` is a valid expansion of `q` by distinct unit fractions with denominators `> 1` |
| `HasEgyptianRepBounded a b M` | `a/b` has an expansion whose denominators are all `≤ M` |
| `isEgyptianRep_union` | disjoint expansions merge into an expansion of the sum |
| `hasEgyptianRepBounded_add` | additive bound transfer: bound `max M₁ M₂` |
| `unit_fraction_split` | Sylvester splitting `1/n = 1/(n+1) + 1/(n(n+1))` |
| `bezout_fraction_decomp` | Bézout partial-fraction decomposition `a/(MN) = v/M + u/N` over `ℚ` |
| `div_over_self_eq_one_div` | divisor-to-fraction identity `d/N = 1/(N/d)` for `d ∣ N` |
| `div_injective_on_divisors` | the map `d ↦ N/d` is injective on divisors of `N` |
| `one_lt_div_of_dvd_lt` | proper divisors `d < N` yield denominators `N/d > 1` |
| `divisors_sum_to_egyptian` | **core bridge**: if `r = ∑ dᵢ` with distinct divisors `dᵢ ∣ N` and `r < N`, then `r/N` has a valid expansion with denominators `N/dᵢ` |
| `hasEgyptianRepBounded_of_divisor_sum` | **landing theorem**: such an `r/N` admits an expansion with all denominators `≤ N`, i.e. `D(r, N) ≤ N` |

The landing theorem is the machine-checked constructive core of
Bleicher–Erdős Lemma 1: any `r ≤ σ(N)` representable as a sum of distinct
divisors of `N` yields an Egyptian expansion of `r/N` with denominators
dividing `N` — hence bounded by `N`.

## Build & verify

Pinned toolchain: Lean `v4.34.1`, mathlib `v4.34.1`
(see `lean-toolchain` and `lake-manifest.json`).

```sh
lake build                      # 0 warnings, 0 errors
lake env lean Axioms.lean       # axiom audit: [propext, Classical.choice, Quot.sound]
```

## Statement of scope

This formalization covers the constructive algebraic reduction and divisor
expansion framework (Lemmas 1–2 level, and `D(r, N) ≤ N`). The full
asymptotic bound `D(N) ≤ K·N·(ln N)³` (Bleicher–Erdős Theorem 2) and its
prime-number-theorem refinements (Yokota 1990) are **not** formalized here.
