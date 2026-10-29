# QuarterSumLadder

Lean 4 / Mathlib formalization of the elementary part of J. S. Farland, *The even quartic class:
weight-two congruences, the quarter-sum ladder, and 2-primary class groups* (Paper IV of the
author's series). It continues [BandParity](https://github.com/jkfarland-bot/bandparity),
[BandParityTower](https://github.com/jkfarland-bot/Bandparitytower) (Paper I) and
[MellinDuality](https://github.com/jkfarland-bot/MellinDuality) (Paper II).

The companion paper is J. S. Farland, *The quarter-sum ladder and the weight-two congruences,
formalized in Lean* (preprint, Zenodo, 2026; DOI to be added).

Let `p ≡ 1 (mod 8)` be prime and `χ` a quartic character modulo `p` with values in `ℤ[i]`. Then `χ`
is even and `w = χ(2) = ±1`. Put `Q = (p - 1)/4`, `R_r = #{0 < n < p/4 : χ(n) = i^r}`, the quarter sum
`Ω = ∑_{0<n<p/4} χ(n) = x + iy` (`x = R₀ - R₂`, `y = R₁ - R₃`), and
`B_{2,χ} = p⁻¹ ∑_{0<m<p} χ(m) m² = c₀ + i c₁`. By Barkan's evaluation and the relative class number
formula, `2(x² + y²) = h⁻(K)` for the imaginary cyclic quartic field `K` of conductor `4p` (quoted, not
formalized). This repository proves:

- **Weight two** (Theorems 3.1 at order 4, 3.2). `c₀, c₁ ∈ ℤ`, `c₀ ≡ 4(E₁ + E₋₁)`,
  `c₁ ≡ 4(E_i + E_{-i})`, `c₀ + c₁ ≡ p - 1 (mod 8)`, with `E_z` the number of `m ≡ 2 (mod 4)` in the
  class `χ(m) = z`; `c₀ ≡ c₁ ≡ 4(R₁ + R₃) (mod 8)`; and `8 ∣ c₀, c₁ ⟺ w = 1 ⟺ 2` is a fourth power.
- **The Gauss–Lehmer product** and its consequences: the quartic Gauss lemma
  `2^Q = (-1)^{R₁+R₃}` in `ZMod p` and `w = (-1)^{R₁+R₃}`; the quarter-interval count
  `κ = ∑_{0<n<p/4} (n/p) = Q - 2(R₁ + R₃)` and `w = 1 ⟺ κ ≡ Q (mod 4)`; if `w = 1`,
  `R₀ ≡ R₁ ≡ R₂ ≡ R₃ (mod 2)` (Theorem 3.3) and `R₂ ≡ (p-1)/8 + [2 ∣ ρ](p-1)/(4ρ) (mod 2)` with
  `ρ = ord_p(2)`; the parity patterns `1010` and `0101` never occur (Corollary 3.4).
- **The ladder** (Lemma 5.1, Theorems 5.2 to 5.4, Lemma 5.5, Theorem 5.6). The four-term expansion of
  `Ω` in powers of `i - 1`; `2 ∥ N(Ω)`, `4 ∥ N(Ω)`, `8 ∣ N(Ω)` in the cases `w = -1`; `w = 1`,
  `p ≡ 9 (mod 16)`; `w = 1`, `p ≡ 1 (mod 16)`; in the last case `16 ∣ N(Ω) ⟺ R₁ + 2R₂ + R₃ ≡ 0 (mod 4)`,
  and its evaluation through `κ`, `(p - 1)/8` and `ρ`; `v₂(x² + y²) = 2 min(v₂x, v₂y) + [v₂x = v₂y]`;
  `64 ∣ 2N(Ω) ⟺ 32 ∣ 2N(Ω) ∧ R₂ + R₃ ≡ Q/2 (mod 4)`.
- **Weight two beyond the first rung** (Lemma 8.1, Theorem 8.2).
  `p(c₀ - c₁) ≡ -4(x - y) (mod 16)`, and `v_λ(B_{2,χ})` is `5`, `6`, `≥ 7` in the three cases.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
```

No `sorry`, no `native_decide`. Every result depends only on `propext`, `Classical.choice` and
`Quot.sound`. The export of `Solution` is accepted by the Lean kernel, nanoda and con-ron.

## Scope, hypotheses and limitations

- The thresholds are stated as divisibility of `N(Ω) = x² + y²` and `N(B₂) = c₀² + c₁²`, since
  `padicValInt 2 0 = 0`. The valuation forms give the exact values `1, 2` and `5, 6` without
  hypotheses, and the lower bounds `3` and `7` under `Ω ≠ 0` and `B_{2,χ} ≠ 0`. These always hold
  (`h⁻(K) ≠ 0`, `L(-1, χ) ≠ 0`), but proving them needs analytic input that is not formalized.
- `w = 1` is the hypothesis `χ 2 = 1`, proved equivalent to `2` being a fourth power in `ZMod p`.
  Gauss's criterion `p = a² + 64b²` is not formalized.
- `κ` is the Legendre sum over `(0, p/4)`, and the fifth threshold is stated for `2N(Ω)`. The
  identifications `κ = h(-4p)/2` and `2N(Ω) = h⁻(K)` are not formalized and are not used.
- Theorem 3.1 is formalized at order 4 only; `c₀` and `c₁` are defined with integer division, and
  `weight_two_integrality` shows the division is exact and `T₂ = p B₂`.
- The comparison lemma (Lemma 8.1) is proved without the hypothesis `w = 1` that the paper states.
- The parity statements come from the Gauss–Lehmer product applied class by class rather than from
  doubling orbits; the thresholds are proved from the coordinates rather than the term valuations.
- Not formalized: Gauss's criterion; Proposition 4.1 (Barkan's evaluation `B_{1,Θ} = -2Ω` and the class
  number formula); Theorem 3.1 for order `2^b ≥ 8` and the octic part of Corollary 3.4; the pattern
  witnesses; the 2-class group (Theorem 6.1, Corollary 6.2), which needs class field theory; the witness
  pairs of Section 7 (Theorem 7.1), which need class numbers; the counterexample at `p = 337`, the
  questions and the observations.

## Sources and novelty

The quartic Gauss lemma `w = (-1)^{R₁+R₃}` and the criterion `w = 1 ⟺ h(-4p) ≡ (p-1)/2 (mod 8)` are
classical (Barrucand and Cohn 1969; E. Brown, Proc. AMS 31 (1972); Williams and Currie, Canad. J.
Math. 34 (1982), whose count of the nonresidues in `(0, p/4)` is `R₁ + R₃`). The product argument is
E. Lehmer's (*Generalizations of Gauss's lemma*, 1977). Through `h⁻(K) = 2N(Ω)`, the first three
thresholds (Theorem 5.2) are the corollary to Theorem 4 of Brown and Parry, *The 2-class group of
biquadratic fields II*, Pacific J. Math. 78 (1978), for the field `Q(√(-ε√p))`, which is `K`; what is
formalized here is the elementary form in the quarter counts, and no priority is claimed for it. The
parity statement (Theorem 3.3) follows from the Gauss lemma, Brown and Parry and Barkan's formula; it
was not found stated. The integrality of `B_{2,χ}` is standard (Carlitz 1959). Not found in the sources
searched: the weight-two congruences of Theorems 3.1 and 3.2, the criteria at the fourth and fifth
thresholds (Theorems 5.3, 5.4, 5.6), and the explicit comparison modulo 16 (Lemma 8.1); the valuations
of Theorem 8.2 can also be reached from the 2-adic Kummer congruence together with Brown and Parry.
Ichimura and Sumida-Takahashi treat the parallel case of conductor `8p` (Tokyo J. Math. 44 (2021)).
Ma, Li and Zhang, *Congruence formulae modulo powers of 2 for class numbers of cyclic quartic fields*,
Sci. China Ser. A 52 (2009), was not accessible and may overlap with the ladder. All novelty claims are
relative to the sources searched.

## Authorship, AI assistance and licence

The mathematics, the statements and the paper are by Joseph S. Farland. The Lean code was drafted
and repaired by Claude (Anthropic) against the paper's statements and proofs. The code is released
under the Apache License 2.0 (`LICENSE`); the paper is CC BY 4.0.

## Layout for the Palomar registry

- `Challenge.lean` is the statement surface to audit. It restates the definitions exactly as the
  development has them and states the 21 results with `sorry`.
- `Solution.lean` proves the same declarations from the development in `QuarterSumLadder/`.
- `comparator.json` lists the compared theorems and definitions and the permitted axioms.
- `formalization.yaml` records authorship, sources, AI assistance, scope and fidelity.
- `scripts/` holds Palomar's checks, copied from the Palomar starter template.
- `check/statements.py` recomputes every formalized statement numerically (both quartic characters,
  all 556 primes `p ≡ 1 (mod 8)` below `2·10⁴`).

```
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap (bwrap)
```

| Paper IV | Challenge declaration |
|---|---|
| §2 | `even_quartic_setting`, `class_sizes` |
| Theorem 3.1 (order 4) | `weight_two_integrality`, `weight_two_coefficient_congruence` |
| Theorem 3.2 and its proof | `weight_two_mod_eight`, `gauss_lehmer_product`, `quartic_gauss_lemma` |
| after Theorem 3.2 | `quarter_interval_formula` |
| Theorem 3.3 | `doubling_orbit_parity` |
| Corollary 3.4 | `parity_patterns` |
| Lemma 5.1 | `quarter_sum_expansion` |
| Theorem 5.2 | `ladder_bottom`, `ladder_bottom_valuation` |
| Theorem 5.3 | `ladder_fourth` |
| Theorem 5.4 and its proof | `ladder_fourth_classical`, `second_quarter_parity` |
| Lemma 5.5 | `coordinate_valuation_formula` |
| Theorem 5.6 | `ladder_fifth` |
| Lemma 8.1 | `weight_two_comparison` |
| Theorem 8.2 | `weight_two_trichotomy`, `weight_two_trichotomy_valuation` |

## Files

| File | Contents |
|---|---|
| `Basic` | quartic characters with values in `ℤ[i]`, copied from the earlier repositories |
| `Defs` | the definitions |
| `Prelim` | the Gauss map and the Gauss–Lehmer product |
| `Classes` | sizes of the classes, their halves and their odd and even parts |
| `Counts` | the quartic Gauss lemma, doubling parity, the parity of `R₂`, `κ` |
| `WeightTwo` | Theorems 3.1 (order 4) and 3.2 |
| `Arith` | sums of two squares modulo powers of 2, Lemma 5.5 |
| `Ladder` | Lemma 5.1, Theorems 5.2 to 5.4 and 5.6 |
| `Boundary` | Lemma 8.1, Theorem 8.2, the valuation forms |
