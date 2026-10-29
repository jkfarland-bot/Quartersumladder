module

public import Mathlib

public section

/-!
# The quarter-sum ladder: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `QuarterSumLadder/`. The numbering follows the paper (Farland, *The even quartic class:
weight-two congruences, the quarter-sum ladder, and 2-primary class groups*, Paper IV).

Throughout `p ≡ 1 (mod 8)` is prime, `χ` is a quartic character modulo `p` with values in `ℤ[i]`,
`x.val` is the least nonnegative residue of `x : ZMod p`, `gi = i`, `Q = (p - 1)/4`,
`R_r = #{0 < n < p/4 : χ(n) = i^r}`, `Ω = x + iy` with `x = R₀ - R₂`, `y = R₁ - R₃`, and
`B_{2,χ} = c₀ + i c₁`. For `z ∈ ℤ[i]`, `z.norm = z.re² + z.im²` and `v_λ(z) = v₂(z.norm)`.
-/

namespace QuarterSumLadder

open Finset

/-! ### Definitions -/

/-- The Gaussian unit `i`. -/
def gi : GaussianInt := ⟨0, 1⟩

section Defs

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- The class `D_z = {x : χ(x) = z}`. -/
def fiber (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : Finset (ZMod p) :=
  univ.filter fun x => χ x = z

/-- `U_z = ∑_{x ∈ D_z} ⟨x⟩²`. -/
def U (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ :=
  ∑ x ∈ fiber χ z, (x.val : ℤ) ^ 2

/-- The real coordinate `c₀ = (U₁ - U₋₁)/p` of `B_{2,χ}`. -/
def c0 (χ : MulChar (ZMod p) GaussianInt) : ℤ := (U χ 1 - U χ (-1)) / p

/-- The imaginary coordinate `c₁ = (U_i - U_{-i})/p` of `B_{2,χ}`. -/
def c1 (χ : MulChar (ZMod p) GaussianInt) : ℤ := (U χ gi - U χ (-gi)) / p

/-- `B_{2,χ} = c₀ + i c₁`. -/
def B2 (χ : MulChar (ZMod p) GaussianInt) : GaussianInt := ⟨c0 χ, c1 χ⟩

/-- `T₂(χ) = ∑_{0 < m < p} χ(m) m² = p B_{2,χ}`. -/
def T2 (χ : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ∑ x : ZMod p, χ x * (((x.val : ℤ) ^ 2 : ℤ) : GaussianInt)

/-- `E_z = #{0 < m < p : m ≡ 2 (mod 4), χ(m) = z}`. -/
def E (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℕ :=
  ((fiber χ z).filter fun x => x.val % 4 = 2).card

/-- The quarter count `R_r = #{0 < n < p/4 : χ(n) = i^r}`. -/
def R (χ : MulChar (ZMod p) GaussianInt) (r : ℕ) : ℕ :=
  ((range p).filter fun n => 0 < n ∧ 4 * n < p ∧ χ (n : ZMod p) = gi ^ r).card

/-- The quarter sum `Ω = R₀ - R₂ + i (R₁ - R₃) = ∑_{0 < n < p/4} χ(n)`. -/
def Omega (χ : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ⟨(R χ 0 : ℤ) - R χ 2, (R χ 1 : ℤ) - R χ 3⟩

/-- `Q = (p - 1)/4`. -/
def Q (p : ℕ) : ℕ := (p - 1) / 4

/-- `κ = ∑_{0 < n < p/4} (n/p)`, which is `h(-4p)/2` by Dirichlet's class number formula. -/
def kappa (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), legendreSym p n

/-- `v_λ(z) = v₂(z z̄)` for `λ = 1 + i`. -/
def vlam (z : GaussianInt) : ℕ := padicValInt 2 z.norm

end Defs

/-! ### Statements -/

section Statements

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The setting** (Paper IV, §2). For `p ≡ 1 (mod 8)` a quartic `χ` is even, `w = χ(2) = ±1`, and
`w = 1` exactly when `2` is a fourth power modulo `p`. -/
theorem even_quartic_setting {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    χ (-1) = 1 ∧ (χ 2 = 1 ∨ χ 2 = -1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) := by
  sorry

/-- Each class `D_z` (`z ∈ {1, i, -1, -i}`) has `Q = (p - 1)/4` elements, and `R₀ + R₁ + R₂ + R₃ = Q`. -/
theorem class_sizes {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) {z : GaussianInt}
    (hz : (z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi)) :
    (fiber χ z).card = Q p ∧ R χ 0 + R χ 1 + R χ 2 + R χ 3 = Q p := by
  sorry

/-- **The coordinates of `B_{2,χ}` are integers** (proof of Theorem 3.1): `p ∣ U_z`, `p c₀ = U₁ - U₋₁`,
`p c₁ = U_i - U_{-i}`, and `∑_{0<m<p} χ(m) m² = p B_{2,χ}`. -/
theorem weight_two_integrality {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (∀ z : GaussianInt, (p : ℤ) ∣ U χ z) ∧ (p : ℤ) * c0 χ = U χ 1 - U χ (-1) ∧
      (p : ℤ) * c1 χ = U χ gi - U χ (-gi) ∧ T2 χ = (p : GaussianInt) * B2 χ := by
  sorry

/-- **The coefficientwise weight-two congruence** (Paper IV, Theorem 3.1, at order `M = 4`):
`c₀ ≡ 4(E₁ + E₋₁)`, `c₁ ≡ 4(E_i + E_{-i})` and `c₀ + c₁ ≡ p - 1 (mod 8)`. -/
theorem weight_two_coefficient_congruence {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    c0 χ ≡ 4 * (E χ 1 + E χ (-1)) [ZMOD 8] ∧ c1 χ ≡ 4 * (E χ gi + E χ (-gi)) [ZMOD 8] ∧
      c0 χ + c1 χ ≡ p - 1 [ZMOD 8] := by
  sorry

/-- **The mod-8 criterion** (Paper IV, Theorem 3.2, without Gauss's criterion `p = a² + 64b²`):
`8 ∣ c₀ ∧ 8 ∣ c₁ ⟺ χ(2) = 1 ⟺ 2` is a fourth power modulo `p`; moreover `c₀ ≡ c₁ ≡ 4(R₁ + R₃) (mod 8)`. -/
theorem weight_two_mod_eight {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ((8 : ℤ) ∣ c0 χ ∧ (8 : ℤ) ∣ c1 χ ↔ χ 2 = 1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) ∧
      c0 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] ∧ c1 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] := by
  sorry

/-- **The Gauss–Lehmer product** (the input to the quartic Gauss lemma): if `A` is a set of nonzero
elements of the half system `0 < ⟨x⟩ < p/2` stable under `x ↦ 2x` (for `⟨x⟩ < p/4`) and
`x ↦ -2x` (otherwise), then `2^{|A|} (-1)^{#\{x ∈ A : ⟨x⟩ > p/4\}} = 1` in `ZMod p`. -/
theorem gauss_lehmer_product (hp2 : p ≠ 2) (A : Finset (ZMod p))
    (hA : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p)
    (hφ : ∀ x ∈ A, (if 4 * x.val < p then 2 * x else -(2 * x)) ∈ A) :
    (2 : ZMod p) ^ A.card * (-1) ^ (A.filter fun x => ¬ 4 * x.val < p).card = 1 := by
  sorry

/-- **The quartic Gauss lemma** (Williams–Currie; proof of Theorem 3.2): `2^Q = (-1)^{R₁ + R₃}` in
`ZMod p`, so `χ(2) = (-1)^{R₁ + R₃}`. -/
theorem quartic_gauss_lemma {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (2 : ZMod p) ^ Q p = (-1) ^ (R χ 1 + R χ 3) ∧ χ 2 = (-1) ^ (R χ 1 + R χ 3) := by
  sorry

/-- **The quarter-interval formula** in counting form (after Theorem 3.2): `κ = ∑_{0<n<p/4} (n/p)`
equals `Q - 2(R₁ + R₃)`, and `χ(2) = 1 ⟺ κ ≡ Q (mod 4)`. With `h(-4p) = 2κ` (Dirichlet's class
number formula, not formalized) this is `w = 1 ⟺ h(-4p) ≡ (p - 1)/2 (mod 8)`. -/
theorem quarter_interval_formula {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    kappa p = (Q p : ℤ) - 2 * (R χ 1 + R χ 3) ∧ (χ 2 = 1 ↔ kappa p % 4 = (Q p : ℤ) % 4) := by
  sorry

/-- **Doubling-orbit parity** (Paper IV, Theorem 3.3): if `χ(2) = 1`, then
`R₀ ≡ R₁ ≡ R₂ ≡ R₃ (mod 2)`. -/
theorem doubling_orbit_parity {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1) :
    R χ 1 % 2 = R χ 0 % 2 ∧ R χ 2 % 2 = R χ 0 % 2 ∧ R χ 3 % 2 = R χ 0 % 2 := by
  sorry

/-- **The excluded patterns** (Paper IV, Corollary 3.4, first statement): the parity vector of
`(R₀, R₁, R₂, R₃)` is never `1010` or `0101`. -/
theorem parity_patterns {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ¬ (R χ 0 % 2 = 1 ∧ R χ 1 % 2 = 0 ∧ R χ 2 % 2 = 1 ∧ R χ 3 % 2 = 0) ∧
      ¬ (R χ 0 % 2 = 0 ∧ R χ 1 % 2 = 1 ∧ R χ 2 % 2 = 0 ∧ R χ 3 % 2 = 1) := by
  sorry

/-- **The four-term expansion** (Paper IV, Lemma 5.1): with `z = i - 1`,
`Ω = Q + (R₁ + 2R₂ + 3R₃) z + (R₂ + 3R₃) z² + R₃ z³`. -/
theorem quarter_sum_expansion {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    Omega χ = (Q p : GaussianInt) + ((R χ 1 + 2 * R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) +
      ((R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) ^ 2 +
        (R χ 3 : GaussianInt) * (gi - 1) ^ 3 := by
  sorry

/-- **The first three thresholds** (Paper IV, Theorem 5.2), with `N(Ω) = x² + y²`: `2 ∥ N(Ω)` if
`χ(2) = -1`; `4 ∥ N(Ω)` if `χ(2) = 1`, `p ≡ 9 (mod 16)`; `8 ∣ N(Ω)` if `χ(2) = 1`, `p ≡ 1 (mod 16)`. -/
theorem ladder_bottom {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → (2 : ℤ) ∣ (Omega χ).norm ∧ ¬ (4 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (4 : ℤ) ∣ (Omega χ).norm ∧ ¬ (8 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (8 : ℤ) ∣ (Omega χ).norm) := by
  sorry

/-- **The first three thresholds** (Paper IV, Theorem 5.2) for `v_λ(Ω) = v₂(N(Ω))`: `1`, `2`, and `≥ 3`
(the last for `Ω ≠ 0`). -/
theorem ladder_bottom_valuation {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → vlam (Omega χ) = 1) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (Omega χ) = 2) ∧
      (χ 2 = 1 → p % 16 = 1 → Omega χ ≠ 0 → 3 ≤ vlam (Omega χ)) := by
  sorry

/-- **The fourth threshold** (Paper IV, Theorem 5.3): if `χ(2) = 1` and `p ≡ 1 (mod 16)`, then
`16 ∣ N(Ω) ⟺ R₁ + 2R₂ + R₃ ≡ 0 (mod 4)`. -/
theorem ladder_fourth {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1)
    (h16 : p % 16 = 1) :
    (16 : ℤ) ∣ (Omega χ).norm ↔ (R χ 1 + 2 * R χ 2 + R χ 3) % 4 = 0 := by
  sorry

/-- **The classical evaluation of the fourth threshold** (Paper IV, Theorem 5.4): if `χ(2) = 1` and
`p ≡ 1 (mod 16)`, then `4 ∣ κ` and, with `ρ = ord_p(2)`,
`16 ∣ N(Ω) ⟺ (Q - κ)/4 + (p - 1)/8 + [2 ∣ ρ] (p - 1)/(4ρ) ≡ 0 (mod 2)`. -/
theorem ladder_fourth_classical {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1)
    (h16 : p % 16 = 1) :
    (4 : ℤ) ∣ kappa p ∧
      ((16 : ℤ) ∣ (Omega χ).norm ↔
        (((Q p : ℤ) - kappa p) / 4 + ((p - 1) / 8 : ℕ) +
          ((if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0 : ℕ) :
            ℤ)) % 2 = 0) := by
  sorry

/-- **The parity of `R₂`** (proof of Theorem 5.4): if `χ(2) = 1`, then
`R₂ ≡ (p - 1)/8 + [2^{(p-1)/8} = -1] (mod 2)`, and `[2^{(p-1)/8} = -1] ≡ [2 ∣ ρ] (p - 1)/(4ρ) (mod 2)`. -/
theorem second_quarter_parity {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) (hw : χ 2 = 1) :
    R χ 2 % 2 = ((p - 1) / 8 + if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 ∧
      (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 =
        (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0) % 2 := by
  sorry

/-- **The coordinate valuation** (Paper IV, Lemma 5.5): for `x, y ≠ 0`,
`v₂(x² + y²) = 2 min(v₂ x, v₂ y) + [v₂ x = v₂ y]`. -/
theorem coordinate_valuation_formula {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValInt 2 (x ^ 2 + y ^ 2) =
      2 * min (padicValInt 2 x) (padicValInt 2 y) +
        if padicValInt 2 x = padicValInt 2 y then 1 else 0 := by
  sorry

/-- **The fifth threshold** (Paper IV, Theorem 5.6), with `h = 2N(Ω)` (`= h⁻(K)` by Proposition 4.1,
not formalized): `64 ∣ h ⟺ 32 ∣ h ∧ R₂ + R₃ ≡ Q/2 (mod 4)`; and given `32 ∣ h`,
`64 ∣ h ⟺ x + y ≡ 0 (mod 8)`. -/
theorem ladder_fifth {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔
        (32 : ℤ) ∣ 2 * (Omega χ).norm ∧ ((R χ 2 + R χ 3 : ℕ) : ℤ) % 4 = ((Q p / 2 : ℕ) : ℤ) % 4) ∧
      ((32 : ℤ) ∣ 2 * (Omega χ).norm →
        ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (8 : ℤ) ∣ (Omega χ).re + (Omega χ).im)) := by
  sorry

/-- **The comparison lemma** (Paper IV, Lemma 8.1): `p(c₀ - c₁) ≡ -4(x - y) (mod 16)`. The paper
assumes `χ(2) = 1`; the congruence holds without it. -/
theorem weight_two_comparison {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (p : ℤ) * (c0 χ - c1 χ) ≡ -4 * ((Omega χ).re - (Omega χ).im) [ZMOD 16] := by
  sorry

/-- **The weight-two trichotomy** (Paper IV, Theorem 8.2), with `N(B₂) = c₀² + c₁²`: `32 ∥ N(B₂)` if
`χ(2) = -1`; `64 ∥ N(B₂)` if `χ(2) = 1`, `p ≡ 9 (mod 16)`; `128 ∣ N(B₂)` if `χ(2) = 1`, `p ≡ 1 (mod 16)`. -/
theorem weight_two_trichotomy {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → (32 : ℤ) ∣ (B2 χ).norm ∧ ¬ (64 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (64 : ℤ) ∣ (B2 χ).norm ∧ ¬ (128 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (128 : ℤ) ∣ (B2 χ).norm) := by
  sorry

/-- **The weight-two trichotomy** (Paper IV, Theorem 8.2) for `v_λ(B_{2,χ})`: `5`, `6`, and `≥ 7`
(the last for `B_{2,χ} ≠ 0`). -/
theorem weight_two_trichotomy_valuation {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    (χ 2 = -1 → vlam (B2 χ) = 5) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (B2 χ) = 6) ∧
      (χ 2 = 1 → p % 16 = 1 → B2 χ ≠ 0 → 7 ≤ vlam (B2 χ)) := by
  sorry

end Statements

end QuarterSumLadder
