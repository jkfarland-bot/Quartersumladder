module

public import Mathlib
public import QuarterSumLadder.Basic

@[expose] public section

/-!
# The quarter-sum ladder: definitions

Throughout `p ≡ 1 (mod 8)` is prime and `χ` is a quartic character modulo `p` with values in
`ℤ[i]` (Farland, *The even quartic class*, Paper IV). Then `χ` is even, `B_{1,χ} = 0`, and the
objects studied are the weight-two Bernoulli number `B_{2,χ} = c₀ + i c₁` and the quarter sum
`Ω = ∑_{0 < n < p/4} χ(n) = R₀ + i R₁ - R₂ - i R₃`.
-/

namespace QuarterSumLadder

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

end QuarterSumLadder
