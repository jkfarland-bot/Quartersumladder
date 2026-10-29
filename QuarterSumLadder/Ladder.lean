module

public import QuarterSumLadder.WeightTwo
public import QuarterSumLadder.Arith

@[expose] public section

/-!
# The ladder

For `p ≡ 1 (mod 8)` and a quartic `χ`, `Ω = x + iy` with `x = R₀ - R₂`, `y = R₁ - R₃` and
`N(Ω) = x² + y²`; by the relative class number formula `h⁻(K) = 2 N(Ω)` (not formalized).

* `four_term_expansion` (Lemma 5.1);
* `first_thresholds` (Theorem 5.2): `v_λ(Ω) = 1` if `χ(2) = -1`, `= 2` if `χ(2) = 1` and
  `p ≡ 9 (mod 16)`, `≥ 3` if `χ(2) = 1` and `p ≡ 1 (mod 16)`;
* `fourth_threshold` (Theorem 5.3) and `fourth_threshold_eval` (Theorem 5.4);
* `fifth_threshold` (Theorem 5.6).
-/

namespace QuarterSumLadder

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

/-- **The four-term expansion** (Paper IV, Lemma 5.1): with `z = i - 1`,
`Ω = Q + (R₁ + 2R₂ + 3R₃) z + (R₂ + 3R₃) z² + R₃ z³`. -/
theorem four_term_expansion :
    Omega χ = (Q p : GaussianInt) + ((R χ 1 + 2 * R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) +
      ((R χ 2 + 3 * R χ 3 : ℕ) : GaussianInt) * (gi - 1) ^ 2 +
        (R χ 3 : GaussianInt) * (gi - 1) ^ 3 := by
  have hs : (Q p : GaussianInt) = R χ 0 + R χ 1 + R χ 2 + R χ 3 := by
    rw [← sum_R hp8 hχ]; push_cast; ring
  have hO : Omega χ = (R χ 0 : GaussianInt) + R χ 1 * gi + R χ 2 * gi ^ 2 + R χ 3 * gi ^ 3 := by
    rw [gi_sq, gi_cube]; ext <;> simp [Omega, gi] <;> ring
  rw [hO, hs]; push_cast; ring

/-- The parities of the coordinates. -/
lemma coord_parity :
    (χ 2 = -1 → (Omega χ).re % 2 = 1 ∧ (Omega χ).im % 2 = 1) ∧
      (χ 2 = 1 → (Omega χ).re % 2 = 0 ∧ (Omega χ).im % 2 = 0 ∧
        ((Omega χ).re - (Omega χ).im) % 4 = (Q p : ℤ) % 4) := by
  have hs := sum_R hp8 hχ
  have hQ : 2 ∣ Q p := by have := mod_eight_aux hp8; unfold Q; omega
  have hre : (Omega χ).re = (R χ 0 : ℤ) - R χ 2 := rfl
  have him : (Omega χ).im = (R χ 1 : ℤ) - R χ 3 := rfl
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · have hq := quarter_law hp8 hχ
    rw [hw] at hq
    have hodd : Odd (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · rw [he.neg_one_pow] at hq; exact absurd hq (by decide)
      · exact ho
    obtain ⟨k, hk⟩ := hodd
    rw [hre, him]; omega
  · obtain ⟨h1, h2, h3⟩ := orbit_parity hp8 hχ hw
    rw [hre, him]; omega

/-- **The first three thresholds** (Paper IV, Theorem 5.2), in terms of `N(Ω) = x² + y²`. -/
theorem first_thresholds :
    (χ 2 = -1 → (2 : ℤ) ∣ (Omega χ).norm ∧ ¬ (4 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (4 : ℤ) ∣ (Omega χ).norm ∧ ¬ (8 : ℤ) ∣ (Omega χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (8 : ℤ) ∣ (Omega χ).norm) := by
  obtain ⟨hodd, heven⟩ := coord_parity hp8 hχ
  have hpq := mod_eight_aux hp8
  rw [norm_eq]
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 => ?_⟩
  · obtain ⟨hx, hy⟩ := hodd hw
    have := sq_add_sq_odd hx hy
    omega
  · obtain ⟨hx, hy, hxy⟩ := heven hw
    obtain ⟨h4, h8⟩ := even_even_eight hx hy
    refine ⟨h4, fun h => ?_⟩
    have := h8.1 h
    have hQ : (Q p : ℤ) % 4 = 2 := by unfold Q; omega
    omega
  · obtain ⟨hx, hy, hxy⟩ := heven hw
    obtain ⟨_, h8⟩ := even_even_eight hx hy
    refine h8.2 ?_
    have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
    omega

/-- **The fourth threshold** (Paper IV, Theorem 5.3): if `χ(2) = 1` and `p ≡ 1 (mod 16)`, then
`16 ∣ N(Ω) ⟺ R₁ + 2R₂ + R₃ ≡ 0 (mod 4)`. -/
theorem fourth_threshold (hw : χ 2 = 1) (h16 : p % 16 = 1) :
    (16 : ℤ) ∣ (Omega χ).norm ↔ (R χ 1 + 2 * R χ 2 + R χ 3) % 4 = 0 := by
  obtain ⟨hx, hy, hxy⟩ := (coord_parity hp8 hχ).2 hw
  have hs := sum_R hp8 hχ
  have hpq := mod_eight_aux hp8
  have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
  rw [norm_eq, sixteen_dvd_iff]
  have hre : (Omega χ).re = (R χ 0 : ℤ) - R χ 2 := rfl
  rw [hre] at hx hxy ⊢
  omega

/-- **The classical evaluation of the fourth threshold** (Paper IV, Theorem 5.4). If `χ(2) = 1`
and `p ≡ 1 (mod 16)`, then `4 ∣ κ` (that is, `8 ∣ h(-4p)`), and with `ρ = ord_p(2)`,
`16 ∣ N(Ω) ⟺ (Q - κ)/4 + (p - 1)/8 + [2 ∣ ρ] (p - 1)/(4ρ) ≡ 0 (mod 2)`. Here
`(Q - κ)/4 = (p - 1 - 2h(-4p))/16`. -/
theorem fourth_threshold_eval (hw : χ 2 = 1) (h16 : p % 16 = 1) :
    (4 : ℤ) ∣ kappa p ∧
      ((16 : ℤ) ∣ (Omega χ).norm ↔
        (((Q p : ℤ) - kappa p) / 4 + ((p - 1) / 8 : ℕ) +
          ((if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0 : ℕ) :
            ℤ)) % 2 = 0) := by
  have hk := kappa_eq hp8 hχ
  have hq := quarter_law hp8 hχ
  rw [hw] at hq
  have heven : Even (R χ 1 + R χ 3) := by
    rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
    · exact he
    · rw [ho.neg_one_pow] at hq; exact absurd hq (by decide)
  obtain ⟨j, hj⟩ := heven
  have hpq := mod_eight_aux hp8
  have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
  have hR2 := R_two_parity hp8 hχ hw
  have hρ := parity_rho hp8 hχ hw
  have h4 := fourth_threshold hp8 hχ hw h16
  set ι := (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0)
  set δ := (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0)
  have hδ : δ ≤ 1 := by simp only [δ]; split_ifs <;> omega
  refine ⟨⟨((Q p : ℤ) / 4) - j, by rw [hk]; push_cast [hj]; omega⟩, ?_⟩
  rw [h4, hk]
  have : ((Q p : ℤ) - ((Q p : ℤ) - 2 * ((R χ 1 : ℤ) + R χ 3))) / 4 = j := by
    have : ((R χ 1 : ℤ) + R χ 3) = j + j := by exact_mod_cast hj
    rw [this]; omega
  rw [this]
  omega

/-- **The fifth threshold** (Paper IV, Theorem 5.6), with `h = 2 N(Ω)` (`= h⁻(K)`): `64 ∣ h` iff
`32 ∣ h` and `R₂ + R₃ ≡ Q/2 (mod 4)`; and, given `32 ∣ h`, `64 ∣ h ⟺ x + y ≡ 0 (mod 8)`. -/
theorem fifth_threshold :
    ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔
        (32 : ℤ) ∣ 2 * (Omega χ).norm ∧ ((R χ 2 + R χ 3 : ℕ) : ℤ) % 4 = ((Q p / 2 : ℕ) : ℤ) % 4) ∧
      ((32 : ℤ) ∣ 2 * (Omega χ).norm →
        ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (8 : ℤ) ∣ (Omega χ).re + (Omega χ).im)) := by
  have hs := sum_R hp8 hχ
  have hpq := mod_eight_aux hp8
  have hQ : 2 ∣ Q p := by unfold Q; omega
  have hxy : (Omega χ).re + (Omega χ).im = (Q p : ℤ) - 2 * ((R χ 2 : ℤ) + R χ 3) := by
    show ((R χ 0 : ℤ) - R χ 2) + ((R χ 1 : ℤ) - R χ 3) = _
    have : (R χ 0 + R χ 1 + R χ 2 + R χ 3 : ℤ) = Q p := by exact_mod_cast hs
    linarith
  have h32 : (32 : ℤ) ∣ 2 * (Omega χ).norm ↔ (16 : ℤ) ∣ (Omega χ).norm := by omega
  have h64 : (64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (32 : ℤ) ∣ (Omega χ).norm := by omega
  have key : (32 : ℤ) ∣ 2 * (Omega χ).norm →
      ((64 : ℤ) ∣ 2 * (Omega χ).norm ↔ (8 : ℤ) ∣ (Omega χ).re + (Omega χ).im) := by
    intro h
    rw [h32, norm_eq, sixteen_dvd_iff] at h
    rw [h64, norm_eq]
    exact thirtytwo_dvd_iff h.1 h.2
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, key⟩
  · have h' : (32 : ℤ) ∣ 2 * (Omega χ).norm := by omega
    refine ⟨h', ?_⟩
    have := (key h').1 h
    rw [hxy] at this
    obtain ⟨k, hk⟩ := hQ
    push_cast [hk]; omega
  · refine (key h.1).2 ?_
    rw [hxy]
    obtain ⟨k, hk⟩ := hQ
    have := h.2; push_cast [hk] at this ⊢; omega

end Quartic

end QuarterSumLadder
