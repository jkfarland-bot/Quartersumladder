module

public import Mathlib

@[expose] public section

/-!
# Sums of two squares modulo powers of two

Elementary facts about `x² + y²` for integers, used for the thresholds of the ladder, and the
coordinate-valuation lemma (Paper IV, Lemma 5.5): for `x, y ≠ 0`,
`v₂(x² + y²) = 2 min(v₂ x, v₂ y) + [v₂ x = v₂ y]`.
-/

namespace QuarterSumLadder

lemma sq_mod_two (a : ℤ) : a ^ 2 % 2 = a % 2 := by
  rcases Int.even_or_odd a with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have : (r + r) ^ 2 = 2 * (2 * r ^ 2) := by ring
    rw [this]; omega
  · have : (2 * r + 1) ^ 2 = 2 * (2 * r ^ 2 + 2 * r) + 1 := by ring
    rw [this]; omega

lemma sq_odd_mod_eight {a : ℤ} (ha : a % 2 = 1) : a ^ 2 % 8 = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, a = 2 * r + 1 := ⟨a / 2, by omega⟩
  have h : (2 * r + 1) ^ 2 = 4 * (r * (r + 1)) + 1 := by ring
  obtain ⟨s, hs⟩ := Int.even_mul_succ_self r
  rw [h, hs]; omega

lemma sq_add_sq_odd {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 1) : (x ^ 2 + y ^ 2) % 8 = 2 := by
  have := sq_odd_mod_eight hx; have := sq_odd_mod_eight hy; omega

lemma sq_add_sq_mixed {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 0) : (x ^ 2 + y ^ 2) % 2 = 1 := by
  have := sq_mod_two x; have := sq_mod_two y; omega

/-- For even `x, y`: `x² + y² = 4((x/2)² + (y/2)²)`. -/
lemma sq_add_sq_even {x y : ℤ} (hx : x % 2 = 0) (hy : y % 2 = 0) :
    x ^ 2 + y ^ 2 = 4 * ((x / 2) ^ 2 + (y / 2) ^ 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
  rw [Int.mul_ediv_cancel_left _ two_ne_zero, Int.mul_ediv_cancel_left _ two_ne_zero]; ring

/-- For even `x, y`: `4 ∣ x² + y²`, and `8 ∣ x² + y² ↔ 4 ∣ x - y`. -/
lemma even_even_eight {x y : ℤ} (hx : x % 2 = 0) (hy : y % 2 = 0) :
    (4 : ℤ) ∣ x ^ 2 + y ^ 2 ∧ ((8 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (4 : ℤ) ∣ x - y) := by
  rw [sq_add_sq_even hx hy]
  refine ⟨dvd_mul_right 4 _, ?_⟩
  have h1 := sq_mod_two (x / 2); have h2 := sq_mod_two (y / 2)
  omega

/-- `16 ∣ x² + y² ↔ 4 ∣ x ∧ 4 ∣ y`. -/
lemma sixteen_dvd_iff (x y : ℤ) : (16 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (4 : ℤ) ∣ x ∧ (4 : ℤ) ∣ y := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · rw [sq_add_sq_even hx hy]
    have h1 := sq_mod_two (x / 2); have h2 := sq_mod_two (y / 2)
    rcases Int.emod_two_eq_zero_or_one (x / 2) with ha | ha <;>
      rcases Int.emod_two_eq_zero_or_one (y / 2) with hb | hb
    · obtain ⟨a, ha'⟩ : ∃ a, x / 2 = 2 * a := ⟨x / 2 / 2, by omega⟩
      obtain ⟨b, hb'⟩ : ∃ b, y / 2 = 2 * b := ⟨y / 2 / 2, by omega⟩
      rw [ha', hb']
      constructor
      · intro _; omega
      · intro _; exact ⟨a ^ 2 + b ^ 2, by ring⟩
    · have := sq_add_sq_mixed (x := y / 2) (y := x / 2) hb ha; omega
    · have := sq_add_sq_mixed ha hb; omega
    · have := sq_add_sq_odd ha hb; omega
  · have := sq_add_sq_mixed (x := y) (y := x) hy hx; omega
  · have := sq_add_sq_mixed hx hy; omega
  · have := sq_add_sq_odd hx hy; omega

/-- If `4 ∣ x` and `4 ∣ y`, then `32 ∣ x² + y² ↔ 8 ∣ x + y`. -/
lemma thirtytwo_dvd_iff {x y : ℤ} (hx : (4 : ℤ) ∣ x) (hy : (4 : ℤ) ∣ y) :
    (32 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (8 : ℤ) ∣ x + y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have h : (4 * u) ^ 2 + (4 * v) ^ 2 = 16 * (u ^ 2 + v ^ 2) := by ring
  rw [h]
  have h1 := sq_mod_two u; have h2 := sq_mod_two v
  omega

lemma padicValInt_two_mul {a : ℤ} (ha : a ≠ 0) : padicValInt 2 (2 * a) = padicValInt 2 a + 1 := by
  rw [mul_comm]; exact_mod_cast padicValInt_mul_eq_succ (p := 2) a ha

lemma padicValInt_odd {a : ℤ} (ha : a % 2 = 1) : padicValInt 2 a = 0 :=
  padicValInt.eq_zero_of_not_dvd (by push_cast; omega)

/-- **The coordinate valuation** (Paper IV, Lemma 5.5): for `x, y ≠ 0`,
`v₂(x² + y²) = 2 min(v₂ x, v₂ y) + δ`, with `δ = 1` if `v₂ x = v₂ y` and `δ = 0` otherwise. -/
theorem coordinate_valuation {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValInt 2 (x ^ 2 + y ^ 2) =
      2 * min (padicValInt 2 x) (padicValInt 2 y) +
        if padicValInt 2 x = padicValInt 2 y then 1 else 0 := by
  induction h : x.natAbs using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    rcases Int.emod_two_eq_zero_or_one x with hx2 | hx2 <;>
      rcases Int.emod_two_eq_zero_or_one y with hy2 | hy2
    · obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
      have ha : a ≠ 0 := by rintro rfl; simp at hx
      have hb : b ≠ 0 := by rintro rfl; simp at hy
      have hlt : a.natAbs < n := by rw [← h, Int.natAbs_mul]; have := Int.natAbs_pos.2 ha; simp; omega
      have hN : (2 * a) ^ 2 + (2 * b) ^ 2 = 2 * (2 * (a ^ 2 + b ^ 2)) := by ring
      have hab : a ^ 2 + b ^ 2 ≠ 0 := by positivity
      rw [hN, padicValInt_two_mul (by positivity), padicValInt_two_mul hab, ih _ hlt ha hb rfl,
        padicValInt_two_mul ha, padicValInt_two_mul hb]
      simp only [add_left_inj]
      rw [min_add_add_right]; ring_nf
    · rw [padicValInt_odd hy2]
      have hv : 1 ≤ padicValInt 2 x := by
        obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
        rw [padicValInt_two_mul (by rintro rfl; simp at hx)]; omega
      have := sq_add_sq_mixed (x := y) (y := x) hy2 hx2
      rw [add_comm, padicValInt_odd this, if_neg (by omega)]; simp
    · rw [padicValInt_odd hx2]
      have hv : 1 ≤ padicValInt 2 y := by
        obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
        rw [padicValInt_two_mul (by rintro rfl; simp at hy)]; omega
      have := sq_add_sq_mixed hx2 hy2
      rw [padicValInt_odd this, if_neg (by omega)]; simp
    · rw [padicValInt_odd hx2, padicValInt_odd hy2, if_pos rfl]
      have h8 := sq_add_sq_odd hx2 hy2
      obtain ⟨m, hm⟩ : ∃ m, x ^ 2 + y ^ 2 = 2 * m ∧ m % 2 = 1 := ⟨(x ^ 2 + y ^ 2) / 2, by omega⟩
      rw [hm.1, padicValInt_two_mul (by omega), padicValInt_odd hm.2]; simp

end QuarterSumLadder
