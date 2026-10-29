module

public import QuarterSumLadder.Counts

@[expose] public section

/-!
# Weight two

For `p ≡ 1 (mod 8)` and a quartic `χ`, with `U_z = ∑_{χ(m) = z} m²`:

* `p_dvd_U`, `T2_eq`: `p ∣ U_z` and `∑ χ(m) m² = p (c₀ + i c₁)`, so `B_{2,χ} = c₀ + i c₁` with integer
  coordinates;
* `weight_two_congruence` (Paper IV, Theorem 3.1 at order `4`): `c₀ ≡ 4(E₁ + E₋₁)`,
  `c₁ ≡ 4(E_i + E_{-i})` and `c₀ + c₁ ≡ p - 1 (mod 8)`;
* `coords_mod_eight`: `c₀ ≡ c₁ ≡ 4(R₁ + R₃) (mod 8)`;
* `mod_eight_criterion` (Theorem 3.2): `8 ∣ c₀ ∧ 8 ∣ c₁ ⟺ χ(2) = 1 ⟺ 2` is a fourth power.
-/

namespace QuarterSumLadder

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- Odd squares are `1`, squares of `m ≡ 2 (mod 4)` are `4`, and other squares `0`, modulo `8`. -/
lemma sq_mod_eight (v : ℕ) :
    (((v : ℤ) ^ 2 : ℤ) : ZMod 8) = (if v % 2 = 1 then 1 else 0) + 4 * (if v % 4 = 2 then 1 else 0) := by
  have h : ((v : ℤ) : ZMod 8) = ((v % 8 : ℕ) : ZMod 8) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  have h2 : v % 2 = v % 8 % 2 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  have h4 : v % 4 = v % 8 % 4 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  push_cast
  rw [show ((v : ZMod 8)) = ((v % 8 : ℕ) : ZMod 8) by rw [ZMod.natCast_mod], h2, h4]
  have hlt := Nat.mod_lt v (show 0 < 8 by norm_num)
  interval_cases (v % 8) <;> decide

/-- `#{0 < m < p : m ≡ 2 (mod 4)} = Q`. -/
lemma card_two_mod_four (hp8 : p % 8 = 1) :
    (univ.filter fun x : ZMod p => x.val % 4 = 2).card = Q p := by
  have hpq := mod_eight_aux hp8
  rw [show Q p = (range (Q p)).card by simp]
  refine card_nbij' (fun x => x.val / 4) (fun k => ((4 * k + 2 : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hx ⊢
    have := ZMod.val_lt x; omega
  · intro k hk
    simp only [coe_range, Set.mem_Iio, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : 4 * (x.val / 4) + 2 = x.val := by omega
    show ((4 * (x.val / 4) + 2 : ℕ) : ZMod p) = x
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    show ((4 * k + 2 : ℕ) : ZMod p).val / 4 = k
    rw [ZMod.val_natCast_of_lt (by omega)]; omega

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

/-- **Divisibility**: `p ∣ U_z` for each class. -/
theorem p_dvd_U {z : GaussianInt} : (p : ℤ) ∣ U χ z := by
  have h17 := seventeen_le hp8
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  set u : ZMod p := (g : ZMod p) ^ 4 with hu
  have hu0 : u ≠ 0 := pow_ne_zero _ g.ne_zero
  have hχu : χ u = 1 := by
    rw [hu, map_pow]
    rcases quartic_apply_generator χ hχ hg with h | h <;> rw [h] <;> decide
  have hu2 : u ^ 2 ≠ 1 := by
    intro h
    rw [hu, ← pow_mul, ← Units.val_pow_eq_pow_val, Units.val_eq_one] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hgo] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hS : ((U χ z : ℤ) : ZMod p) = ∑ x ∈ fiber χ z, x ^ 2 := by
    unfold U; push_cast; simp
  rw [hS]
  have hperm : ∑ x ∈ fiber χ z, x ^ 2 = ∑ x ∈ fiber χ z, (u * x) ^ 2 := by
    refine sum_nbij' (fun x => u⁻¹ * x) (fun x => u * x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_fiber] at *
      have : χ u⁻¹ = 1 := by
        have h := (map_mul χ u u⁻¹).symm
        rw [mul_inv_cancel₀ hu0, map_one, hχu, one_mul] at h; exact h
      rw [map_mul, this, one_mul, hx]
    · intro x hx; rw [mem_fiber] at *; rw [map_mul, hχu, one_mul, hx]
    · intro x _; show u * (u⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
    · intro x _; show u⁻¹ * (u * x) = x; rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
    · intro x _; show x ^ 2 = (u * (u⁻¹ * x)) ^ 2; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  have : (u ^ 2 - 1) * ∑ x ∈ fiber χ z, x ^ 2 = 0 := by
    have h2 : ∑ x ∈ fiber χ z, (u * x) ^ 2 = u ^ 2 * ∑ x ∈ fiber χ z, x ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    rw [sub_mul, one_mul, ← h2, ← hperm, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hu2
  · exact h

lemma p_mul_c0 : (p : ℤ) * c0 χ = U χ 1 - U χ (-1) :=
  Int.mul_ediv_cancel' (dvd_sub (p_dvd_U hp8 hχ) (p_dvd_U hp8 hχ))

lemma p_mul_c1 : (p : ℤ) * c1 χ = U χ gi - U χ (-gi) :=
  Int.mul_ediv_cancel' (dvd_sub (p_dvd_U hp8 hχ) (p_dvd_U hp8 hχ))

/-- `T₂(χ) = ∑ χ(m) m² = p B_{2,χ}` with `B_{2,χ} = c₀ + i c₁`. -/
theorem T2_eq : T2 χ = (p : GaussianInt) * B2 χ := by
  have hfib : ∀ w : GaussianInt, ∑ x ∈ fiber χ w, χ x * (((x.val : ℤ) ^ 2 : ℤ) : GaussianInt) =
      w * ((U χ w : ℤ) : GaussianInt) := by
    intro w; unfold U; push_cast; rw [mul_sum]
    exact sum_congr rfl fun x hx => by rw [mem_fiber.1 hx]
  unfold T2
  rw [sum_univ_fibers hχ _ (by simp [MulChar.map_zero]), hfib, hfib, hfib, hfib]
  have h0 := p_mul_c0 hp8 hχ
  have h1 := p_mul_c1 hp8 hχ
  unfold B2
  set a := U χ 1
  set b := U χ gi
  set c := U χ (-1)
  set d := U χ (-gi)
  ext <;> simp [gi] <;> linarith

/-- The odd elements of a class have the same number, `Q/2`, in every class. -/
lemma odd_card {z : GaussianInt} (hz : FourVal z) :
    2 * ((fiber χ z).filter fun x => x.val % 2 = 1).card = Q p := by
  have h := card_odd_fiber hp8 hχ hz
  have : ((fiber χ z).filter fun x => x.val % 2 = 1) = (fiber χ z).filter fun x => Odd x.val := by
    ext x; simp [Nat.odd_iff]
  rw [this]; exact h

omit hp8 hχ in
/-- `U_z ≡ #(odd in D_z) + 4 E_z (mod 8)`. -/
lemma U_mod_eight (z : GaussianInt) :
    ((U χ z : ℤ) : ZMod 8) =
      (((fiber χ z).filter fun x => x.val % 2 = 1).card : ZMod 8) + 4 * (E χ z : ZMod 8) := by
  unfold U E
  rw [Int.cast_sum, sum_congr rfl (fun x _ => sq_mod_eight x.val), sum_add_distrib, ← mul_sum,
    sum_boole, sum_boole]

/-- **The weight-two congruence** (Paper IV, Theorem 3.1 at order `4`). -/
theorem weight_two_congruence :
    c0 χ ≡ 4 * (E χ 1 + E χ (-1)) [ZMOD 8] ∧ c1 χ ≡ 4 * (E χ gi + E χ (-gi)) [ZMOD 8] ∧
      c0 χ + c1 χ ≡ p - 1 [ZMOD 8] := by
  have hp1 : ((p : ℕ) : ZMod 8) = 1 := by
    rw [← ZMod.natCast_mod p 8, hp8]; simp
  have hc0 : ((c0 χ : ℤ) : ZMod 8) = ((U χ 1 - U χ (-1) : ℤ) : ZMod 8) := by
    rw [← p_mul_c0 hp8 hχ]; push_cast; rw [hp1, one_mul]
  have hc1 : ((c1 χ : ℤ) : ZMod 8) = ((U χ gi - U χ (-gi) : ℤ) : ZMod 8) := by
    rw [← p_mul_c1 hp8 hχ]; push_cast; rw [hp1, one_mul]
  have o1 := odd_card hp8 hχ (z := 1) (Or.inl rfl)
  have oi := odd_card hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have om := odd_card hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have omi := odd_card hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  have e1 : ((((fiber χ 1).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 8) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by
    congr 1; omega
  have e2 : ((((fiber χ gi).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 8) =
      (((fiber χ (-gi)).filter fun x => x.val % 2 = 1).card : ℕ) := by
    congr 1; omega
  have h8 : (8 : ZMod 8) = 0 := rfl
  -- the total count of `m ≡ 2 (mod 4)`
  have hE := sum_univ_fibers hχ (fun x : ZMod p => if x.val % 4 = 2 then (1 : ℕ) else 0)
    (by simp)
  simp only [← card_filter] at hE
  rw [card_two_mod_four hp8] at hE
  have hEq : (E χ 1 + E χ gi + E χ (-1) + E χ (-gi) : ℕ) = Q p := by
    unfold E; rw [hE]
  have hpq := mod_eight_aux hp8
  have hEq' : (E χ 1 : ZMod 8) + E χ gi + E χ (-1 : GaussianInt) + E χ (-gi) = Q p := by
    have := congrArg (fun n : ℕ => (n : ZMod 8)) hEq; push_cast at this; exact this
  have hQ : ((p : ℕ) : ZMod 8) - 1 = 4 * (Q p : ZMod 8) := by
    have : ((p - 1 : ℕ) : ZMod 8) = ((4 * Q p : ℕ) : ZMod 8) := by rw [hpq]
    push_cast [Nat.cast_sub hp.out.one_le] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · refine (ZMod.intCast_eq_intCast_iff _ _ 8).1 ?_
    rw [hc0]; push_cast
    rw [U_mod_eight (χ := χ), U_mod_eight (χ := χ), e1]
    linear_combination (-(E χ (-1) : ZMod 8)) * h8
  · refine (ZMod.intCast_eq_intCast_iff _ _ 8).1 ?_
    rw [hc1]; push_cast
    rw [U_mod_eight (χ := χ), U_mod_eight (χ := χ), e2]
    linear_combination (-(E χ (-gi) : ZMod 8)) * h8
  · refine (ZMod.intCast_eq_intCast_iff _ _ 8).1 ?_
    push_cast
    rw [hc0, hc1]; push_cast
    rw [U_mod_eight (χ := χ), U_mod_eight (χ := χ), U_mod_eight, U_mod_eight, e1, e2]
    linear_combination 4 * hEq' - hQ - ((E χ (-1) : ZMod 8) + E χ (-gi)) * h8

lemma fourVal_mul_two {z : GaussianInt} (hz : FourVal z) : FourVal (χ 2 * z) := by
  rcases char_two hp8 hχ with h | h <;> rw [h] <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp [FourVal]

/-- `E_z + #{0 < m < p/4 : χ(m) = z} = Q/2`. -/
lemma E_add_R {z : GaussianInt} (hz : FourVal z) :
    E χ z + ((fiber χ z).filter fun x => 4 * x.val < p).card = Q p / 2 := by
  have hsq := char_two_sq hp8 hχ
  set y := χ 2 * z with hy
  have hyv := fourVal_mul_two hp8 hχ hz
  have hhalf := card_half_fiber hp8 hχ hyv
  have hsplit := card_filter_add_card_filter_not (s := (fiber χ y).filter fun x => 2 * x.val < p)
    (p := fun x => Odd x.val)
  rw [filter_filter, filter_filter] at hsplit
  have heven : ((fiber χ y).filter fun x => 2 * x.val < p ∧ ¬ Odd x.val) =
      (fiber χ y).filter fun x => 2 * x.val < p ∧ Even x.val := by
    ext x; simp [Nat.not_odd_iff_even]
  rw [heven, card_even_half hp8 hχ, hy, ← mul_assoc, hsq, one_mul] at hsplit
  rw [E_eq hp8 hχ]
  omega

/-- `E₁ + E₋₁ = R₁ + R₃` and `E_i + E_{-i} = R₀ + R₂`. -/
lemma E_sums : E χ 1 + E χ (-1) = R χ 1 + R χ 3 ∧ E χ gi + E χ (-gi) = R χ 0 + R χ 2 := by
  have a := E_add_R hp8 hχ (z := 1) (Or.inl rfl)
  have b := E_add_R hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have c := E_add_R hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have d := E_add_R hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  rw [← R_zero] at a; rw [← R_one] at b; rw [← R_two] at c; rw [← R_three] at d
  have hs := sum_R hp8 hχ
  have hQ : 2 ∣ Q p := by have := mod_eight_aux hp8; unfold Q; omega
  omega

/-- `c₀ ≡ c₁ ≡ 4(R₁ + R₃) (mod 8)`. -/
theorem coords_mod_eight :
    c0 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] ∧ c1 χ ≡ 4 * (R χ 1 + R χ 3) [ZMOD 8] := by
  obtain ⟨h0, h1, -⟩ := weight_two_congruence hp8 hχ
  obtain ⟨e1, e2⟩ := E_sums hp8 hχ
  have hs := sum_R hp8 hχ
  have hQ : 2 ∣ Q p := by have := mod_eight_aux hp8; unfold Q; omega
  refine ⟨?_, ?_⟩
  · have : (E χ 1 : ℤ) + E χ (-1) = R χ 1 + R χ 3 := by exact_mod_cast e1
    rw [this] at h0; exact h0
  · have : (E χ gi : ℤ) + E χ (-gi) = R χ 0 + R χ 2 := by exact_mod_cast e2
    rw [this] at h1
    refine h1.trans ?_
    rw [Int.modEq_iff_dvd]
    have hs' : (R χ 0 : ℤ) + R χ 2 = Q p - (R χ 1 + R χ 3) := by
      have : (R χ 0 + R χ 1 + R χ 2 + R χ 3 : ℤ) = Q p := by exact_mod_cast hs
      linarith
    obtain ⟨k, hk⟩ := hQ
    refine ⟨-(k : ℤ) + (R χ 1 + R χ 3), ?_⟩
    rw [hs']; push_cast [hk]; ring

/-- **The mod-8 criterion** (Paper IV, Theorem 3.2): `8 ∣ c₀` and `8 ∣ c₁` exactly when
`χ(2) = 1`, that is, when `2` is a fourth power modulo `p`. (Gauss's criterion, `p = a² + 64 b²`, is
not formalized.) -/
theorem mod_eight_criterion :
    ((8 : ℤ) ∣ c0 χ ∧ (8 : ℤ) ∣ c1 χ ↔ χ 2 = 1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) := by
  refine ⟨?_, char_eq_one_iff hχ (two_ne_zero_zmod (hp2_of hp8))⟩
  obtain ⟨h0, h1⟩ := coords_mod_eight hp8 hχ
  have hq := quarter_law hp8 hχ
  rw [Int.ModEq] at h0 h1
  rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
  · rw [he.neg_one_pow] at hq
    obtain ⟨k, hk⟩ := he
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = k + k := by exact_mod_cast hk
    push_cast at hk'
    simp only [hq, iff_true]
    constructor <;> omega
  · rw [ho.neg_one_pow] at hq
    obtain ⟨k, hk⟩ := ho
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    push_cast at hk'
    rw [hq]
    simp only [show ((-1 : GaussianInt) = 1) ↔ False by decide, iff_false, not_and]
    omega

end Quartic

end QuarterSumLadder
