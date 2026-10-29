module

public import QuarterSumLadder.Classes

@[expose] public section

/-!
# The quarter counts

For `p ≡ 1 (mod 8)` and a quartic `χ`:

* `sum_R`: `R₀ + R₁ + R₂ + R₃ = Q`;
* `kappa_eq`: `κ = Q - 2(R₁ + R₃)` (the quarter-interval formula, with `κ = h(-4p)/2`);
* `quarter_law`: `χ(2) = (-1)^{R₁ + R₃}` (E. Lehmer's criterion at `k = 2`, the quartic Gauss lemma
  of Williams and Currie);
* `orbit_parity`: if `χ(2) = 1`, then `R₀ ≡ R₁ ≡ R₂ ≡ R₃ (mod 2)` (Paper IV, Theorem 3.3);
* `R_two_parity`, `parity_rho`: the parity of `R₂` through `2^{(p-1)/8}` and through `ord_p(2)`;
* `patterns_excluded`: the parity vector of `(R₀, R₁, R₂, R₃)` is never `1010` or `0101`.
-/

namespace QuarterSumLadder

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma gi_cube : gi ^ 3 = -gi := by rw [pow_succ, gi_sq]; ring

/-- `#{x : x ≠ 0, ⟨x⟩ < p/4} = Q`. -/
lemma card_quarter (hp8 : p % 8 = 1) :
    (univ.filter fun x : ZMod p => x ≠ 0 ∧ 4 * x.val < p).card = Q p := by
  have hpq := mod_eight_aux hp8
  rw [show Q p = (Icc 1 (Q p)).card by simp]
  refine card_nbij' (fun x => x.val) (fun n => (n : ZMod p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_Icc, Set.mem_Icc] at hx ⊢
    have := val_pos_of_ne_zero hx.1
    omega
  · intro n hn
    simp only [coe_Icc, Set.mem_Icc, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hn ⊢
    have hlt : n < p := by omega
    rw [ZMod.val_natCast_of_lt hlt]
    refine ⟨?_, by omega⟩
    rw [Ne, ← ZMod.val_eq_zero, ZMod.val_natCast_of_lt hlt]; omega
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro n hn
    simp only [coe_Icc, Set.mem_Icc] at hn
    exact ZMod.val_natCast_of_lt (by omega)

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

omit hp8 hχ in
lemma R_zero : R χ 0 = ((fiber χ 1).filter fun x => 4 * x.val < p).card := by
  simpa using R_eq (χ := χ) 0

omit hp8 hχ in
lemma R_one : R χ 1 = ((fiber χ gi).filter fun x => 4 * x.val < p).card := by
  simpa using R_eq (χ := χ) 1

omit hp8 hχ in
lemma R_two : R χ 2 = ((fiber χ (-1)).filter fun x => 4 * x.val < p).card := by
  simpa [gi_sq] using R_eq (χ := χ) 2

omit hp8 hχ in
lemma R_three : R χ 3 = ((fiber χ (-gi)).filter fun x => 4 * x.val < p).card := by
  simpa [gi_cube] using R_eq (χ := χ) 3

/-- `R₀ + R₁ + R₂ + R₃ = Q`. -/
theorem sum_R : R χ 0 + R χ 1 + R χ 2 + R χ 3 = Q p := by
  have h := sum_univ_fibers hχ
    (fun x : ZMod p => if x ≠ 0 ∧ 4 * x.val < p then (1 : ℕ) else 0) (by simp)
  have hf : ∀ w : GaussianInt, w ≠ 0 →
      ∑ x ∈ fiber χ w, (if x ≠ 0 ∧ 4 * x.val < p then (1 : ℕ) else 0) =
        ((fiber χ w).filter fun x => 4 * x.val < p).card := by
    intro w hw
    rw [card_filter]
    exact sum_congr rfl fun x hx => by simp [ne_zero_of_mem_fiber hw hx]
  rw [hf 1 one_ne_zero, hf gi (by decide), hf (-1) (by decide), hf (-gi) (by decide),
    sum_boole, Nat.cast_id, card_quarter hp8] at h
  rw [R_zero, R_one, R_two, R_three]
  omega

omit hp hp8 hχ in
lemma half_mem {x : ZMod p} (h : 4 * x.val < p) : 2 * x.val < p := by omega

omit hp8 hχ in
/-- The half part of a class, with `R_r` of its elements in `(0, p/4)`. -/
lemma card_half_filter_quarter (z : GaussianInt) :
    (((fiber χ z).filter fun x => 2 * x.val < p).filter fun x => 4 * x.val < p) =
      (fiber χ z).filter fun x => 4 * x.val < p := by
  ext x; simp only [mem_filter]; constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, half_mem h3⟩, h3⟩

lemma gaussMap_char (x : ZMod p) : χ (gaussMap x) = χ 2 * χ x := by
  unfold gaussMap
  split_ifs
  · rw [map_mul]
  · rw [char_neg hp8 hχ, map_mul]

omit hp8 hχ in
lemma neg_one_pow_mul_self (n : ℕ) : ((-1 : ZMod p) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; simp

/-- `2^Q = (-1)^{R₁ + R₃}` in `ZMod p`. -/
theorem two_pow_Q : (2 : ZMod p) ^ Q p = (-1) ^ (R χ 1 + R χ 3) := by
  have hp2 := hp2_of hp8
  set A := (fiber χ 1 ∪ fiber χ (-1)).filter fun x => 2 * x.val < p with hA
  have hdisj : Disjoint (fiber χ 1) (fiber χ (-1)) := by
    rw [disjoint_left]; intro x h1 h2
    rw [mem_fiber] at h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  have hcardA : A.card = Q p := by
    rw [hA, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
    have h1 := card_half_fiber hp8 hχ (z := 1) (Or.inl rfl)
    have h2 := card_half_fiber hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
    omega
  have hmem : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p := by
    intro x hx
    rw [hA, mem_filter, mem_union] at hx
    refine ⟨?_, hx.2⟩
    rcases hx.1 with h | h
    · exact ne_zero_of_mem_fiber one_ne_zero h
    · exact ne_zero_of_mem_fiber (by decide) h
  have hφ : ∀ x ∈ A, gaussMap x ∈ A := by
    intro x hx
    have hx0 := (hmem x hx).1
    rw [hA, mem_filter, mem_union] at hx ⊢
    refine ⟨?_, gaussMap_mem_half hp2 hx0 hx.2⟩
    rw [mem_fiber, mem_fiber, gaussMap_char hp8 hχ]
    rcases char_two hp8 hχ with h2 | h2 <;> rcases hx.1 with h | h <;>
      rw [mem_fiber] at h <;> rw [h2, h] <;> norm_num
  have hkey := gauss_product hp2 A hmem hφ
  have hq : (A.filter fun x => 4 * x.val < p).card = R χ 0 + R χ 2 := by
    rw [hA, filter_filter, filter_union, card_union_of_disjoint
      (disjoint_filter_filter hdisj), R_zero, R_two]
    congr 2 <;> ext x <;> simp only [mem_filter] <;>
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, half_mem h.2, h.2⟩⟩
  have hsplit := card_filter_add_card_filter_not (s := A) (p := fun x => 4 * x.val < p)
  have hsum := sum_R hp8 hχ
  rw [hq, hcardA] at hsplit
  have hμ : (A.filter fun x => ¬ 4 * x.val < p).card = R χ 1 + R χ 3 := by omega
  rw [hμ, hcardA] at hkey
  calc (2 : ZMod p) ^ Q p = (2 : ZMod p) ^ Q p * ((-1) ^ (R χ 1 + R χ 3) * (-1) ^ (R χ 1 + R χ 3)) :=
        by rw [neg_one_pow_mul_self, mul_one]
    _ = (-1) ^ (R χ 1 + R χ 3) := by rw [← mul_assoc, hkey, one_mul]

/-- `χ(x) = 1 ⟺ x^Q = 1` for `x ≠ 0`. -/
theorem char_eq_one_iff_pow {x : ZMod p} (hx : x ≠ 0) : χ x = 1 ↔ x ^ Q p = 1 := by
  have hpq := mod_eight_aux hp8
  have hQ : 0 < Q p := by have := seventeen_le hp8; omega
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  obtain ⟨j, hj⟩ := hg (Units.mk0 x hx)
  have hxj : x = (g : ZMod p) ^ j := by
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    exact this.symm
  rw [hxj, map_pow, gi_pow_eq_one_iff (quartic_apply_generator χ hχ hg), ← pow_mul,
    ← Units.val_pow_eq_pow_val, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one, hgo, hpq,
    show j * Q p = Q p * j by ring, mul_comm 4 (Q p)]
  exact (Nat.mul_dvd_mul_iff_left hQ).symm

omit hp8 hχ in
lemma neg_one_ne_one_zmod (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by linear_combination -h
  exact two_ne_zero_zmod hp2 h2

/-- **The quarter law** (the quartic Gauss lemma): `χ(2) = (-1)^{R₁ + R₃}`. -/
theorem quarter_law : χ 2 = (-1) ^ (R χ 1 + R χ 3) := by
  have hp2 := hp2_of hp8
  have h := two_pow_Q hp8 hχ
  have hc := char_eq_one_iff_pow hp8 hχ (two_ne_zero_zmod hp2)
  rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
  · rw [he.neg_one_pow] at h ⊢; exact hc.2 h
  · rw [ho.neg_one_pow] at h ⊢
    rcases char_two hp8 hχ with h2 | h2
    · exfalso; rw [hc.1 h2] at h; exact absurd h.symm (neg_one_ne_one_zmod hp2)
    · exact h2

/-- Gauss's product on the half part of a single class, when `χ(2) = 1`. -/
lemma gauss_class (hw : χ 2 = 1) {z : GaussianInt} (hz : FourVal z) :
    (2 : ZMod p) ^ (Q p / 2) *
        (-1) ^ (Q p / 2 - ((fiber χ z).filter fun x => 4 * x.val < p).card) = 1 ∧
      ((fiber χ z).filter fun x => 4 * x.val < p).card ≤ Q p / 2 := by
  have hp2 := hp2_of hp8
  have hz0 : z ≠ 0 := by rcases hz with rfl | rfl | rfl | rfl <;> decide
  set A := (fiber χ z).filter fun x => 2 * x.val < p with hA
  have hcardA : A.card = Q p / 2 := by
    have := card_half_fiber hp8 hχ hz; rw [← hA] at this; omega
  have hmem : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p := fun x hx =>
    ⟨ne_zero_of_mem_fiber hz0 (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
  have hφ : ∀ x ∈ A, gaussMap x ∈ A := by
    intro x hx
    have hx0 := (hmem x hx).1
    rw [hA, mem_filter] at hx ⊢
    refine ⟨?_, gaussMap_mem_half hp2 hx0 hx.2⟩
    rw [mem_fiber, gaussMap_char hp8 hχ, hw, one_mul]; exact mem_fiber.1 hx.1
  have hkey := gauss_product hp2 A hmem hφ
  have hsplit := card_filter_add_card_filter_not (s := A) (p := fun x => 4 * x.val < p)
  rw [hA, filter_filter] at hsplit
  have hf : ((fiber χ z).filter fun x => 2 * x.val < p ∧ 4 * x.val < p) =
      (fiber χ z).filter fun x => 4 * x.val < p := by
    ext x; simp only [mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, half_mem h.2, h.2⟩⟩
  rw [hf, ← hA, hcardA] at hsplit
  rw [hcardA] at hkey
  refine ⟨?_, by omega⟩
  rwa [show (A.filter fun x => ¬ 4 * x.val < p).card =
    Q p / 2 - ((fiber χ z).filter fun x => 4 * x.val < p).card by omega] at hkey

omit hp8 hχ in
lemma neg_one_pow_eq_iff (hp2 : p ≠ 2) (a b : ℕ) :
    (-1 : ZMod p) ^ a = (-1) ^ b ↔ a % 2 = b % 2 := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod p), neg_one_pow_eq_pow_mod_two (R := ZMod p) (n := b)]
  have h1 := neg_one_ne_one_zmod hp2
  have ha := Nat.mod_lt a (show 0 < 2 by norm_num)
  have hb := Nat.mod_lt b (show 0 < 2 by norm_num)
  interval_cases (a % 2) <;> interval_cases (b % 2) <;> simp [h1, h1.symm]

/-- **Doubling-orbit parity** (Paper IV, Theorem 3.3). If `χ(2) = 1`, then
`R₀ ≡ R₁ ≡ R₂ ≡ R₃ (mod 2)`. -/
theorem orbit_parity (hw : χ 2 = 1) :
    R χ 1 % 2 = R χ 0 % 2 ∧ R χ 2 % 2 = R χ 0 % 2 ∧ R χ 3 % 2 = R χ 0 % 2 := by
  have hp2 := hp2_of hp8
  have g0 := gauss_class hp8 hχ hw (z := 1) (Or.inl rfl)
  have g1 := gauss_class hp8 hχ hw (z := gi) (Or.inr (Or.inl rfl))
  have g2 := gauss_class hp8 hχ hw (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have g3 := gauss_class hp8 hχ hw (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  rw [← R_zero] at g0
  rw [← R_one] at g1
  rw [← R_two] at g2
  rw [← R_three] at g3
  have hc : ∀ a b : ℕ, (2 : ZMod p) ^ (Q p / 2) * (-1) ^ a = 1 →
      (2 : ZMod p) ^ (Q p / 2) * (-1) ^ b = 1 → a % 2 = b % 2 := by
    intro a b ha hb
    rw [← neg_one_pow_eq_iff hp2]
    have h2 : (2 : ZMod p) ^ (Q p / 2) ≠ 0 := pow_ne_zero _ (two_ne_zero_zmod hp2)
    exact mul_left_cancel₀ h2 (ha.trans hb.symm)
  have e1 := hc _ _ g1.1 g0.1
  have e2 := hc _ _ g2.1 g0.1
  have e3 := hc _ _ g3.1 g0.1
  have := g0.2; have := g1.2; have := g2.2; have := g3.2
  omega

/-- The parity of `R₂` when `χ(2) = 1`: `R₂ ≡ (p - 1)/8 + [2^{(p-1)/8} = -1] (mod 2)`. -/
theorem R_two_parity (hw : χ 2 = 1) :
    R χ 2 % 2 = ((p - 1) / 8 + if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 := by
  have hp2 := hp2_of hp8
  have g2 := gauss_class hp8 hχ hw (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  rw [← R_two] at g2
  have hQ8 : Q p / 2 = (p - 1) / 8 := by unfold Q; omega
  rw [hQ8] at g2
  obtain ⟨hk, hle⟩ := g2
  have h1 := neg_one_ne_one_zmod hp2
  rcases Nat.even_or_odd ((p - 1) / 8 - R χ 2) with he | ho
  · rw [he.neg_one_pow, mul_one] at hk
    rw [hk, if_neg h1.symm]
    obtain ⟨j, hj⟩ := he; omega
  · rw [ho.neg_one_pow] at hk
    have : (2 : ZMod p) ^ ((p - 1) / 8) = -1 := by linear_combination -hk
    rw [if_pos this]
    obtain ⟨j, hj⟩ := ho; omega

/-- The indicator `[2^{(p-1)/8} = -1]` through `ρ = ord_p(2)`, when `2` is a fourth power. -/
theorem parity_rho (hw : χ 2 = 1) :
    (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 =
      (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0) % 2 := by
  have hp2 := hp2_of hp8
  have h1 := neg_one_ne_one_zmod hp2
  have hpq := mod_eight_aux hp8
  have h2Q : (2 : ZMod p) ^ Q p = 1 := (char_eq_one_iff_pow hp8 hχ (two_ne_zero_zmod hp2)).1 hw
  set ρ := orderOf (2 : ZMod p) with hρ
  have hρQ : ρ ∣ Q p := orderOf_dvd_of_pow_eq_one h2Q
  obtain ⟨t, ht⟩ := hρQ
  have hQeven : 2 ∣ Q p := by unfold Q; omega
  have hQ8 : (p - 1) / 8 = Q p / 2 := by unfold Q; omega
  have hdiv : (p - 1) / (4 * ρ) = t := by
    have hρpos : 0 < ρ := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨Q p, by have := seventeen_le hp8; unfold Q; omega, h2Q⟩)
    rw [hpq, ht, show 4 * (ρ * t) = (4 * ρ) * t by ring, Nat.mul_div_cancel_left _ (by omega)]
  rw [hdiv, hQ8]
  by_cases hρe : 2 ∣ ρ
  · rw [if_pos hρe]
    obtain ⟨σ, hσ⟩ := hρe
    have hρpos : 0 < ρ := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨Q p, by have := seventeen_le hp8; unfold Q; omega, h2Q⟩)
    have hσpos : 0 < σ := by omega
    have hsq : (2 : ZMod p) ^ σ * (2 : ZMod p) ^ σ = 1 := by
      rw [← pow_add, show σ + σ = ρ by omega, hρ, pow_orderOf_eq_one]
    have hne : (2 : ZMod p) ^ σ ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hσv : (2 : ZMod p) ^ σ = -1 := by
      rcases mul_self_eq_one_iff.1 hsq with h | h
      · exact absurd h hne
      · exact h
    have hQ2 : Q p / 2 = σ * t := by
      rw [ht, hσ, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [hQ2, pow_mul, hσv]
    rcases Nat.even_or_odd t with he | ho
    · rw [he.neg_one_pow, if_neg h1.symm]; obtain ⟨j, hj⟩ := he; omega
    · rw [ho.neg_one_pow, if_pos rfl]; obtain ⟨j, hj⟩ := ho; omega
  · rw [if_neg hρe]
    have hodd : Nat.Coprime ρ 2 := by
      rw [Nat.coprime_two_right]; exact Nat.odd_iff.2 (by omega)
    have hρh : ρ ∣ Q p / 2 := by
      have : ρ ∣ 2 * (Q p / 2) := by rw [Nat.mul_div_cancel' hQeven]; exact ⟨t, ht⟩
      exact hodd.dvd_of_dvd_mul_left this
    obtain ⟨u, hu⟩ := hρh
    rw [hu, pow_mul, hρ, pow_orderOf_eq_one, one_pow, if_neg h1.symm]

/-- **The excluded patterns** (Paper IV, Corollary 3.4): the parity vector of
`(R₀, R₁, R₂, R₃)` is never `1010` or `0101`. -/
theorem patterns_excluded :
    ¬ (R χ 0 % 2 = 1 ∧ R χ 1 % 2 = 0 ∧ R χ 2 % 2 = 1 ∧ R χ 3 % 2 = 0) ∧
      ¬ (R χ 0 % 2 = 0 ∧ R χ 1 % 2 = 1 ∧ R χ 2 % 2 = 0 ∧ R χ 3 % 2 = 1) := by
  rcases char_two hp8 hχ with hw | hw
  · have := orbit_parity hp8 hχ hw
    constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;> omega
  · have hq := quarter_law hp8 hχ
    rw [hw] at hq
    have hodd : Odd (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · rw [he.neg_one_pow] at hq; exact absurd hq (by decide)
      · exact ho
    obtain ⟨k, hk⟩ := hodd
    constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;> omega

/-- **The quarter-interval formula**: `κ = Q - 2(R₁ + R₃)`, where `κ = ∑_{0<n<p/4} (n/p)`
(which is `h(-4p)/2`). -/
theorem kappa_eq : kappa p = (Q p : ℤ) - 2 * (R χ 1 + R χ 3) := by
  have hpq := mod_eight_aux hp8
  set q : ZMod p → ℤ := fun x => quadraticChar (ZMod p) x with hq
  have h1 : kappa p = ∑ x ∈ univ.filter (fun x : ZMod p => x ≠ 0 ∧ 4 * x.val < p), q x := by
    unfold kappa
    refine sum_nbij' (fun n => (n : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [mem_filter, mem_range, mem_univ, true_and] at hn ⊢
      rw [ZMod.val_natCast_of_lt hn.1]
      refine ⟨?_, hn.2.2⟩
      rw [Ne, ← ZMod.val_eq_zero, ZMod.val_natCast_of_lt hn.1]; omega
    · intro x hx
      simp only [mem_filter, mem_range, mem_univ, true_and] at hx ⊢
      exact ⟨ZMod.val_lt x, val_pos_of_ne_zero hx.1, hx.2⟩
    · intro n hn
      simp only [mem_filter, mem_range] at hn
      exact ZMod.val_natCast_of_lt hn.1
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro n _; simp [hq, legendreSym]
  have h2 := sum_univ_fibers hχ (fun x : ZMod p => if x ≠ 0 ∧ 4 * x.val < p then q x else 0)
    (by simp)
  rw [← sum_filter] at h2
  have hf : ∀ w : GaussianInt, w ≠ 0 → ∀ ε : ℤ, (∀ x ∈ fiber χ w, q x = ε) →
      ∑ x ∈ fiber χ w, (if x ≠ 0 ∧ 4 * x.val < p then q x else 0) =
        ε * ((fiber χ w).filter fun x => 4 * x.val < p).card := by
    intro w hw ε hε
    rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
    refine sum_congr rfl fun x hx => ?_
    by_cases h4 : 4 * x.val < p <;> simp [h4, ne_zero_of_mem_fiber hw hx, hε x hx]
  have hq1 : ∀ w : GaussianInt, (w = 1 ∨ w = -1) → ∀ x ∈ fiber χ w, q x = 1 := by
    intro w hw x hx
    have hx0 := ne_zero_of_mem_fiber (by rcases hw with rfl | rfl <;> decide) hx
    show (quadraticChar (ZMod p) x : ℤ) = 1; rw [quadraticChar_of_char_one hχ hx0 (by rw [mem_fiber.1 hx]; exact hw)]
  have hqi : ∀ w : GaussianInt, (w = gi ∨ w = -gi) → ∀ x ∈ fiber χ w, q x = -1 := by
    intro w hw x hx
    have hx0 := ne_zero_of_mem_fiber (by rcases hw with rfl | rfl <;> decide) hx
    show (quadraticChar (ZMod p) x : ℤ) = -1; rw [quadraticChar_of_char_gi hχ hx0 (by rw [mem_fiber.1 hx]; exact hw)]
  rw [hf 1 one_ne_zero 1 (hq1 1 (Or.inl rfl)), hf gi (by decide) (-1) (hqi gi (Or.inl rfl)),
    hf (-1) (by decide) 1 (hq1 (-1) (Or.inr rfl)), hf (-gi) (by decide) (-1) (hqi (-gi) (Or.inr rfl)),
    ← R_zero, ← R_one, ← R_two, ← R_three] at h2
  rw [h1, h2]
  have hs := sum_R hp8 hχ
  have : (Q p : ℤ) = R χ 0 + R χ 1 + R χ 2 + R χ 3 := by exact_mod_cast hs.symm
  rw [this]; ring

/-- **The classical criterion** (Paper IV, after Theorem 3.2; Barrucand–Cohn, Williams–Currie):
`χ(2) = 1 ⟺ κ ≡ Q (mod 4)`, that is, `h(-4p) ≡ (p - 1)/2 (mod 8)` with `h(-4p) = 2κ`. -/
theorem kappa_criterion : χ 2 = 1 ↔ kappa p % 4 = (Q p : ℤ) % 4 := by
  have hk := kappa_eq hp8 hχ
  have hq := quarter_law hp8 hχ
  rw [hq, hk]
  rcases Nat.even_or_odd (R χ 1 + R χ 3) with ⟨j, hj⟩ | ⟨j, hj⟩
  · have : ((R χ 1 : ℤ) + R χ 3) = j + j := by exact_mod_cast hj
    rw [hj, Even.neg_one_pow ⟨j, rfl⟩, this]; simp only [true_iff]; omega
  · have : ((R χ 1 : ℤ) + R χ 3) = 2 * j + 1 := by exact_mod_cast hj
    rw [hj, Odd.neg_one_pow ⟨j, rfl⟩, this]
    simp only [show ((-1 : GaussianInt) = 1) ↔ False from ⟨fun h => absurd h (by decide), False.elim⟩,
      false_iff]
    omega

end Quartic

end QuarterSumLadder
