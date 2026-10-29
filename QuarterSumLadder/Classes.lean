module

public import QuarterSumLadder.Prelim

@[expose] public section

/-!
# The four classes of a quartic character at `p ≡ 1 (mod 8)`

For `p ≡ 1 (mod 8)` and `χ` of order `4` with values in `ℤ[i]`: `χ` is even, `χ(2) = ± 1`, every
class `D_z` (`z ∈ {1, i, -1, -i}`) has `Q = (p - 1)/4` elements, half of them in `(0, p/2)` and
half of them odd, and the counts `R_r`, `E_z` are counts of half-system elements.
-/

namespace QuarterSumLadder

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma mod_eight_aux (hp8 : p % 8 = 1) : p - 1 = 4 * Q p := by unfold Q; omega

lemma seventeen_le (hp8 : p % 8 = 1) : 17 ≤ p := by
  by_contra h
  have h2 := hp.out.two_le
  have : p = 9 := by omega
  subst this; exact absurd hp.out (by norm_num)

omit hp in
lemma hp2_of (hp8 : p % 8 = 1) : p ≠ 2 := by omega

lemma mem_fiber {χ : MulChar (ZMod p) GaussianInt} {x : ZMod p} {z : GaussianInt} :
    x ∈ fiber χ z ↔ χ x = z := by simp [fiber]

/-- A set closed under negation, not containing `0`, is split in half by any predicate that
negation reverses. -/
lemma two_mul_card_filter_of_neg {S : Finset (ZMod p)} (P : ZMod p → Prop) [DecidablePred P]
    (hS : ∀ x ∈ S, -x ∈ S) (hP : ∀ x ∈ S, (P (-x) ↔ ¬ P x)) :
    2 * (S.filter P).card = S.card := by
  have h : (S.filter P).card = (S.filter fun x => ¬ P x).card := by
    refine card_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hS x hx.1, fun h => ((hP x hx.1).1 h) hx.2⟩
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hS x hx.1, (hP x hx.1).2 hx.2⟩
    · intro x _; simp
    · intro x _; simp
  have := card_filter_add_card_filter_not (s := S) (p := P)
  omega

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

lemma char_even : χ (-1) = 1 := quartic_apply_neg_one_of_one χ hχ hp8

omit hp8 in
lemma char_ne_zero {x : ZMod p} (hx : x ≠ 0) : χ x ≠ 0 := by
  rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide

lemma char_neg (x : ZMod p) : χ (-x) = χ x := by
  calc χ (-x) = χ (-1 * x) := by rw [neg_one_mul]
    _ = χ (-1) * χ x := map_mul _ _ _
    _ = χ x := by rw [char_even hp8 hχ, one_mul]

lemma neg_mem_fiber {x : ZMod p} {z : GaussianInt} (h : x ∈ fiber χ z) : -x ∈ fiber χ z := by
  rw [mem_fiber] at *; rw [char_neg hp8 hχ, h]

lemma char_two : χ 2 = 1 ∨ χ 2 = -1 := by
  have hsq : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff (hp2_of hp8)).2 (Or.inl hp8)
  exact (isSquare_iff_char hχ (two_ne_zero_zmod (hp2_of hp8))).1 hsq

lemma char_two_sq : χ 2 * χ 2 = 1 := by
  rcases char_two hp8 hχ with h | h <;> rw [h] <;> norm_num

omit hp8 hχ in
lemma ne_zero_of_mem_fiber {x : ZMod p} {z : GaussianInt} (hz : z ≠ 0) (hx : x ∈ fiber χ z) :
    x ≠ 0 := by
  rintro rfl; rw [mem_fiber, MulChar.map_zero] at hx; exact hz hx.symm

omit hp8 in
/-- A sum over `ZMod p` of a function vanishing at `0` splits over the four classes. -/
lemma sum_univ_fibers {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (h0 : f 0 = 0) :
    ∑ x, f x = ∑ x ∈ fiber χ 1, f x + ∑ x ∈ fiber χ gi, f x + ∑ x ∈ fiber χ (-1), f x +
      ∑ x ∈ fiber χ (-gi), f x := by
  have hmaps : ∀ x ∈ (univ : Finset (ZMod p)),
      χ x ∈ ({0, 1, gi, -1, -gi} : Finset GaussianInt) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · rcases quartic_values χ hχ hx with h | h | h | h <;> simp [h]
  rw [← sum_fiberwise_of_maps_to hmaps, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have hz : ∑ x ∈ univ.filter (fun x => χ x = 0), f x = 0 := by
    refine sum_eq_zero fun x hx => ?_
    have hx0 : x = 0 := by
      by_contra h; exact char_ne_zero hχ h (mem_filter.1 hx).2
    rw [hx0, h0]
  rw [hz, zero_add]
  simp only [fiber, add_assoc]

/-- The four values. -/
abbrev FourVal (z : GaussianInt) : Prop := z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi

omit hp8 in
lemma exists_char_eq {z : GaussianInt} (hz : FourVal z) : ∃ c : ZMod p, c ≠ 0 ∧ χ c = z := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  have hu := quartic_apply_generator χ hχ hg
  have hg0 : (g : ZMod p) ≠ 0 := g.ne_zero
  have hpow : ∀ k : ℕ, χ ((g : ZMod p) ^ k) = (χ g) ^ k := fun k => map_pow χ _ k
  have key : ∀ k : ℕ, k < 4 → z = (χ g) ^ k → ∃ c : ZMod p, c ≠ 0 ∧ χ c = z :=
    fun k _ h => ⟨(g : ZMod p) ^ k, pow_ne_zero _ hg0, by rw [hpow, h]⟩
  rcases hu with hu | hu <;> rcases hz with rfl | rfl | rfl | rfl
  · exact key 0 (by norm_num) (by simp)
  · exact key 1 (by norm_num) (by rw [hu, pow_one])
  · exact key 2 (by norm_num) (by rw [hu, gi_sq])
  · exact key 3 (by norm_num) (by rw [hu, pow_succ, gi_sq]; ring)
  · exact key 0 (by norm_num) (by simp)
  · exact key 3 (by norm_num) (by rw [hu, pow_succ, neg_sq, gi_sq]; ring)
  · exact key 2 (by norm_num) (by rw [hu, neg_sq, gi_sq])
  · exact key 1 (by norm_num) (by rw [hu, pow_one])

omit hp8 in
lemma card_fiber_eq_one {z : GaussianInt} (hz : FourVal z) :
    (fiber χ z).card = (fiber χ 1).card := by
  obtain ⟨c, hc0, hc⟩ := exists_char_eq hχ hz
  refine card_nbij' (fun x => c⁻¹ * x) (fun x => c * x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_coe, mem_fiber] at *
    have : χ c * χ c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    rw [map_mul, hx, ← hc, mul_comm]; exact this
  · intro x hx; rw [mem_coe, mem_fiber] at *; rw [map_mul, hx, hc, mul_one]
  · intro x _; show c * (c⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  · intro x _; show c⁻¹ * (c * x) = x; rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

/-- Every class has `Q = (p - 1)/4` elements. -/
theorem card_fiber {z : GaussianInt} (hz : FourVal z) : (fiber χ z).card = Q p := by
  have h := sum_univ_fibers hχ (fun x : ZMod p => if x = 0 then 0 else (1 : ℕ)) (by simp)
  have hf : ∀ w : GaussianInt, w ≠ 0 →
      ∑ x ∈ fiber χ w, (if x = 0 then 0 else (1 : ℕ)) = (fiber χ w).card := by
    intro w hw
    rw [card_eq_sum_ones]
    exact sum_congr rfl fun x hx => by simp [ne_zero_of_mem_fiber hw hx]
  rw [hf 1 one_ne_zero, hf gi (by decide), hf (-1) (by decide), hf (-gi) (by decide),
    card_fiber_eq_one hχ (Or.inr (Or.inl rfl)), card_fiber_eq_one hχ (Or.inr (Or.inr (Or.inl rfl))),
    card_fiber_eq_one hχ (Or.inr (Or.inr (Or.inr rfl)))] at h
  have hl : ∑ x : ZMod p, (if x = 0 then 0 else (1 : ℕ)) = p - 1 := by
    rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one,
      filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  rw [hl] at h
  rw [card_fiber_eq_one hχ hz]
  have := mod_eight_aux hp8
  omega

omit hp8 hχ in
lemma neg_half_odd (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    (Odd (-x).val ↔ ¬ Odd x.val) := by
  rw [val_neg_of_ne_zero' hx, Nat.odd_sub (ZMod.val_lt x).le]
  have := odd_p hp2
  simp [this]

/-- Half of each class lies in `(0, p/2)`. -/
theorem card_half_fiber {z : GaussianInt} (hz : FourVal z) :
    2 * ((fiber χ z).filter fun x => 2 * x.val < p).card = Q p := by
  have hz0 : z ≠ 0 := by rcases hz with rfl | rfl | rfl | rfl <;> decide
  rw [two_mul_card_filter_of_neg _ (fun x hx => neg_mem_fiber hp8 hχ hx)
    (fun x hx => neg_half_iff (hp2_of hp8) (ne_zero_of_mem_fiber hz0 hx)), card_fiber hp8 hχ hz]

/-- Half of each class is odd. -/
theorem card_odd_fiber {z : GaussianInt} (hz : FourVal z) :
    2 * ((fiber χ z).filter fun x => Odd x.val).card = Q p := by
  have hz0 : z ≠ 0 := by rcases hz with rfl | rfl | rfl | rfl <;> decide
  rw [two_mul_card_filter_of_neg _ (fun x hx => neg_mem_fiber hp8 hχ hx)
    (fun x hx => neg_half_odd (hp2_of hp8) (ne_zero_of_mem_fiber hz0 hx)), card_fiber hp8 hχ hz]

omit hp8 hχ in
/-- `R_r` counts the elements of the class of `i^r` in `(0, p/4)`. -/
theorem R_eq (r : ℕ) : R χ r = ((fiber χ (gi ^ r)).filter fun x => 4 * x.val < p).card := by
  have hz0 : gi ^ r ≠ 0 := pow_ne_zero _ (by decide)
  unfold R
  refine card_nbij' (fun n => (n : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn ⊢
    rw [mem_fiber, ZMod.val_natCast_of_lt hn.1]
    exact ⟨hn.2.2.2, hn.2.2.1⟩
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_fiber] at hx ⊢
    refine ⟨ZMod.val_lt x, val_pos_of_ne_zero (ne_zero_of_mem_fiber hz0 (mem_fiber.2 hx.1)),
      hx.2, by rw [ZMod.natCast_zmod_val]; exact hx.1⟩
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn
    exact ZMod.val_natCast_of_lt hn.1
  · intro x _; exact ZMod.natCast_zmod_val x

omit hp8 hχ in
lemma val_half_of_even {y : ZMod p} (hy : Even y.val) : (2 * (y.val / 2 : ℕ) : ZMod p) = y := by
  obtain ⟨k, hk⟩ := hy
  rw [show y.val / 2 = k by omega, ← ZMod.natCast_zmod_val y, hk]; push_cast; ring

/-- The even elements of a class in `(0, p/2)` are the doubles of the class of `χ(2) z` in
`(0, p/4)`. -/
theorem card_even_half (z : GaussianInt) :
    ((fiber χ z).filter fun x => 2 * x.val < p ∧ Even x.val).card =
      ((fiber χ (χ 2 * z)).filter fun x => 4 * x.val < p).card := by
  have hsq := char_two_sq hp8 hχ
  have hp2 := hp2_of hp8
  refine card_nbij' (fun y => ((y.val / 2 : ℕ) : ZMod p)) (fun x => 2 * x) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hy ⊢
    obtain ⟨hyz, hyl, hye⟩ := hy
    have hlt : y.val / 2 < p := by omega
    rw [ZMod.val_natCast_of_lt hlt]
    refine ⟨?_, by omega⟩
    have h2 : χ 2 * χ ((y.val / 2 : ℕ) : ZMod p) = z := by
      rw [← map_mul, val_half_of_even hye, hyz]
    linear_combination (χ 2) * h2 - χ ((y.val / 2 : ℕ) : ZMod p) * hsq
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hx ⊢
    have hv := val_two_mul_of_lt (show 2 * x.val < p by omega)
    rw [hv, map_mul, hx.1]
    refine ⟨by linear_combination z * hsq, by omega, even_two_mul _⟩
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq] at hy
    exact val_half_of_even hy.2.2
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq] at hx
    have hv := val_two_mul_of_lt (show 2 * x.val < p by omega)
    show (((2 * x).val / 2 : ℕ) : ZMod p) = x
    rw [hv, show 2 * x.val / 2 = x.val by omega, ZMod.natCast_zmod_val]

/-- `E_z` counts the odd elements in `(0, p/2)` of the class of `χ(2) z`. -/
theorem E_eq (z : GaussianInt) :
    E χ z = ((fiber χ (χ 2 * z)).filter fun x => 2 * x.val < p ∧ Odd x.val).card := by
  have hsq := char_two_sq hp8 hχ
  unfold E
  refine card_nbij' (fun y => ((y.val / 2 : ℕ) : ZMod p)) (fun x => 2 * x) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hy ⊢
    obtain ⟨hyz, hy4⟩ := hy
    have hye : Even y.val := Nat.even_iff.2 (by omega)
    have hlt : y.val / 2 < p := by have := ZMod.val_lt y; omega
    rw [ZMod.val_natCast_of_lt hlt]
    have h2 : χ 2 * χ ((y.val / 2 : ℕ) : ZMod p) = z := by
      rw [← map_mul, val_half_of_even hye, hyz]
    refine ⟨by linear_combination (χ 2) * h2 - χ ((y.val / 2 : ℕ) : ZMod p) * hsq,
      by have := ZMod.val_lt y; omega, Nat.odd_iff.2 (by omega)⟩
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hx ⊢
    have hv := val_two_mul_of_lt hx.2.1
    rw [hv, map_mul, hx.1]
    refine ⟨by linear_combination z * hsq, ?_⟩
    have := Nat.odd_iff.1 hx.2.2; omega
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq] at hy
    obtain ⟨_, h4⟩ := hy
    exact val_half_of_even (Nat.even_iff.2 (by omega))
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq] at hx
    have hv := val_two_mul_of_lt hx.2.1
    show (((2 * x).val / 2 : ℕ) : ZMod p) = x
    rw [hv, show 2 * x.val / 2 = x.val by omega, ZMod.natCast_zmod_val]

end Quartic

end QuarterSumLadder
