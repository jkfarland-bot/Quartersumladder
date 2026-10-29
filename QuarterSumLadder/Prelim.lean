module

public import QuarterSumLadder.Defs

@[expose] public section

/-!
# Half systems and the Gauss–Lehmer product

`gauss_product`: if a set `A` of representatives in `(0, p/2)` is carried into itself by the Gauss
map `x ↦ 2x` (for `⟨x⟩ < p/4`) or `x ↦ -2x` (otherwise), then
`2^{|A|} (-1)^{#{x ∈ A : ⟨x⟩ > p/4}} = 1`. This is the argument of Gauss's lemma as used by
E. Lehmer (*Generalizations of Gauss's lemma*, 1977).
-/

namespace QuarterSumLadder

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma odd_p (hp2 : p ≠ 2) : Odd p := hp.out.odd_of_ne_two hp2

lemma val_neg_of_ne_zero' {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := by
  rw [ZMod.neg_val, ite_eq_right_iff.mpr (fun h => absurd h hx)]

lemma val_pos_of_ne_zero {x : ZMod p} (hx : x ≠ 0) : 0 < x.val := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]; exact hx

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)

lemma val_two_mul_of_lt {x : ZMod p} (hx : 2 * x.val < p) : (2 * x).val = 2 * x.val := by
  have : (2 * x : ZMod p) = ((2 * x.val : ℕ) : ZMod p) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast_of_lt hx]

lemma neg_half_iff (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    2 * (-x).val < p ↔ ¬ 2 * x.val < p := by
  rw [val_neg_of_ne_zero' hx]
  have h1 := ZMod.val_lt x
  have h2 := val_pos_of_ne_zero hx
  obtain ⟨k, hk⟩ := odd_p hp2
  omega

/-- The Gauss map: `x ↦ 2x` if `⟨x⟩ < p/4`, and `x ↦ -2x` otherwise. -/
def gaussMap (x : ZMod p) : ZMod p := if 4 * x.val < p then 2 * x else -(2 * x)

lemma gaussMap_mem_half (hp2 : p ≠ 2) {x : ZMod p} (hx0 : x ≠ 0) (hx : 2 * x.val < p) :
    2 * (gaussMap x).val < p := by
  have hv := val_two_mul_of_lt hx
  have h2x : (2 * x : ZMod p) ≠ 0 := mul_ne_zero (two_ne_zero_zmod hp2) hx0
  unfold gaussMap
  split_ifs with h4
  · rw [hv]; omega
  · obtain ⟨k, hk⟩ := odd_p hp2
    rw [val_neg_of_ne_zero' h2x, hv]; omega

/-- **The Gauss–Lehmer product.** -/
theorem gauss_product (hp2 : p ≠ 2) (A : Finset (ZMod p))
    (hA : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p) (hφ : ∀ x ∈ A, gaussMap x ∈ A) :
    (2 : ZMod p) ^ A.card * (-1) ^ (A.filter fun x => ¬ 4 * x.val < p).card = 1 := by
  have h20 := two_ne_zero_zmod hp2
  have hinj : Set.InjOn gaussMap (A : Set (ZMod p)) := by
    intro x hx y hy hxy
    rw [mem_coe] at hx hy
    obtain ⟨hx0, hxl⟩ := hA x hx
    obtain ⟨hy0, hyl⟩ := hA y hy
    have key : x = y ∨ x = -y := by
      simp only [gaussMap] at hxy
      split_ifs at hxy
      · exact Or.inl (mul_left_cancel₀ h20 hxy)
      · right; apply mul_left_cancel₀ h20; rw [hxy]; ring
      · right; apply mul_left_cancel₀ h20; rw [mul_neg, ← hxy]; ring
      · left; exact mul_left_cancel₀ h20 (neg_injective hxy)
    rcases key with h | h
    · exact h
    · exfalso
      have := (neg_half_iff hp2 hy0).1
      rw [← h] at this
      exact this hxl hyl
  have himage : A.image gaussMap = A :=
    eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact hφ x hx)
      (by rw [card_image_of_injOn hinj])
  have hprod : ∏ x ∈ A, gaussMap x = ∏ x ∈ A, x := by
    calc ∏ x ∈ A, gaussMap x = ∏ y ∈ A.image gaussMap, y :=
          (prod_image (f := fun y => y) (fun x hx y hy h => hinj hx hy h)).symm
      _ = ∏ x ∈ A, x := by rw [himage]
  have hsplit : ∀ x ∈ A, gaussMap x = (if 4 * x.val < p then 1 else -1) * 2 * x := by
    intro x _; simp only [gaussMap]; split_ifs <;> ring
  rw [prod_congr rfl hsplit, prod_mul_distrib, prod_mul_distrib, prod_const, prod_ite,
    prod_const_one, one_mul, prod_const] at hprod
  have hP0 : ∏ x ∈ A, x ≠ 0 := prod_ne_zero_iff.2 fun x hx => (hA x hx).1
  have := (mul_eq_right₀ hP0).1 hprod
  linear_combination this

end QuarterSumLadder
