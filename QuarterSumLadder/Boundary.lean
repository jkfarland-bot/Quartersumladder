module

public import QuarterSumLadder.Ladder

@[expose] public section

/-!
# Weight two beyond the first rung

* `comparison` (Paper IV, Lemma 8.1): `p(c₀ - c₁) ≡ -4(x - y) (mod 16)` (the paper uses it when
  `χ(2) = 1`; the congruence holds for every even quartic `χ`);
* `b2_trichotomy` (Theorem 8.2): with `N(B₂) = c₀² + c₁²`, `v_λ(B_{2,χ})` is `5` if `χ(2) = -1`,
  `6` if `χ(2) = 1` and `p ≡ 9 (mod 16)`, and at least `7` if `χ(2) = 1` and `p ≡ 1 (mod 16)`.
-/

namespace QuarterSumLadder

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- Squares modulo `16`. -/
lemma sq_mod_sixteen (v : ℕ) :
    (((v : ℤ) ^ 2 : ℤ) : ZMod 16) = (if v % 2 = 1 then 1 else 0) +
      8 * (if v % 8 = 3 ∨ v % 8 = 5 then 1 else 0) + 4 * (if v % 4 = 2 then 1 else 0) := by
  have h2 : v % 2 = v % 16 % 2 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  have h4 : v % 4 = v % 16 % 4 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  have h8 : v % 8 = v % 16 % 8 := (Nat.mod_mod_of_dvd v (by norm_num)).symm
  push_cast
  rw [show ((v : ZMod 16)) = ((v % 16 : ℕ) : ZMod 16) by rw [ZMod.natCast_mod], h2, h4, h8]
  have hlt := Nat.mod_lt v (show 0 < 16 by norm_num)
  interval_cases (v % 16) <;> decide

/-- `#{0 < m < p : m ≡ r (mod 8)} = (p - 1)/8` for `1 ≤ r ≤ 7`. -/
lemma card_mod_eight (hp8 : p % 8 = 1) {r : ℕ} (hr1 : 1 ≤ r) (hr7 : r ≤ 7) :
    (univ.filter fun x : ZMod p => x.val % 8 = r).card = (p - 1) / 8 := by
  rw [show (p - 1) / 8 = (range ((p - 1) / 8)).card by simp]
  refine card_nbij' (fun x => x.val / 8) (fun k => ((8 * k + r : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hx ⊢
    have := ZMod.val_lt x; omega
  · intro k hk
    simp only [coe_range, Set.mem_Iio, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : 8 * (x.val / 8) + r = x.val := by omega
    show ((8 * (x.val / 8) + r : ℕ) : ZMod p) = x
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    show ((8 * k + r : ℕ) : ZMod p).val / 8 = k
    rw [ZMod.val_natCast_of_lt (by omega)]; omega

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

omit hp8 hχ in
/-- `U_z ≡ #(odd) + 8 #(≡ ±3 mod 8) + 4 E_z (mod 16)`. -/
lemma U_mod_sixteen (z : GaussianInt) :
    ((U χ z : ℤ) : ZMod 16) =
      (((fiber χ z).filter fun x => x.val % 2 = 1).card : ZMod 16) +
        8 * (((fiber χ z).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card : ZMod 16) +
          4 * (E χ z : ZMod 16) := by
  unfold U E
  rw [Int.cast_sum, sum_congr rfl (fun x _ => sq_mod_sixteen x.val), sum_add_distrib,
    sum_add_distrib, ← mul_sum, ← mul_sum, sum_boole, sum_boole, sum_boole]

/-- **The comparison lemma** (Paper IV, Lemma 8.1). -/
theorem comparison :
    (p : ℤ) * (c0 χ - c1 χ) ≡ -4 * ((Omega χ).re - (Omega χ).im) [ZMOD 16] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 16).1 ?_
  have hpc : (p : ℤ) * (c0 χ - c1 χ) = (U χ 1 - U χ (-1)) - (U χ gi - U χ (-gi)) := by
    rw [mul_sub, p_mul_c0 hp8 hχ, p_mul_c1 hp8 hχ]
  rw [hpc]; push_cast
  rw [U_mod_sixteen (χ := χ), U_mod_sixteen (χ := χ), U_mod_sixteen (χ := χ),
    U_mod_sixteen (χ := χ)]
  -- odd counts agree
  have o1 := odd_card hp8 hχ (z := 1) (Or.inl rfl)
  have oi := odd_card hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have om := odd_card hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have omi := odd_card hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  have e1 : ((((fiber χ 1).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 16) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by congr 1; omega
  have e2 : ((((fiber χ gi).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 16) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by congr 1; omega
  have e3 : ((((fiber χ (-gi)).filter fun x => x.val % 2 = 1).card : ℕ) : ZMod 16) =
      (((fiber χ (-1)).filter fun x => x.val % 2 = 1).card : ℕ) := by congr 1; omega
  rw [e1, e2, e3]
  -- the counts of `m ≡ ±3 (mod 8)`
  have hT := sum_univ_fibers hχ
    (fun x : ZMod p => if x.val % 8 = 3 ∨ x.val % 8 = 5 then (1 : ℕ) else 0) (by simp)
  simp only [← card_filter] at hT
  have h35 : (univ.filter fun x : ZMod p => x.val % 8 = 3 ∨ x.val % 8 = 5).card =
      2 * ((p - 1) / 8) := by
    rw [filter_or, card_union_of_disjoint (disjoint_filter.2 fun x _ h3 h5 => by omega),
      card_mod_eight hp8 (r := 3) (by norm_num) (by norm_num),
      card_mod_eight hp8 (r := 5) (by norm_num) (by norm_num)]
    ring
  rw [h35] at hT
  set T1 := ((fiber χ 1).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  set Ti := ((fiber χ gi).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  set Tm := ((fiber χ (-1)).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  set Tmi := ((fiber χ (-gi)).filter fun x => x.val % 8 = 3 ∨ x.val % 8 = 5).card
  have hT' : (T1 : ZMod 16) + Ti + Tm + Tmi = 2 * (((p - 1) / 8 : ℕ) : ZMod 16) := by
    have := congrArg (fun n : ℕ => (n : ZMod 16)) hT; push_cast at this; exact this.symm
  -- `E_z = Q/2 - R(z)`
  have a := E_add_R hp8 hχ (z := 1) (Or.inl rfl)
  have b := E_add_R hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have c := E_add_R hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have d := E_add_R hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  rw [← R_zero] at a; rw [← R_one] at b; rw [← R_two] at c; rw [← R_three] at d
  have hE : (E χ 1 : ZMod 16) - E χ (-1) - (E χ gi - E χ (-gi)) =
      -((R χ 0 : ZMod 16) - R χ 2 - (R χ 1 - R χ 3)) := by
    have a' := congrArg (fun n : ℕ => (n : ZMod 16)) a
    have b' := congrArg (fun n : ℕ => (n : ZMod 16)) b
    have c' := congrArg (fun n : ℕ => (n : ZMod 16)) c
    have d' := congrArg (fun n : ℕ => (n : ZMod 16)) d
    push_cast at a' b' c' d'
    linear_combination a' - c' - b' + d'
  have hre : ((Omega χ).re : ZMod 16) = (R χ 0 : ZMod 16) - R χ 2 := by
    show (((R χ 0 : ℤ) - R χ 2 : ℤ) : ZMod 16) = _; push_cast; ring
  have him : ((Omega χ).im : ZMod 16) = (R χ 1 : ZMod 16) - R χ 3 := by
    show (((R χ 1 : ℤ) - R χ 3 : ℤ) : ZMod 16) = _; push_cast; ring
  rw [hre, him]
  have h16 : (16 : ZMod 16) = 0 := rfl
  linear_combination 4 * hE + 8 * hT' + (((p - 1) / 8 : ℕ) - Ti - Tm) * h16

/-- **The weight-two trichotomy** (Paper IV, Theorem 8.2), with `N(B₂) = c₀² + c₁²`. -/
theorem b2_trichotomy :
    (χ 2 = -1 → (32 : ℤ) ∣ (B2 χ).norm ∧ ¬ (64 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 9 → (64 : ℤ) ∣ (B2 χ).norm ∧ ¬ (128 : ℤ) ∣ (B2 χ).norm) ∧
      (χ 2 = 1 → p % 16 = 1 → (128 : ℤ) ∣ (B2 χ).norm) := by
  obtain ⟨h0, h1⟩ := coords_mod_eight hp8 hχ
  have hq := quarter_law hp8 hχ
  have hnorm : (B2 χ).norm = c0 χ ^ 2 + c1 χ ^ 2 := norm_eq _
  rw [Int.ModEq] at h0 h1
  rw [hnorm]
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 => ?_⟩
  · rw [hw] at hq
    have hodd : Odd (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · rw [he.neg_one_pow] at hq; exact absurd hq (by decide)
      · exact ho
    obtain ⟨k, hk⟩ := hodd
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    push_cast at hk'
    obtain ⟨a, ha⟩ : ∃ a, c0 χ = 4 * a ∧ a % 2 = 1 := ⟨c0 χ / 4, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, c1 χ = 4 * b ∧ b % 2 = 1 := ⟨c1 χ / 4, by omega⟩
    rw [ha.1, hb.1, show (4 * a) ^ 2 + (4 * b) ^ 2 = 16 * (a ^ 2 + b ^ 2) by ring]
    have := sq_add_sq_odd ha.2 hb.2
    omega
  · rw [hw] at hq
    have heven : Even (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · exact he
      · rw [ho.neg_one_pow] at hq; exact absurd hq (by decide)
    obtain ⟨k, hk⟩ := heven
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = k + k := by exact_mod_cast hk
    push_cast at hk'
    obtain ⟨a, ha⟩ : ∃ a, c0 χ = 8 * a := ⟨c0 χ / 8, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, c1 χ = 8 * b := ⟨c1 χ / 8, by omega⟩
    have hcmp := comparison hp8 hχ
    obtain ⟨_, _, hxy⟩ := (coord_parity hp8 hχ).2 hw
    have hpq := mod_eight_aux hp8
    have hQ : (Q p : ℤ) % 4 = 2 := by unfold Q; omega
    rw [Int.ModEq, ha, hb] at hcmp
    obtain ⟨t, ht⟩ : ∃ t, (p : ℤ) = 8 * t + 1 := ⟨(p : ℤ) / 8, by omega⟩
    rw [ht] at hcmp
    have hc : (8 * t + 1) * (8 * a - 8 * b) = 8 * (a - b) + 64 * (t * (a - b)) := by ring
    rw [hc] at hcmp
    rw [ha, hb, show (8 * a) ^ 2 + (8 * b) ^ 2 = 64 * (a ^ 2 + b ^ 2) by ring]
    have h1 := sq_mod_two a; have h2 := sq_mod_two b
    refine ⟨dvd_mul_right 64 _, fun h => ?_⟩
    omega
  · rw [hw] at hq
    have heven : Even (R χ 1 + R χ 3) := by
      rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
      · exact he
      · rw [ho.neg_one_pow] at hq; exact absurd hq (by decide)
    obtain ⟨k, hk⟩ := heven
    have hk' : ((R χ 1 + R χ 3 : ℕ) : ℤ) = k + k := by exact_mod_cast hk
    push_cast at hk'
    obtain ⟨a, ha⟩ : ∃ a, c0 χ = 8 * a := ⟨c0 χ / 8, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, c1 χ = 8 * b := ⟨c1 χ / 8, by omega⟩
    have hcmp := comparison hp8 hχ
    obtain ⟨_, _, hxy⟩ := (coord_parity hp8 hχ).2 hw
    have hpq := mod_eight_aux hp8
    have hQ : (Q p : ℤ) % 4 = 0 := by unfold Q; omega
    rw [Int.ModEq, ha, hb] at hcmp
    obtain ⟨t, ht⟩ : ∃ t, (p : ℤ) = 8 * t + 1 := ⟨(p : ℤ) / 8, by omega⟩
    rw [ht] at hcmp
    have hc : (8 * t + 1) * (8 * a - 8 * b) = 8 * (a - b) + 64 * (t * (a - b)) := by ring
    rw [hc] at hcmp
    rw [ha, hb, show (8 * a) ^ 2 + (8 * b) ^ 2 = 64 * (a ^ 2 + b ^ 2) by ring]
    have h1 := sq_mod_two a; have h2 := sq_mod_two b
    omega

end Quartic

end QuarterSumLadder

namespace QuarterSumLadder

/-- `v_λ(z) = k` from `2^k ∣ N(z)` and `2^{k+1} ∤ N(z)`. -/
lemma vlam_eq_of_dvd {z : GaussianInt} {k : ℕ} (h1 : (2 : ℤ) ^ k ∣ z.norm)
    (h2 : ¬ (2 : ℤ) ^ (k + 1) ∣ z.norm) : vlam z = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : z.norm ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have a := (padicValInt_dvd_iff (p := 2) k z.norm).1 (by exact_mod_cast h1)
  have b : ¬ (k + 1 ≤ padicValInt 2 z.norm) := fun hle =>
    h2 (by exact_mod_cast (padicValInt_dvd_iff (p := 2) (k + 1) z.norm).2 (Or.inr hle))
  unfold vlam
  rcases a with a | a
  · exact absurd a hne
  · omega

/-- `k ≤ v_λ(z)` from `2^k ∣ N(z)`, for `z ≠ 0`. -/
lemma le_vlam_of_dvd {z : GaussianInt} (hz : z ≠ 0) {k : ℕ} (h1 : (2 : ℤ) ^ k ∣ z.norm) :
    k ≤ vlam z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : z.norm ≠ 0 := by rwa [Ne, Zsqrtd.norm_eq_zero (fun n h => by nlinarith [sq_nonneg n])]
  rcases (padicValInt_dvd_iff (p := 2) k z.norm).1 (by exact_mod_cast h1) with a | a
  · exact absurd a hne
  · exact a

variable {p : ℕ} [hp : Fact p.Prime] {χ : MulChar (ZMod p) GaussianInt}
  (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

/-- **The first three thresholds** (Paper IV, Theorem 5.2) in valuation form: `v_λ(Ω) = 1` if
`χ(2) = -1`, `v_λ(Ω) = 2` if `χ(2) = 1` and `p ≡ 9 (mod 16)`, and `v_λ(Ω) ≥ 3` if `χ(2) = 1`,
`p ≡ 1 (mod 16)` and `Ω ≠ 0` (which holds since `h⁻(K) = 2N(Ω) ≠ 0`, not formalized). -/
theorem vlam_Omega :
    (χ 2 = -1 → vlam (Omega χ) = 1) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (Omega χ) = 2) ∧
      (χ 2 = 1 → p % 16 = 1 → Omega χ ≠ 0 → 3 ≤ vlam (Omega χ)) := by
  obtain ⟨a, b, c⟩ := first_thresholds hp8 hχ
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 hz => ?_⟩
  · obtain ⟨h1, h2⟩ := a hw; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · obtain ⟨h1, h2⟩ := b hw h16; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · exact le_vlam_of_dvd hz (by simpa using c hw h16)

/-- **The weight-two trichotomy** (Paper IV, Theorem 8.2) in valuation form: `v_λ(B_{2,χ}) = 5` if
`χ(2) = -1`, `= 6` if `χ(2) = 1` and `p ≡ 9 (mod 16)`, and `≥ 7` if `χ(2) = 1`, `p ≡ 1 (mod 16)` and
`B_{2,χ} ≠ 0` (which holds since `L(-1, χ) ≠ 0`, not formalized). -/
theorem vlam_B2 :
    (χ 2 = -1 → vlam (B2 χ) = 5) ∧ (χ 2 = 1 → p % 16 = 9 → vlam (B2 χ) = 6) ∧
      (χ 2 = 1 → p % 16 = 1 → B2 χ ≠ 0 → 7 ≤ vlam (B2 χ)) := by
  obtain ⟨a, b, c⟩ := b2_trichotomy hp8 hχ
  refine ⟨fun hw => ?_, fun hw h16 => ?_, fun hw h16 hz => ?_⟩
  · obtain ⟨h1, h2⟩ := a hw; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · obtain ⟨h1, h2⟩ := b hw h16; exact vlam_eq_of_dvd (by simpa using h1) (by simpa using h2)
  · exact le_vlam_of_dvd hz (by simpa using c hw h16)

end QuarterSumLadder
