/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import order.liminf_limsup
import topology.instances.nnreal

/-!
# Limsup

We prove some auxiliary results about limsups, infis, and suprs.

## Main Results

* `ennreal.le_infi_mul_infi` : if `f g : ι → ennreal` take real values, and
  `∀ (i j : ι), a ≤ f i * g j`, then `a ≤ infi f * infi g`.
* `ennreal.infi_mul_le_mul_infi` : if `u v : ι → ennreal` take real values and are antitone, then 
  `infi (u * v) ≤ infi u * infi v`. 
* `ennreal.limsup_mul_le` : if `u v : ℕ → ℝ≥0∞` are bounded above by real numbers, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top`. 
* `real.limsup_mul_le` : If `u v : ℕ → ℝ` are nonnegative and bounded above, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top `.

## Tags

limsup, real, nnreal, ennreal
-/

noncomputable theory

namespace filter

/-- If `u : β → α` is nonnegative and `is_bounded_under has_le.le f u`, then `0 ≤ limsup u f`. -/
lemma limsup_nonneg_of_nonneg {α β : Type*} [has_zero α] [conditionally_complete_linear_order α]
  {f : filter β} [hf_ne_bot : f.ne_bot] {u : β → α}
  (hfu : is_bounded_under has_le.le f u) (h : 0 ≤ u) : 0 ≤ limsup u f := 
le_limsup_of_frequently_le (frequently_of_forall h) hfu

/-- If `filter.limsup u at_top ≤ x`, then for all `ε > 0`, eventually we have `u a < x + ε`.  -/
lemma eventually_lt_add_pos_of_limsup_le {α : Type*} [preorder α] {x : ℝ} {u : α → ℝ} 
  (hu_bdd : is_bounded_under has_le.le at_top u) (hu : filter.limsup u at_top ≤ x) 
  {ε : ℝ} (hε : 0 < ε) : ∀ᶠ (a : α) in at_top, u a < x + ε :=
eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

/-- If `filter.limsup u at_top ≤ x`, then for all `ε > 0`, there exists a positive natural
  number `n` such that `u n < x + ε`.  -/
lemma exists_lt_of_limsup_le {x : ℝ} {u : ℕ → ℝ} (hu_bdd : is_bounded_under has_le.le at_top u)
  (hu : filter.limsup u at_top ≤ x) {ε : ℝ} (hε : 0 < ε) :
  ∃ n : pnat, u n < x + ε :=
begin
  have h : ∀ᶠ (a : ℕ) in at_top, u a < x + ε := eventually_lt_add_pos_of_limsup_le hu_bdd hu hε,
  simp only [eventually_at_top, ge_iff_le] at h,
  obtain ⟨n, hn⟩ := h,
  exact ⟨⟨n + 1, nat.succ_pos _⟩, hn (n + 1) (nat.le_succ _)⟩,
end

end filter

open filter
open_locale topological_space nnreal ennreal

lemma bdd_above.is_bounded_under {α : Type*} [preorder α] {u : α → ℝ} 
  (hu_bdd : bdd_above (set.range u)) : is_bounded_under has_le.le at_top u :=
begin
  obtain ⟨b, hb⟩ := hu_bdd,
  use b,
  simp only [mem_upper_bounds, set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff'] at hb,
  exact eventually_map.mpr (eventually_of_forall hb)
end

namespace nnreal

lemma coe_limsup {u : ℕ → ℝ} (hu : 0 ≤ u) :
  limsup u at_top = (((limsup (λ n, (⟨u n, hu n⟩ : ℝ≥0)) at_top) : ℝ≥0) : ℝ) :=
begin
  simp only [limsup_eq],
  norm_cast,
  apply congr_arg,
  ext x,
  simp only [set.mem_set_of_eq, set.mem_image],
  refine ⟨λ hx, _, λ hx, _⟩,
  { have hx' := hx,
    simp only [eventually_at_top, ge_iff_le] at hx',
    obtain ⟨N, hN⟩ := hx',
    have hx0 : 0 ≤ x := le_trans (hu N) (hN N (le_refl _)),
    exact ⟨⟨x, hx0⟩, hx, rfl⟩, },
  { obtain ⟨y, hy, hyx⟩ := hx,
    simp_rw [← nnreal.coe_le_coe, nnreal.coe_mk, hyx] at hy,
    exact hy }
end

/-- If `u : ℕ → ℝ` is bounded above an nonnegative, it is also bounded above when regarded as 
  a function to `ℝ≥0`. -/
lemma bdd_above' {u : ℕ → ℝ} (hu0 : 0 ≤ u) (hu_bdd: bdd_above (set.range u)) :
  bdd_above (set.range (λ (n : ℕ), (⟨u n, hu0 n⟩ : ℝ≥0))) :=
begin
  obtain ⟨B, hB⟩ := hu_bdd,
  simp only [mem_upper_bounds, set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] at hB,
  have hB0 : 0 ≤ B := le_trans (hu0 0) (hB 0),
  use (⟨B, hB0⟩ : ℝ≥0),
  simp only [mem_upper_bounds, set.mem_range, forall_exists_index, subtype.forall, 
    subtype.mk_le_mk],
  rintros x - n hn,
  rw ← hn,
  exact hB n,
end

lemma eventually_le_of_bdd_above' {u : ℕ → ℝ≥0} (hu : bdd_above (set.range u)) :
  {a : ℝ≥0 | ∀ᶠ (n : ℕ) in at_top, u n ≤ a}.nonempty :=
begin
  obtain ⟨B, hB⟩ := hu,
  simp only [mem_upper_bounds, set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] 
    at hB,
  exact ⟨B, eventually_of_forall hB⟩,
end

end nnreal

namespace ennreal

/-- If `f g : ι → ℝ≥0∞` take real values, and `∀ (i j : ι), a ≤ f i * g j`, then
  `a ≤ infi f * infi g`. -/
lemma le_infi_mul_infi {ι : Sort*} [hι : nonempty ι] {a : ℝ≥0∞} {f g : ι → ℝ≥0∞} 
  (hf : ∀ x, f x ≠ ⊤) (hg : ∀ x, g x ≠ ⊤) (H : ∀ (i j : ι), a ≤ f i * g j) :
  a ≤ infi f * infi g :=
begin
  have hg' : infi g ≠ ⊤,
  { rw [ne.def, infi_eq_top, not_forall], exact ⟨hι.some, hg hι.some⟩ },
  rw infi_mul hg',
  refine le_infi _,
  intros i,
  rw mul_infi (hf i),
  exact le_infi (H i),
  { apply_instance },
  { apply_instance },
end

/-- If `u v : ι → ℝ≥0∞` take real values and are antitone, then `infi (u * v) ≤ infi u * infi v`. -/
lemma infi_mul_le_mul_infi {u v : ℕ → ℝ≥0∞} (hu_top : ∀ x, u x ≠ ⊤) (hu : antitone u) 
  (hv_top : ∀ x, v x ≠ ⊤) (hv : antitone v) : infi (u * v) ≤ infi u * infi v :=
begin
  rw infi_le_iff,
  intros b hb,
  apply le_infi_mul_infi hu_top hv_top,
  intros m n,
  exact le_trans (hb (max m n)) (mul_le_mul (hu (le_max_left _ _)) (hv (le_max_right _ _))),
end

lemma supr_tail_seq (u : ℕ → ℝ≥0∞) (n : ℕ) : 
  (⨆ (k : ℕ) (x : n ≤ k), u k) = ⨆ (k : { k : ℕ // n ≤ k}), u k :=
by rw supr_subtype; refl

lemma le_supr_prop (u : ℕ → ℝ≥0∞) {n k : ℕ} (hnk : n ≤ k) :
  u k ≤ ⨆ (k : ℕ) (x : n ≤ k), u k :=
begin
  refine le_supr_of_le k _,
  rw csupr_pos hnk,
  exact le_refl _,
end

/-- The function sending `n : ℕ` to `⨆ (k : ℕ) (x : n ≤ k), u k` is antitone. -/
lemma antitone.supr {u : ℕ → ℝ≥0∞} :
  antitone (λ (n : ℕ), ⨆ (k : ℕ) (x : n ≤ k), u k) :=
begin
  apply antitone_nat_of_succ_le _,
  intros n,
  rw [supr₂_le_iff],
  intros k hk,
  exact le_supr_prop u (le_trans (nat.le_succ n) hk),
end

/-- If `u : ℕ → ℝ≥0∞` is bounded above by a real number, then its `supr` is finite. -/
lemma supr_le_top_of_bdd_above {u : ℕ → ℝ≥0∞} {B : ℝ≥0} (hu : ∀ x, u x ≤ B) (n : ℕ):
  (⨆ (k : ℕ) (x : n ≤ k), u k) ≠ ⊤ :=
begin
  have h_le : (⨆ (k : ℕ) (x : n ≤ k), u k) ≤ B,
  { rw supr_tail_seq,
    exact supr_le (λ m, hu m), },
  exact ne_top_of_le_ne_top coe_ne_top h_le
end

/-- If `u v : ℕ → ℝ≥0∞` are bounded above by real numbers, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top`. -/
lemma limsup_mul_le {u v : ℕ → ℝ≥0∞} {Bu Bv : ℝ≥0} (hu : ∀ x, u x ≤ Bu) (hv : ∀ x, v x ≤ Bv) :
  filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top :=
begin
  have h_le : (⨅ (n : ℕ), ⨆ (i : ℕ) (x : n ≤ i), u i * v i) ≤ 
    (⨅ (n : ℕ), (⨆ (i : ℕ) (x : n ≤ i), u i) *(⨆ (j : ℕ) (x : n ≤ j), v j)),
  { refine infi_mono _,
    intros n,
    apply supr_le _,
    intros k,
    apply supr_le _,
    intros hk, 
    exact mul_le_mul (le_supr_prop u hk) (le_supr_prop v hk), },
  simp only [filter.limsup_eq_infi_supr_of_nat, ge_iff_le, pi.mul_apply],
  exact le_trans h_le (infi_mul_le_mul_infi (supr_le_top_of_bdd_above hu) antitone.supr
    (supr_le_top_of_bdd_above hv) antitone.supr),
end

lemma coe_limsup {u : ℕ → ℝ≥0} (hu : bdd_above (set.range u)) :
  (((limsup u at_top) : ℝ≥0) : ℝ≥0∞) = limsup (λ n, (u n : ℝ≥0∞)) at_top :=
begin
  simp only [limsup_eq],
  rw [coe_Inf (nnreal.eventually_le_of_bdd_above' hu), Inf_eq_infi],
  simp only [eventually_at_top, ge_iff_le, set.mem_set_of_eq, infi_exists],
  { apply le_antisymm,
    { apply le_infi₂ _,
      intros x n,
      apply le_infi _,
      intro h,
      cases x,
      { simp only [none_eq_top, le_top], },
      { simp only [some_eq_coe, coe_le_coe] at h,
        exact infi₂_le_of_le x n (infi_le_of_le h (le_refl _)) }},
    { apply le_infi₂ _,
      intros x n,
      apply le_infi _,
      intro h,
      refine infi₂_le_of_le x n _,
      simp_rw coe_le_coe,
      exact infi_le_of_le h (le_refl _) }},
end

lemma coe_limsup' {u : ℕ → ℝ} (hu : bdd_above (set.range u)) (hu0 : 0 ≤ u) :
  (limsup (λ n, ((coe : ℝ≥0 → ℝ≥0∞) (⟨u n, hu0 n⟩ : ℝ≥0))) at_top) =
  (coe : ℝ≥0 → ℝ≥0∞) (⟨limsup u at_top, limsup_nonneg_of_nonneg hu.is_bounded_under hu0⟩ : ℝ≥0) :=
by rw [← ennreal.coe_limsup (nnreal.bdd_above' hu0 hu), ennreal.coe_eq_coe, ← nnreal.coe_eq,
  subtype.coe_mk, nnreal.coe_limsup]

end ennreal


namespace real

/-- If `u v : ℕ → ℝ` are nonnegative and bounded above, then `u * v` is bounded above. -/
lemma range_bdd_above_mul {u v : ℕ → ℝ} (hu : bdd_above (set.range u)) (hu0 : 0 ≤ u)
   (hv : bdd_above (set.range v)) (hv0 : 0 ≤ v) :  bdd_above (set.range (u * v)) :=
begin
  obtain ⟨bu, hbu⟩ := hu,
  obtain ⟨bv, hbv⟩ := hv,
  use bu*bv,
  simp only [mem_upper_bounds, set.mem_range, pi.mul_apply, forall_exists_index,
    forall_apply_eq_imp_iff'] at hbu hbv ⊢,
  intros n,
  exact mul_le_mul (hbu n) (hbv n) (hv0 n) (le_trans (hu0 n) (hbu n)),
end

/-- If `u v : ℕ → ℝ` are nonnegative and bounded above, then
  `filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top `.-/
lemma limsup_mul_le {u v : ℕ → ℝ} (hu_bdd : bdd_above (set.range u)) (hu0 : 0 ≤ u) 
  (hv_bdd : bdd_above (set.range v)) (hv0 : 0 ≤ v) :
  filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top :=
begin
  have h_bdd : bdd_above (set.range (u * v)),
  { exact range_bdd_above_mul hu_bdd hu0 hv_bdd hv0 },
  have hc : ∀ n : ℕ, (⟨u n * v n, (mul_nonneg (hu0 n) (hv0 n))⟩ : ℝ≥0) = ⟨u n, hu0 n⟩*⟨v n, hv0 n⟩,
  { intro n, simp only [nonneg.mk_mul_mk], },
  rw [← nnreal.coe_mk _ (limsup_nonneg_of_nonneg h_bdd.is_bounded_under (mul_nonneg hu0 hv0)),
    ← nnreal.coe_mk _ (limsup_nonneg_of_nonneg hu_bdd.is_bounded_under hu0),
    ← nnreal.coe_mk _ (limsup_nonneg_of_nonneg hv_bdd.is_bounded_under hv0),
    ← nnreal.coe_mul, nnreal.coe_le_coe, ← ennreal.coe_le_coe, ennreal.coe_mul],
  simp only [← ennreal.coe_limsup', pi.mul_apply, hc, ennreal.coe_mul],
  obtain ⟨Bu, hBu⟩ := hu_bdd,
  obtain ⟨Bv, hBv⟩ := hv_bdd,
  simp only [mem_upper_bounds, set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] 
    at hBu hBv,
  have hBu_0 : 0 ≤ Bu := le_trans (hu0 0) (hBu 0),
  have hBu' : ∀ (n : ℕ), (⟨u n, hu0 n⟩ : ℝ≥0)  ≤ (⟨Bu, hBu_0⟩ : ℝ≥0),
  { simp only [← nnreal.coe_le_coe, nnreal.coe_mk], exact hBu },
  have hBv_0 : 0 ≤ Bv := le_trans (hv0 0) (hBv 0),
  have hBv' : ∀ (n : ℕ), (⟨v n, hv0 n⟩ : ℝ≥0) ≤ (⟨Bv, hBv_0⟩ : ℝ≥0),
  { simp only [← nnreal.coe_le_coe, nnreal.coe_mk], exact hBv },
  simp_rw ← ennreal.coe_le_coe at hBu' hBv',
  exact ennreal.limsup_mul_le hBu' hBv',
end

-- Alternative proof of limsup_mul_le
lemma limsup_mul_le' {u v : ℕ → ℝ} (hu_bdd : bdd_above (set.range u)) (hu0 : 0 ≤ u) 
  (hv_bdd : bdd_above (set.range v)) (hv0 : 0 ≤ v) :
  filter.limsup (u * v) at_top ≤ filter.limsup u at_top * filter.limsup v at_top :=
begin
  have h_bdd : bdd_above (set.range (u * v)),
  { exact range_bdd_above_mul hu_bdd hu0 hv_bdd hv0 },
  have hc : ∀ n : ℕ, (⟨u n * v n, (mul_nonneg (hu0 n) (hv0 n))⟩ : ℝ≥0) = ⟨u n, hu0 n⟩*⟨v n, hv0 n⟩,
  { intro n, simp only [nonneg.mk_mul_mk], },
  rw [nnreal.coe_limsup (mul_nonneg hu0 hv0), nnreal.coe_limsup  hu0, nnreal.coe_limsup hv0,
    ← nnreal.coe_mul, nnreal.coe_le_coe, ← ennreal.coe_le_coe, ennreal.coe_mul,
    ennreal.coe_limsup (nnreal.bdd_above' _ h_bdd), 
    ennreal.coe_limsup (nnreal.bdd_above' hu0 hu_bdd),
    ennreal.coe_limsup (nnreal.bdd_above' hv0 hv_bdd)],

  simp only [pi.mul_apply, hc, ennreal.coe_mul],
  obtain ⟨Bu, hBu⟩ := hu_bdd,
  obtain ⟨Bv, hBv⟩ := hv_bdd,
  simp only [mem_upper_bounds, set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] 
    at hBu hBv,
  have hBu_0 : 0 ≤ Bu := le_trans (hu0 0) (hBu 0),
  have hBu' : ∀ (n : ℕ), (⟨u n, hu0 n⟩ : ℝ≥0)  ≤ (⟨Bu, hBu_0⟩ : ℝ≥0),
  { simp only [← nnreal.coe_le_coe, nnreal.coe_mk], exact hBu },
  have hBv_0 : 0 ≤ Bv := le_trans (hv0 0) (hBv 0),
  have hBv' : ∀ (n : ℕ), (⟨v n, hv0 n⟩ : ℝ≥0) ≤ (⟨Bv, hBv_0⟩ : ℝ≥0),
  { simp only [← nnreal.coe_le_coe, nnreal.coe_mk], exact hBv },

  simp_rw ← ennreal.coe_le_coe at hBu' hBv',
  exact ennreal.limsup_mul_le hBu' hBv',
end

end real