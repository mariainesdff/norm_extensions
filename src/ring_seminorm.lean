/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.normed.ring.seminorm
import analysis.seminorm

/-!
# Nonarchimedean ring seminorms and algebra norms

In this file, we define some properties of functions (power-multiplicative, extends, 
nonarchimedean) which will be of special interest to us when applied to ring seminorms or
additive group seminorms.

We prove several properties of nonarchimedean functions.

We also define algebra norms and multiplicative algebra norms.

## Main Definitions
* `is_pow_mul` : `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
  `f (r ^ n) = (f r) ^ n`.
* `function_extends` : given an `α`-algebra `β`, a function `f : β → ℝ` extends a function 
  `g : α → ℝ` if `∀ x : α, f (algebra_map α β x) = g x`. 
* `is_nonarchimedean`: a function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong 
  triangle inequality `f (r + s) ≤ max (f r) (f s)` for all `r s : R`.
* `algebra_norm` : an algebra norm on an `R`-algebra norm `S` is a ring norm on `S` compatible with
  the action of `R`.
* `mul_algebra_norm` : amultiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative
  ring norm on `S` compatible with the action of `R`. 

## Main Results
* `is_nonarchimedean_multiset_image_add` : given a nonarchimedean additive group seminorm `f` on 
  `α`, a function `g : β → α` and a multiset `s : multiset β`, we can always find `b : β`, belonging
  to `s` if `s` is nonempty, such that `f (t.sum g) ≤ f (g b)` .

## Tags

norm, nonarchimedean, pow_mul, power-multiplicative, algebra norm
-/

set_option old_structure_cmd true

open metric

namespace nat 

lemma one_div_cast_pos {n : ℕ} (hn : n ≠ 0) : 0 < 1/(n : ℝ) := 
begin
  rw [one_div, inv_pos, cast_pos],
  exact nat.pos_of_ne_zero hn,  
end

lemma one_div_cast_nonneg (n : ℕ): 0 ≤ 1/(n : ℝ) := 
begin
  by_cases hn : n = 0,
  { rw [hn, cast_zero, div_zero] },
  { refine le_of_lt (one_div_cast_pos hn), }
end

lemma one_div_cast_ne_zero {n : ℕ} (hn : n ≠ 0) : 1/(n : ℝ) ≠ 0 := 
ne_of_gt (one_div_cast_pos hn)

end nat

/-- A function `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
  `f (r ^ n) = (f r) ^ n`. -/
def is_pow_mul {R : Type*} [ring R] (f : R → ℝ) :=
∀ (a : R) {n : ℕ} (hn : 1 ≤ n), f (a^n) = (f a) ^ n

/-- Given an `α`-algebra `β`, a function `f : β → ℝ` extends a function `g : α → ℝ` if 
  `∀ x : α, f (algebra_map α β x) = g x`. -/
def function_extends {α : Type*} [comm_ring α] (g : α → ℝ) {β : Type*} [ring β] [algebra α β]
  (f : β → ℝ) : Prop :=
∀ x : α, f (algebra_map α β x) = g x 

/-- A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong triangle inequality
  `f (r + s) ≤ max (f r) (f s)` for all `r s : R`. -/
def is_nonarchimedean {R : Type*} [add_group R] (f : R → ℝ) : Prop := 
∀ r s, f (r + s) ≤ max (f r) (f s)

/-- A nonarchimedean function satisfies the triangle inequality. -/
lemma add_le_of_is_nonarchimedean {α : Type*} [add_comm_group α] {f : α → ℝ} (hf : ∀ x : α, 0 ≤ f x)
  (hna : is_nonarchimedean f) (a b : α) : f (a + b) ≤ f a + f b :=
begin
  apply le_trans (hna _ _),
  rw [max_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left],
  exact ⟨hf _, hf _⟩,
end

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n • a) ≤ (f a)`. -/
lemma is_nonarchimedean_nsmul {F α : Type*} [add_comm_group α] [add_group_seminorm_class F α] 
  {f : F} (hna : is_nonarchimedean f) (n : ℕ) (a : α) : f (n • a) ≤ (f a) := 
begin
  induction n with n hn,
  { rw [zero_smul, (map_zero _)], exact map_nonneg _ _ },
  { have : n.succ • a = (n + 1) • a := rfl,
    rw [this, add_smul, one_smul],
    exact le_trans (hna _ _) (max_le_iff.mpr ⟨hn, le_refl _⟩) }
end

/-- If `f` is a nonarchimedean additive group seminorm on `α`, then for every `n : ℕ` and `a : α`,
  we have `f (n * a) ≤ (f a)`. -/
lemma is_nonarchimedean_nmul {F α : Type*} [ring α] [add_group_seminorm_class F α] {f : F}
  (hna : is_nonarchimedean f) (n : ℕ) (a : α) : f (n * a) ≤ (f a) := 
begin
  rw ← nsmul_eq_mul,
  exact is_nonarchimedean_nsmul hna _ _,
end

/-- If `f` is a nonarchimedean additive group seminorm on `α` and `x y : α` are such that
  `f y ≠ f x`, then `f (x + y) = max (f x) (f y)`. -/
lemma is_nonarchimedean_add_eq_max_of_ne {F α : Type*} [ring α] [add_group_seminorm_class F α]
  {f : F} (hna : is_nonarchimedean f) {x y : α} (hne : f y ≠ f x) :
  f (x + y) = max (f x) (f y) :=
begin
  wlog hle := le_total (f y) (f x) using [x y],
  have hlt : f y < f x, from lt_of_le_of_ne hle hne,
  have : f x ≤ max (f (x + y)) (f y), from calc
    f x = f (x + y + (-y)) : by rw [add_neg_cancel_right]
               ... ≤ max (f (x + y)) (f (-y)) : hna _ _
               ... = max (f (x + y)) (f y) : by rw map_neg_eq_map f y,
  have hnge : f y ≤ f (x + y),
  { apply le_of_not_gt,
    intro hgt,
    rw max_eq_right_of_lt hgt at this,
    apply not_lt_of_ge this,
    assumption },
  have : f x ≤ f (x + y), by rwa [max_eq_left hnge] at this,
  apply le_antisymm,
  { exact hna _ _ },
  { rw max_eq_left_of_lt hlt,
    assumption },
  rw [add_comm, max_comm], exact this (ne.symm hne),
end

open_locale classical

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a finset
  `t : finset β`, we can always find `b : β`, belonging to `t` if `t` is nonempty, such that
  `f (t.sum g) ≤ f (g b)` . -/
lemma is_nonarchimedean_finset_image_add {F α : Type*} [ring α] [add_group_seminorm_class F α]
  {f : F} (hna : is_nonarchimedean f) {β : Type*} [hβ : nonempty β] (g : β → α) (t : finset β) :
  ∃ (b : β) (hb : t.nonempty → b ∈ t), f (t.sum g) ≤ f (g b) := 
begin
  apply finset.induction_on t,
  { rw [finset.sum_empty],
    refine ⟨hβ.some, by simp only [finset.not_nonempty_empty, is_empty.forall_iff], _⟩,
    rw map_zero f, exact map_nonneg f _ },
  { rintros a s has ⟨M, hMs, hM⟩,
    rw [finset.sum_insert has],
    by_cases hMa : f (g M) ≤ f (g a),
    { refine ⟨a, _, le_trans (hna _ _) (max_le_iff.mpr (⟨le_refl _,le_trans hM hMa⟩))⟩,
      simp only [finset.nonempty_coe_sort, finset.insert_nonempty, finset.mem_insert,
        eq_self_iff_true, true_or, forall_true_left] },
    { rw not_le at hMa,
      by_cases hs : s.nonempty,
      { refine ⟨M, _, le_trans (hna _ _)
          (max_le_iff.mpr ⟨le_of_lt hMa, hM⟩)⟩,
        simp only [finset.nonempty_coe_sort, finset.insert_nonempty, finset.mem_insert,
          forall_true_left],
        exact or.intro_right _ (hMs hs)  },
      { use a,
        split,
        { simp only [finset.insert_nonempty, finset.mem_insert, eq_self_iff_true, true_or,
            forall_true_left] },
          have h0 : f (s.sum g) = 0,
          { rw [finset.not_nonempty_iff_eq_empty.mp hs, finset.sum_empty, map_zero] },
          apply le_trans (hna _ _),
          rw h0,
          exact max_le_iff.mpr ⟨le_refl _, map_nonneg _ _⟩ }}} 
end

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a function `g : β → α` and a 
  multiset `s : multiset β`, we can always find `b : β`, belonging to `s` if `s` is nonempty, 
  such that `f (t.sum g) ≤ f (g b)` . -/
lemma is_nonarchimedean_multiset_image_add {F α : Type*} [ring α] [add_group_seminorm_class F α]
  {f : F} (hna : is_nonarchimedean f) {β : Type*} [hβ : nonempty β] (g : β → α) (s : multiset β) :
  ∃ (b : β) (hb : 0 < s.card → b ∈ s), f ((multiset.map g s).sum) ≤ f (g b) := 
begin
  apply multiset.induction_on s,
  { rw [multiset.map_zero, multiset.sum_zero, multiset.card_zero, map_zero f],
    refine ⟨hβ.some, by simp only [not_lt_zero', is_empty.forall_iff], map_nonneg _ _⟩ },
  { rintros a t ⟨M, hMs, hM⟩,
    by_cases hMa : f (g M) ≤ f (g a),
    { refine ⟨a, _, _⟩,
      { simp only [multiset.card_cons, nat.succ_pos', multiset.mem_cons_self, forall_true_left] },
      { rw [multiset.map_cons, multiset.sum_cons],
        exact le_trans (hna _ _) (max_le_iff.mpr (⟨le_refl _,le_trans hM hMa⟩)), }},
    { rw not_le at hMa,
      by_cases ht : 0 < t.card,
      { refine ⟨M, _, _⟩,
        { simp only [multiset.card_cons, nat.succ_pos', multiset.mem_cons, forall_true_left],
          exact or.intro_right _ (hMs ht) },
          rw [multiset.map_cons, multiset.sum_cons],
          exact le_trans (hna _ _) (max_le_iff.mpr ⟨le_of_lt hMa, hM⟩) },
      { refine ⟨a, _, _⟩,
        { simp only [multiset.card_cons, nat.succ_pos', multiset.mem_cons_self, forall_true_left] },
        { have h0 : f (multiset.map g t).sum = 0,
          { simp only [not_lt, le_zero_iff, multiset.card_eq_zero] at ht,
            rw [ht, multiset.map_zero, multiset.sum_zero, map_zero f] },
          rw [multiset.map_cons, multiset.sum_cons],
          apply le_trans (hna _ _),
          rw h0,
          exact max_le_iff.mpr ⟨le_refl _, map_nonneg _ _⟩ }}}}
end

/-- Given a nonarchimedean additive group seminorm `f` on `α`, a number `n : ℕ` and a function 
  `g : ℕ → α`, there exists `m : ℕ` such that `f ((finset.range n).sum g) ≤ f (g m)`.
  If `0 < n`, this `m` satisfies `m < n`. -/
lemma is_nonarchimedean_finset_range_add_le {F α : Type*} [ring α] [add_group_seminorm_class F α]
  {f : F} (hna : is_nonarchimedean f) (n : ℕ) (g : ℕ → α) : ∃ (m : ℕ) (hm : 0 < n → m < n),
  f ((finset.range n).sum g) ≤ f (g m) :=
begin
  obtain ⟨m, hm, h⟩ := is_nonarchimedean_finset_image_add hna g (finset.range n),
  rw [finset.nonempty_range_iff, ← zero_lt_iff, finset.mem_range] at hm,
  exact ⟨m, hm, h⟩,
end

/-- If `f` is a nonarchimedean additive group seminorm on a commutative ring `α`, `n : ℕ`, and 
  `a b : α`, then we can find `m : ℕ` such that `m ≤ n` and 
  `f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m)))`. -/
lemma is_nonarchimedean_add_pow {F α : Type*} [comm_ring α] [ring_seminorm_class F α] {f : F}
  (hna : is_nonarchimedean f) (n : ℕ) (a b : α) :
  ∃ (m : ℕ) (hm : m ∈ list.range(n + 1)), f ((a + b) ^ n) ≤ (f (a ^ m)) * (f (b ^ (n - m))) :=
begin
  obtain ⟨m, hm_lt, hM⟩ := is_nonarchimedean_finset_image_add hna 
    (λ (m : ℕ), a ^ m * b ^ (n - m) * ↑(n.choose m)) (finset.range (n + 1)),
  simp only [finset.nonempty_range_iff, ne.def, nat.succ_ne_zero, not_false_iff, finset.mem_range,
    if_true, forall_true_left] at hm_lt,
  refine ⟨m, list.mem_range.mpr hm_lt, _⟩,
  simp only [← add_pow] at hM,
  rw mul_comm at hM,
  exact le_trans hM (le_trans (is_nonarchimedean_nmul hna _ _) (map_mul_le_mul _ _ _)),
end

/-- If `f` is a ring seminorm on `a`, then `∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n`. -/
lemma map_pow_le_pow {F α : Type*} [ring α] [ring_seminorm_class F α] (f : F) (a : α) :
  ∀ {n : ℕ}, n ≠ 0 → f (a ^ n) ≤ f a ^ n
| 0 h       := absurd rfl h
| 1 h       := by simp only [pow_one]
| (n + 2) h := by simp only [pow_succ _ (n + 1)]; exact le_trans (map_mul_le_mul f a _)
                (mul_le_mul_of_nonneg_left (map_pow_le_pow n.succ_ne_zero) (map_nonneg f a))

/-- If `f` is a ring seminorm on `a` with `f 1 ≤ `, then `∀ (n : ℕ), f (a ^ n) ≤ f a ^ n`. -/
lemma map_pow_le_pow' {F α : Type*} [ring α] [ring_seminorm_class F α] {f : F} (hf1 : f 1 ≤ 1) 
  (a : α) : ∀ (n : ℕ), f (a ^ n) ≤ f a ^ n
| 0       := by simp only [pow_zero, hf1] 
| (n + 1) := by simp only [pow_succ _ n]; exact le_trans (map_mul_le_mul f a _)
              (mul_le_mul_of_nonneg_left (map_pow_le_pow' n) (map_nonneg f a))

/-- An algebra norm on an `R`-algebra norm `S` is a ring norm on `S` compatible with the
  action of `R`. -/
structure algebra_norm (R : Type*) [semi_normed_comm_ring R] (S : Type*) [ring S] 
  [algebra R S] extends seminorm R S, ring_norm S

attribute [nolint doc_blame] algebra_norm.to_seminorm algebra_norm.to_ring_norm

instance (K : Type*) [normed_field K] : inhabited (algebra_norm K K) := 
⟨{ to_fun   := norm,
  map_zero' := norm_zero,
  add_le'   := norm_add_le,
  neg'      := norm_neg,
  smul'     := norm_mul,
  mul_le'   := norm_mul_le,
  eq_zero_of_map_eq_zero' := λ x, norm_eq_zero.mp}⟩

/-- `algebra_norm_class F α` states that `F` is a type of algebra norms on the ring `β`.
You should extend this class when you extend `algebra_norm`. -/
class algebra_norm_class (F : Type*) (R : out_param $ Type*) [semi_normed_comm_ring R]
  (S : out_param $ Type*) [ring S] [algebra R S]
  extends seminorm_class F R S, ring_norm_class F S

-- `R` is an `out_param`, so this is a false positive.
attribute [nolint dangerous_instance] algebra_norm_class.to_ring_norm_class

namespace algebra_norm

variables {R : Type*} [semi_normed_comm_ring R]  {S : Type*} [ring S] [algebra R S]
  {f : algebra_norm R S}

/-- The ring_seminorm underlying an algebra norm. -/
def to_ring_seminorm (f : algebra_norm R S) : ring_seminorm S :=
f.to_ring_norm.to_ring_seminorm

instance algebra_norm_class : algebra_norm_class (algebra_norm R S) R S :=
{ coe := λ f, f.to_fun,
  coe_injective' :=  λ f f' h, 
  begin
    simp only [ring_norm.to_fun_eq_coe, fun_like.coe_fn_eq] at h,
    cases f; cases f'; congr',
  end,
  map_zero := λ f, f.map_zero',
  map_add_le_add := λ f, f.add_le',
  map_mul_le_mul := λ f, f.mul_le',
  map_neg_eq_map := λ f, f.neg',
  eq_zero_of_map_eq_zero := λ f, f.eq_zero_of_map_eq_zero',
  map_smul_eq_mul := λ f, f.smul' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (algebra_norm R S) (λ _, S → ℝ) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe (p : algebra_norm R S) : p.to_fun = p := rfl

@[ext] lemma ext {p q : algebra_norm R S} : (∀ x, p x = q x) → p = q := fun_like.ext p q

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
lemma extends_norm' {f : algebra_norm R S} (hf1 : f 1 = 1) (a : R) : f (a • 1) = ‖ a ‖   :=
by rw [← mul_one ‖ a ‖ , ← hf1]; exact f.smul' _ _

/-- An `R`-algebra norm such that `f 1 = 1` extends the norm on `R`. -/
lemma extends_norm {f : algebra_norm R S} (hf1 : f 1 = 1) (a : R) : 
  f (algebra_map R S a) = ‖ a ‖  :=
by rw algebra.algebra_map_eq_smul_one; exact extends_norm' hf1 _

end algebra_norm

/-- A multiplicative algebra norm on an `R`-algebra norm `S` is a multiplicative ring norm on `S`
  compatible with the action of `R`. -/
structure mul_algebra_norm (R : Type*) [semi_normed_comm_ring R] (S : Type*) [ring S] 
  [algebra R S] extends seminorm R S, mul_ring_norm S

attribute [nolint doc_blame] mul_algebra_norm.to_seminorm mul_algebra_norm.to_mul_ring_norm

instance (K : Type*) [normed_field K] : inhabited (mul_algebra_norm K K) := 
⟨{ to_fun   := norm,
  map_zero' := norm_zero,
  add_le'   := norm_add_le,
  neg'      := norm_neg,
  smul'     := norm_mul,
  map_one'  := norm_one,
  map_mul'  := norm_mul,
  eq_zero_of_map_eq_zero' := λ x, norm_eq_zero.mp}⟩

/-- `algebra_norm_class F α` states that `F` is a type of algebra norms on the ring `β`.
You should extend this class when you extend `algebra_norm`. -/
class mul_algebra_norm_class (F : Type*) (R : out_param $ Type*) [semi_normed_comm_ring R]
  (S : out_param $ Type*) [ring S] [algebra R S]
  extends seminorm_class F R S, mul_ring_norm_class F S

-- `R` is an `out_param`, so this is a false positive.
attribute [nolint dangerous_instance] mul_algebra_norm_class.to_mul_ring_norm_class

namespace mul_algebra_norm

variables {R S : out_param $ Type*} [semi_normed_comm_ring R] [ring S] [algebra R S]
  {f : algebra_norm R S}

instance mul_algebra_norm_class : mul_algebra_norm_class (mul_algebra_norm R S) R S :=
{ coe := λ f, f.to_fun,
  coe_injective' :=  λ f f' h, 
  begin
    simp only [ring_norm.to_fun_eq_coe, fun_like.coe_fn_eq] at h,
    cases f; cases f'; congr',
  end,
  map_zero := λ f, f.map_zero',
  map_add_le_add := λ f, f.add_le',
  map_one := λ f, f.map_one',
  map_mul := λ f, f.map_mul',
  map_neg_eq_map := λ f, f.neg',
  eq_zero_of_map_eq_zero := λ f, f.eq_zero_of_map_eq_zero',
  map_smul_eq_mul := λ f, f.smul' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (mul_algebra_norm R S) (λ _, S → ℝ) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe (p : mul_algebra_norm R S) : p.to_fun = p := rfl

@[ext] lemma ext {p q : mul_algebra_norm R S} : (∀ x, p x = q x) → p = q := fun_like.ext p q

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
lemma extends_norm' (f : mul_algebra_norm R S) (a : R) : f (a • 1) = ‖ a ‖  :=
by rw [← mul_one ‖ a ‖, ← f.map_one', ← f.smul']; refl

/-- A multiplicative `R`-algebra norm extends the norm on `R`. -/
lemma extends_norm (f : mul_algebra_norm R S) (a : R) : 
  f (algebra_map R S a) = ‖ a ‖ :=
by rw algebra.algebra_map_eq_smul_one; exact extends_norm' _ _

end mul_algebra_norm

namespace mul_ring_norm

variables {R : Type*} [non_assoc_ring R] 

/-- The ring norm underlying a multiplicative ring norm. -/
def to_ring_norm (f : mul_ring_norm R) : ring_norm R :=
{ to_fun    := f,
  map_zero' := f.map_zero',
  add_le'   := f.add_le',
  neg'      := f.neg',
  mul_le'   := λ x y, le_of_eq (f.map_mul' x y),
  eq_zero_of_map_eq_zero' := f.eq_zero_of_map_eq_zero' }

/-- A multiplicative ring norm is power-multiplicative. -/
lemma is_pow_mul {A : Type*} [ring A] (f : mul_ring_norm A) : is_pow_mul f := λ x n hn,
begin
  induction n with n ih,
  { exfalso, linarith },
  { by_cases hn1 : 1 ≤ n,
    { rw [pow_succ, pow_succ, map_mul, ih hn1] },
    { rw [not_le, nat.lt_one_iff] at hn1,
      rw [hn1, pow_one, pow_one], }}
end

end mul_ring_norm

/-- The seminorm on a `semi_normed_ring`, as a `ring_seminorm`. -/
def seminormed_ring.to_ring_seminorm (R : Type*) [semi_normed_ring R] :
  ring_seminorm R :=
{ to_fun    := norm,
  map_zero' := norm_zero,
  add_le'   := norm_add_le,
  mul_le'   := norm_mul_le,
  neg'      := norm_neg, }

/-- The norm on a `normed_ring`, as a `ring_norm`. -/
@[simps] def normed_ring.to_ring_norm (R : Type*) [normed_ring R] :
  ring_norm R :=
{ to_fun    := norm,
  map_zero' := norm_zero,
  add_le'   := norm_add_le,
  mul_le'   := norm_mul_le,
  neg'      := norm_neg,
  eq_zero_of_map_eq_zero' := λ x hx, by { rw ← norm_eq_zero, exact hx }}

@[simp] lemma normed_ring.to_ring_norm_apply (R : Type*) [normed_ring R] (x : R):
  (normed_ring.to_ring_norm R) x = ‖ x ‖ := rfl

/-- The norm on a `normed_field`, as a `mul_ring_norm`. -/
def normed_field.to_mul_ring_norm (R : Type*) [normed_field R] :
  mul_ring_norm R :=
{ to_fun    := norm,
  map_zero' := norm_zero,
  map_one'  := norm_one,
  add_le'   := norm_add_le,
  map_mul'  := norm_mul,
  neg'      := norm_neg,
  eq_zero_of_map_eq_zero' := λ x hx, by { rw ← norm_eq_zero, exact hx }}
