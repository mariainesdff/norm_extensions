/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import data.real.nnreal
import ring_theory.valuation.basic

/-!
# Rank one valuations

We define rank one valuations and discrete valuations

## Main Definitions
* `is_rank_one` : A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
* `is_discrete` : A valuation is discrete if it is nontrivial and its image is contained in
  `with_zero (multiplicative ℤ)`. 

## Tags

valuation, rank one, discrete, with_zero
-/

noncomputable theory

open function multiplicative

open_locale nnreal

variables {R : Type*} [ring R] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

lemma mult_with_top_R_zero : multiplicative.of_add (order_dual.to_dual ⊤) = 
  (0 : multiplicative (with_top ℝ)ᵒᵈ) := rfl 

section is_rank_one

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`. -/
class is_rank_one (v : valuation R Γ₀)  :=
(hom : Γ₀ →*₀ ℝ≥0) 
(strict_mono : strict_mono hom) 
(nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1)

/-- If `v` is a rank one valuation and `x : Γ₀` has image `0` under `is_rank_one.hom v`, then 
  `x = 0`. -/
lemma zero_of_is_rank_one_hom_zero (v : valuation R Γ₀) [is_rank_one v] {x : Γ₀}
 (hx : is_rank_one.hom v x = 0) : x = 0 :=
begin
  have hx0 : 0 ≤ x := zero_le',
  cases le_iff_lt_or_eq.mp hx0 with h_lt h_eq,
  { have hs := is_rank_one.strict_mono h_lt,
    rw [map_zero, hx] at hs,
    exact absurd hs not_lt_zero', },
  { exact h_eq.symm }
end

/-- If `v` is a rank one valuation, then`x : Γ₀` has image `0` under `is_rank_one.hom v` if and
  only if `x = 0`. -/
@[simp] lemma is_rank_one_hom_eq_zero_iff (v : valuation R Γ₀) [hv : is_rank_one v] {x : Γ₀} :
  is_rank_one.hom v x = 0 ↔  x = 0 :=
⟨λ h, zero_of_is_rank_one_hom_zero v h, λ h, by rw [h, map_zero]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one valuation `v : valuation R Γ₀`. -/
def is_rank_one_unit (v : valuation R Γ₀) [hv : is_rank_one v] : Γ₀ˣ :=
units.mk0 (v (classical.some hv.nontrivial)) (classical.some_spec hv.nontrivial).1

/-- A proof that `is_rank_one_unit v ≠ 1`. -/
lemma is_rank_one_unit_ne_one (v : valuation R Γ₀) [hv : is_rank_one v] : 
  is_rank_one_unit v ≠ 1 :=
begin
  rw [ne.def, ← units.eq_iff, units.coe_one],
  exact (classical.some_spec hv.nontrivial).2,
end

/-- A valuation is discrete if it is nontrivial and its image is contained in
  `with_zero (multiplicative ℤ)`. -/
class is_discrete (v : valuation R Γ₀) :=
(hom : Γ₀ →*₀ with_zero (multiplicative ℤ)) 
(strict_mono : strict_mono hom) 
(nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1)

end is_rank_one

-- In this section, we develop some API for `with_zero`, to be PR'd to mathlib. 
namespace with_zero

variables {G H : Type*}

/-- A term of `G` that represents a nonzero term of `with_zero G`. -/
def some {x : with_zero G} (hx : x ≠ 0) : G := classical.some (ne_zero_iff_exists.mp hx)

lemma some_spec {x : with_zero G} (hx : x ≠ 0) : ↑(some hx) = x :=
classical.some_spec (ne_zero_iff_exists.mp hx)

@[simp] lemma some_coe {g : G} : some (@coe_ne_zero G g) = g :=
coe_inj.mp (classical.some_spec (ne_zero_iff_exists.mp (@coe_ne_zero G g)))

/-- If `G` is a monoid and `x y : with_zero G` have a nonzero product, then 
  `some hxy = some (left_ne_zero_of_mul hxy) * some (right_ne_zero_of_mul hxy)`  -/
lemma some_mul [monoid G] {x y : with_zero G} (hxy : x * y ≠ 0) :
  some hxy = some (left_ne_zero_of_mul hxy) * some (right_ne_zero_of_mul hxy) :=
by rw [← coe_inj, coe_mul, some_spec, some_spec, some_spec]

/-- The monoid_with_zero homomorphism `with_zero G →* with_zero H` induced by a monoid homomorphism
  `f : G →* H`. -/
def coe_monoid_hom [monoid G] [monoid H] (f : G →* H) [decidable_eq (with_zero G)] : 
  with_zero G →*₀ with_zero H := 
{ to_fun := λ x, if hx : x = 0 then 0 else f (some hx),
  map_zero' := by simp only [dif_pos],
  map_one' := 
  begin
    have h1 : (1 : with_zero G) ≠ 0 := one_ne_zero,
    have h := (classical.some_spec (ne_zero_iff_exists.mp h1)),
    rw dif_neg h1,
    simp_rw ← coe_one at h ⊢,
    rw [coe_inj, some_coe, f.map_one],
  end,
  map_mul' := λ x y,
  begin
    by_cases hxy : x * y = 0,
    { rw dif_pos hxy,
      cases zero_eq_mul.mp (eq.symm hxy) with hx hy,
      { rw [dif_pos hx, zero_mul] },
      { rw [dif_pos hy, mul_zero] }},
    { rw [dif_neg hxy, dif_neg (left_ne_zero_of_mul hxy), dif_neg (right_ne_zero_of_mul hxy),
        ← coe_mul, coe_inj, ← f.map_mul, some_mul hxy] }
  end }

  end with_zero