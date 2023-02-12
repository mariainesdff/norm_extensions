/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.valuation.integers
import topology.metric_space.cau_seq_filter
import topology.algebra.valued_field
import spectral_norm_unique
import normed_valued

/-!
# The `p`-adic complex numbers.

In this file we define the field `ℂ_[p]` of `p`-adic complex numbers and we give it both a normed 
field and a valued field structure, induced by the unique extension of the `p`-adic norm to `ℂ_[p]`.

## Main Definitions

* `padic_complex` : the type of `p`-adic complex numbers.
* `padic_complex_integers` : the ring of integers of `ℂ_[p]`.


## Main Results

* `padic_complex.norm_extends` : the norm on `ℂ_[p]` extends the norm on `Q_p_alg p`, and hence
  the norm on `ℚ_[p]`.
* `padic_complex.is_nonarchimedean` : The norm on `ℂ_[p]` is nonarchimedean.


## Notation

We introduce the notation `ℂ_[p]` for the `p`-adic complex numbers, and `𝓞_ℂ_[p]` for its ring of
integers.

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/


noncomputable theory

open rank_one_valuation

open_locale nnreal

variables (p : ℕ) [fact (nat.prime p)]

/-- `Q_p_alg p` is the algebraic closure of `ℚ_[p]`. -/
@[reducible] def Q_p_alg : Type* := algebraic_closure ℚ_[p]

/-- `Q_p_alg p` is an algebraic extension of `ℚ_[p]`. -/
lemma Q_p_alg.is_algebraic : algebra.is_algebraic ℚ_[p] (Q_p_alg p) := 
algebraic_closure.is_algebraic _

instance : has_coe ℚ_[p] (Q_p_alg p) := ⟨algebra_map ℚ_[p] (Q_p_alg p)⟩

protected lemma coe_eq : (coe : ℚ_[p] → (Q_p_alg p)) = algebra_map ℚ_[p] (Q_p_alg p) := rfl

namespace Q_p_alg

/-- `Q_p_alg p` is a normed field, where the norm is the `p`-adic norm, that is, the spectral norm
induced by the `p`-adic norm on `ℚ_[p]`. -/
instance normed_field : normed_field (Q_p_alg p) := 
spectral_norm_to_normed_field (Q_p_alg.is_algebraic p) padic_norm_e.nonarchimedean

/-- The norm on `Q_p_alg p` is nonarchimedean. -/
lemma is_nonarchimedean : is_nonarchimedean (norm : (Q_p_alg p) → ℝ) :=
spectral_norm_is_nonarchimedean (Q_p_alg.is_algebraic p) (padic_norm_e.nonarchimedean)

/-- The norm on `Q_p_alg p` is the spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
lemma norm_def (x : Q_p_alg p) : ‖ x ‖ = spectral_norm (Q_p_alg.is_algebraic p) x := rfl

/-- The norm on `Q_p_alg p` extends the `p`-adic norm on `ℚ_[p]`. -/
lemma Q_p.norm_extends (x : ℚ_[p]) : ‖ (x : Q_p_alg p) ‖ = ‖ x ‖ := 
spectral_alg_norm_extends _ _ (padic_norm_e.nonarchimedean)

/-- `Q_p_alg p` is a valued field, with the valuation corresponding to the `p`-adic norm. -/
instance valued_field : valued (Q_p_alg p) ℝ≥0 :=
normed_field.to_valued (Q_p_alg.is_nonarchimedean p)

/-- The valuation of `x : Q_p_alg p` agrees with its `ℝ≥0`-valued norm. -/
lemma v_def (x : Q_p_alg p) : valued.v x = ‖ x ‖₊ := rfl

/-- The coercion of the valuation of `x : Q_p_alg p` to `ℝ` agrees with its norm. -/
lemma v_def_coe (x : Q_p_alg p) : 
  ((valued.v x : ℝ≥0) : ℝ) = spectral_norm (Q_p_alg.is_algebraic p) x := rfl

/-- The valuation of `p : Q_p_alg p` is `1/p`. -/
lemma valuation_p (p : ℕ) [fact p.prime] : valued.v (p : Q_p_alg p) = 1/(p : ℝ≥0) :=
begin
  rw [← map_nat_cast (algebra_map  ℚ_[p] (Q_p_alg p)), ← coe_eq],
  ext,
  rw [v_def_coe, coe_eq, spectral_norm.extends,padic_norm_e.norm_p, one_div, nonneg.coe_inv,
    nnreal.coe_nat_cast],
end

end Q_p_alg

/-- `ℂ_[p]` is the field of `p`-adic complex numbers, that is, the completion of `Q_p_alg p` with
respect to the `p`-adic norm. -/
def padic_complex := uniform_space.completion (Q_p_alg p) 

notation `ℂ_[`p`]` := padic_complex p

namespace padic_complex

/-- The `p`-adic complex numbers have a field structure. -/
instance : field ℂ_[p] := uniform_space.completion.field

/-- The `p`-adic complex numbers are inhabited. -/
instance : inhabited ℂ_[p] := ⟨0⟩

/-- `ℂ_[p]` is a valued field, where the valuation is the one extending that on `Q_p_alg p`. -/
instance valued_field : valued (ℂ_[p]) ℝ≥0 := valued.valued_completion 

/-- `ℂ_[p]` is a complete space. -/
instance complete_space : complete_space (ℂ_[p]) := uniform_space.completion.complete_space _

instance : has_coe_t (Q_p_alg p) ℂ_[p] := uniform_space.completion.has_coe_t _

/-- The valuation on `ℂ_[p]` extends the valuation on `Q_p_alg p`. -/
lemma valuation_extends (x : Q_p_alg p) : valued.v (x : ℂ_[p]) = valued.v x := 
valued.extension_extends _

/-- `ℂ_[p]` is an algebra over `Q_p_alg p`. -/
instance : algebra (Q_p_alg p) ℂ_[p] := uniform_space.completion.algebra' _

lemma coe_eq : (coe : (Q_p_alg p) → ℂ_[p]) = algebra_map (Q_p_alg p) ℂ_[p] := rfl

lemma coe_zero : ((0 : Q_p_alg p) : ℂ_[p]) = 0 := rfl

/-- The valuation of `p : ℂ_[p]` is `1/p`. -/
lemma valuation_p (p : ℕ) [fact p.prime] : valued.v (p : ℂ_[p]) = 1/(p : ℝ≥0) :=
by rw [← map_nat_cast (algebra_map _ _), ← coe_eq, valuation_extends, Q_p_alg.valuation_p]

/-- The valuation on `ℂ_[p]` has rank one. -/
instance : is_rank_one (padic_complex.valued_field p).v := 
{ hom := monoid_with_zero_hom.id ℝ≥0,
  strict_mono := strict_mono_id,
  nontrivial  := 
  begin
    use p,
    haveI hp : nat.prime p := _inst_1.elim,
    simp only [valuation_p, one_div, ne.def, inv_eq_zero, nat.cast_eq_zero, 
      inv_eq_one, nat.cast_eq_one],
    exact ⟨hp.ne_zero, hp.ne_one⟩,
  end }

/-- `ℂ_[p]` is a normed field, where the norm corresponds to the extension of the `p`-adic 
  valuation.-/
instance : normed_field ℂ_[p] := valued_field.to_normed_field

/-- The norm on `ℂ_[p]` agrees with the valuation. -/
lemma norm_def : (norm : ℂ_[p] → ℝ) = rank_one_valuation.norm_def := rfl

/-- The norm on `ℂ_[p]` extends the norm on `Q_p_alg p`. -/
lemma norm_extends (x : Q_p_alg p) : ‖ (x : ℂ_[p]) ‖ = ‖ x ‖ := 
begin
  by_cases hx : x = 0,
  { rw [hx, coe_zero, norm_zero, norm_zero] },
  { simp only [norm_def, rank_one_valuation.norm_def, valuation_extends, 
      monoid_with_zero_hom.coe_mk], 
    refl }
end

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends that on `Q_p_alg p`. -/
lemma nnnorm_extends (x : Q_p_alg p) : ‖ (x : ℂ_[p]) ‖₊ = ‖ x ‖₊ := 
by { ext, exact norm_extends p x }

/-- The norm on `ℂ_[p]` is nonarchimedean. -/
lemma is_nonarchimedean : is_nonarchimedean (norm : ℂ_[p] → ℝ) :=
begin
  intros x y,
  apply uniform_space.completion.induction_on₂ x y,
  { exact is_closed_le (continuous.comp continuous_norm continuous_add) (continuous.max
      (continuous.comp (@continuous_norm ℂ_[p] _) (continuous.fst continuous_id))
      (continuous.comp (@continuous_norm ℂ_[p] _) (continuous.snd continuous_id))) },
  { intros a b,
    simp only [← uniform_space.completion.coe_add, norm_extends],
    exact Q_p_alg.is_nonarchimedean p a b }
end

end padic_complex

/-- We define `𝓞_ℂ_[p]` as the subring elements of `ℂ_[p]` with valuation `≤ 1`. -/
def padic_complex_integers : subring ℂ_[p] := (padic_complex.valued_field p).v.integer

notation `𝓞_ℂ_[`p`]` := padic_complex_integers p

/-- `𝓞_ℂ_[p]` is the ring of integers of `ℂ_[p]`. -/
lemma padic_complex.integers : valuation.integers (padic_complex.valued_field p).v  𝓞_ℂ_[p] := 
valuation.integer.integers _