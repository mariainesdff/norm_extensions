/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.normed.field.unit_ball
import field_theory.is_alg_closed.algebraic_closure
import ring_theory.valuation.integers
import number_theory.padics.padic_numbers
import topology.metric_space.cau_seq_filter
import topology.algebra.valued_field
import spectral_norm_unique
import normed_valued

noncomputable theory

open_locale nnreal

variables (p : ℕ) [fact (nat.prime p)]

@[reducible] def Q_p_alg : Type* := algebraic_closure ℚ_[p]

lemma Q_p_alg.is_algebraic : algebra.is_algebraic ℚ_[p] (Q_p_alg p) := 
algebraic_closure.is_algebraic _

instance : has_coe ℚ_[p] (Q_p_alg p) := ⟨algebra_map ℚ_[p] (Q_p_alg p)⟩

protected lemma coe_eq : (coe : ℚ_[p] → (Q_p_alg p)) = algebra_map ℚ_[p] (Q_p_alg p) := rfl

lemma padic.is_nonarchimedean : is_nonarchimedean (norm : ℚ_[p] → ℝ) :=
padic_norm_e.nonarchimedean

namespace Q_p_alg

noncomputable! instance normed_field : normed_field (Q_p_alg p) := 
@spectral_norm_to_normed_field ℚ_[p] _ padic.complete_space _ _ _ (Q_p_alg.is_algebraic p) 
  (padic.is_nonarchimedean p)
-- The old proof now times out
--spectral_norm_to_normed_field (Q_p_alg.is_algebraic p) (padic.is_nonarchimedean p)

lemma is_nonarchimedean : is_nonarchimedean (norm : (Q_p_alg p) → ℝ) :=
spectral_norm_is_nonarchimedean (Q_p_alg.is_algebraic p) (padic_norm_e.nonarchimedean)

lemma norm_def (x : Q_p_alg p) : ‖ x ‖ = spectral_norm (Q_p_alg.is_algebraic p) x := rfl


instance valued_field : valued (Q_p_alg p) ℝ≥0 :=
normed_field.to_valued (Q_p_alg.is_nonarchimedean p)

lemma v_def (x : Q_p_alg p) : valued.v x = ‖ x ‖₊ :=
by { ext, refl }

lemma v_def_coe (x : Q_p_alg p) : 
  ((valued.v x : ℝ≥0) : ℝ) = spectral_norm (Q_p_alg.is_algebraic p) x := rfl

end Q_p_alg

--lemma Q_p_alg.v_ext (x : ℚ_[p]) : valued.v (x : Q_p_alg p) = ∥ (x : Q_p_alg p)  ∥₊ := rfl

def C_p := uniform_space.completion (Q_p_alg p) 

notation `ℂ_[`p`]` := C_p p

instance : field ℂ_[p] := uniform_space.completion.field

noncomputable! instance C_p.valued_field : valued (ℂ_[p]) ℝ≥0 := valued.valued_completion 

instance : has_coe_t (Q_p_alg p) ℂ_[p] := uniform_space.completion.has_coe_t _

lemma C_p.valuation_extends (x : Q_p_alg p) : valued.v (x : ℂ_[p]) = valued.v x := 
valued.extension_extends _

instance : algebra (Q_p_alg p) ℂ_[p] := 
uniform_space.completion.algebra' _

example {p : ℕ} [fact p.prime] : ((p : ℚ_[p]) : Q_p_alg p) = (p : Q_p_alg p) :=
by rw [coe_eq, map_nat_cast]

protected lemma C_p.coe_eq : (coe : (Q_p_alg p) → ℂ_[p]) = algebra_map (Q_p_alg p) ℂ_[p] := rfl

protected lemma C_p.coe_zero : ((0 : Q_p_alg p) : ℂ_[p]) = 0 := rfl


example {p : ℕ} [fact p.prime] : ((p : Q_p_alg p) : ℂ_[p]) = (p : ℂ_[p]) :=
by rw [C_p.coe_eq, map_nat_cast]

lemma Q_p_alg.valuation_p (p : ℕ) [fact p.prime] : valued.v (p : Q_p_alg p) = 1/(p : ℝ≥0) :=
begin
  have hp : (p : Q_p_alg p) = ((p : ℚ_[p]) : Q_p_alg p),
  { rw [coe_eq, map_nat_cast] },
  ext,
  rw [Q_p_alg.v_def_coe, hp, coe_eq, spectral_norm.extends,padic_norm_e.norm_p, one_div,
    nonneg.coe_inv, nnreal.coe_nat_cast],
end

lemma C_p.valuation_p (p : ℕ) [fact p.prime] : valued.v (p : ℂ_[p]) = 1/(p : ℝ≥0) :=
begin
  have : ((p : Q_p_alg p) : ℂ_[p]) = (p : ℂ_[p]),
  { rw [C_p.coe_eq, map_nat_cast] },
  rw ← this,
  rw C_p.valuation_extends,
  exact Q_p_alg.valuation_p p,
end

instance : is_rank_one (C_p.valued_field p).v := 
{ hom := monoid_with_zero_hom.id ℝ≥0,
  strict_mono := strict_mono_id,
  nontrivial  := 
  begin
    use p,
    haveI hp : nat.prime p := _inst_1.elim,
    simp only [C_p.valuation_p, one_div, ne.def, inv_eq_zero, nat.cast_eq_zero, 
      inv_eq_one, nat.cast_eq_one],
    exact ⟨hp.ne_zero, hp.ne_one⟩,
  end }

instance : normed_field ℂ_[p] := valued_field.to_normed_field

lemma C_p.norm_def : (norm : ℂ_[p] → ℝ) = norm_def := rfl

lemma C_p.norm_extends (x : Q_p_alg p) : ‖ (x : ℂ_[p]) ‖ = ‖ x ‖ := 
begin
  by_cases hx : x = 0,
  { rw [hx, C_p.coe_zero, norm_zero, norm_zero] },
  { simp only [C_p.norm_def, norm_def, C_p.valuation_extends, monoid_with_zero_hom.coe_mk], 
    refl }
end

lemma C_p.nnnorm_extends (x : Q_p_alg p) : ‖ (x : ℂ_[p]) ‖₊ = ‖ x ‖₊ := 
by { ext, exact C_p.norm_extends p x }

lemma C_p.is_nonarchimedean : is_nonarchimedean (norm : ℂ_[p] → ℝ) :=
begin
  intros x y,
  apply uniform_space.completion.induction_on₂ x y,
  { exact is_closed_le (continuous.comp continuous_norm continuous_add) (continuous.max
      (continuous.comp (@continuous_norm ℂ_[p] _) (continuous.fst continuous_id))
      (continuous.comp (@continuous_norm ℂ_[p] _) (continuous.snd continuous_id))) },
  { intros a b,
    simp only [← uniform_space.completion.coe_add, C_p.norm_extends],
    exact Q_p_alg.is_nonarchimedean p a b }
end

def C_p_integers : subring ℂ_[p] := (C_p.valued_field p).v.integer

notation `𝓞_ℂ_[`p`]` := C_p_integers p