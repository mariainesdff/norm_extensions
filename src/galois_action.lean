/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Cp_def

noncomputable theory

variables {p : ℕ} [fact (nat.prime p)]

-- Found by infer_instance
instance : has_smul ((Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) (Q_p_alg p) := 
smul_zero_class.to_has_smul

-- Found by infer_instance
instance : mul_action ((Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) (Q_p_alg p) := 
mul_distrib_mul_action.to_mul_action

lemma galois_map_isometry (σ : (Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) : isometry σ :=
begin
  rw isometry_iff_dist_eq,
  intros x y,
  simp only [dist_eq_norm, ← map_sub, Q_p_alg.norm_def,
    spectral_norm.aut_isom (Q_p_alg.is_algebraic p) σ (x - y)],
end

instance : has_uniform_continuous_const_smul (Q_p_alg p ≃ₐ[ℚ_[p]] Q_p_alg p) (Q_p_alg p) := 
⟨λ σ, (galois_map_isometry σ).uniform_continuous⟩

instance : mul_action ((Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) (ℂ_[p]) := 
uniform_space.completion.mul_action ((Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) (Q_p_alg p)