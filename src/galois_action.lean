/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Cp_def

/-!
# The Galois action on the `p`-adic complex numbers.

In this file, we show that the action of the absolute Galois group of `ℚ_[p]` on `Q_p_alg p` 
extends to an action on `ℂ_[p]`.

## Tags

p-adic, p adic, padic, galois action, galois
-/

noncomputable theory

variables {p : ℕ} [fact (nat.prime p)]

/-- The elements of the Galois group Gal((Q_p_alg p)/ℚ_[p]) are isometries. -/
lemma galois_map_isometry (σ : (Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) : isometry σ :=
begin
  rw isometry_iff_dist_eq,
  intros x y,
  simp only [dist_eq_norm, ← map_sub, Q_p_alg.norm_def,
    spectral_norm_aut_isom (Q_p_alg.is_algebraic p) σ (x - y)],
end

/-- Any `σ` in `Q_p_alg p ≃ₐ[ℚ_[p]] Q_p_alg p` acts uniformly continuously on `Q_p_alg p`. -/
instance : has_uniform_continuous_const_smul (Q_p_alg p ≃ₐ[ℚ_[p]] Q_p_alg p) (Q_p_alg p) := 
⟨λ σ, (galois_map_isometry σ).uniform_continuous⟩

/-- The action of the absolute galois of `ℚ_[p]` on `Q_p_alg p` extends to an action on `ℂ_[p]`.-/
instance : mul_action ((Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) (ℂ_[p]) := 
uniform_space.completion.mul_action ((Q_p_alg p) ≃ₐ[ℚ_[p]] (Q_p_alg p)) (Q_p_alg p)