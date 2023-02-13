/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import data.polynomial.laurent
import ring_theory.witt_vector.basic
import ring_theory.perfection
import topology.algebra.nonarchimedean.adic_topology
import Cp_def

/-!
# Fontaine period rings

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

variables (p : ℕ)  [fact p.prime]

/- Fontaine's period rings -/

open mv_polynomial

/-- The first example of Fontaine period ring is given by the algebraic closure `K^alg` of a
 `p`-adic field `K`. -/
@[nolint unused_arguments] def K_alg {K : Type*} [field K] [algebra ℚ_[p] K]  (h_fin : finite_dimensional ℚ_[p] K) := 
algebraic_closure K 

/-- The ring `B_HT` is defined as the Laurent polynomial ring `ℂ_[p][X, X⁻¹]`. -/
def B_HT := laurent_polynomial ℂ_[p]

-- We know present the strategy for the formalization of B_dR
instance : fact ((padic_complex.valued_field p).v ↑p ≠ 1) := 
⟨by simp only [padic_complex.valuation_p, one_div, ne.def, inv_eq_one, nat.cast_eq_one,
      nat.prime.ne_one _inst_1.1, not_false_iff]⟩

def E :=  pre_tilt ℂ_[p] (padic_complex.valued_field p).v 𝓞_ℂ_[p]
(valuation.integer.integers _) p

instance : comm_ring (E p) := pre_tilt.comm_ring ℂ_[p] (padic_complex.valued_field p).v 𝓞_ℂ_[p]
(valuation.integer.integers _) p

/-- `A_inf` is the ring of Witt vectors of `E p`. -/
def A_inf := witt_vector p (E p)

instance : comm_ring (A_inf p) := witt_vector.comm_ring _ _

def B_inf_plus := localization.away (p : A_inf p)
instance : comm_ring (B_inf_plus p) := localization.comm_ring

noncomputable! def theta : ring_hom (B_inf_plus p) ℂ_[p] := sorry

lemma theta.surjective : function.surjective (theta p) := sorry

instance : with_ideal (B_inf_plus p) := ⟨(theta p).ker⟩

def B_dR_plus := uniform_space.completion (B_inf_plus p)

instance : comm_ring (B_dR_plus p) := uniform_space.completion.comm_ring (B_inf_plus p)

def B_dR := fraction_ring (B_dR_plus p)

#lint