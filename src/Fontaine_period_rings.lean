/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import field_theory.is_alg_closed.algebraic_closure
import data.polynomial.laurent
import ring_theory.witt_vector.basic
import ring_theory.perfection
import topology.algebra.nonarchimedean.adic_topology
import Cp_def

/-!
# Fontaine's period rings

Fontaine's period rings are certain rings that can detect interesting properties of Galois 
representations. They also play a key role in comparison theorems between cohomology theories.

We formalize the definitions of the Fontaine period rings `K_alg` and `B_HT` and provide a
strategy for a formalization of the definition of the ring `B_dR`.

## Main Definitions

* `K_alg` : the algebraic closure of a `p`-adic field `K`.
* `B_HT` : the ring of Laurent polynomials `ℂ_[p][X, X⁻¹]`


## Tags

Fontaine period rings, Galois representation theory, p-adic Hodge theory
-/

noncomputable theory

variables (p : ℕ)  [fact p.prime]

open mv_polynomial

/-- The first example of a Fontaine period ring is given by the algebraic closure `K^alg` of a
 `p`-adic field `K`. -/
@[nolint unused_arguments] def K_alg {K : Type*} [field K] [algebra ℚ_[p] K] 
  (h_fin : finite_dimensional ℚ_[p] K) := 
algebraic_closure K 

instance  {K : Type*} [field K] [algebra ℚ_[p] K] (h_fin : finite_dimensional ℚ_[p] K) :
 inhabited (K_alg p h_fin) := algebraic_closure.inhabited _

/-- The ring `B_HT` is defined as the ring of Laurent polynomials `ℂ_[p][X, X⁻¹]`. -/
def B_HT := laurent_polynomial ℂ_[p]

instance : inhabited (B_HT p) := ⟨laurent_polynomial.C 0⟩

/-!  We know present the strategy for the formalization of `B_dR`. An expanded explanation of the
mathematical construction is provided in the accompanying paper. -/
instance : fact ((padic_complex.valued_field p).v ↑p ≠ 1) := 
⟨by simp only [padic_complex.valuation_p, one_div, ne.def, inv_eq_one, nat.cast_eq_one,
      nat.prime.ne_one _inst_1.1, not_false_iff]⟩

/-- First, we define a ring `E p` as the perfection of `𝓞_ℂ|[p]/(p)`. -/
def E :=  pre_tilt ℂ_[p] (padic_complex.valued_field p).v 𝓞_ℂ_[p]
(valuation.integer.integers _) p

instance : comm_ring (E p) := pre_tilt.comm_ring ℂ_[p] (padic_complex.valued_field p).v 𝓞_ℂ_[p]
(valuation.integer.integers _) p

instance : inhabited (E p) := ⟨0⟩

/-- `A_inf p` is the ring of Witt vectors of `E p`. -/
def A_inf := witt_vector p (E p)

instance : comm_ring (A_inf p) := witt_vector.comm_ring _ _

instance : inhabited (A_inf p) := ⟨0⟩

/-- `B_inf_plus p` is the ring `(A_inf p)[1/p]`. -/
def B_inf_plus := localization.away (p : A_inf p)
instance : comm_ring (B_inf_plus p) := localization.comm_ring

instance : inhabited (B_inf_plus p) := ⟨0⟩

/-- The missing part in the definition of `B_dR p` is the construction of a canonical ring
homomorphism from `B_inf_plus p` to `ℂ_[p]`.-/
noncomputable! def theta : ring_hom (B_inf_plus p) ℂ_[p] := sorry

/-- The map `theta` is surjective. -/
lemma theta.surjective : function.surjective (theta p) := sorry

instance : with_ideal (B_inf_plus p) := ⟨(theta p).ker⟩

/--`B_dR_plus p` is the completion of `B_inf_plus p` with respect to the ideal `ker(theta)`. -/
def B_dR_plus := uniform_space.completion (B_inf_plus p)

instance : comm_ring (B_dR_plus p) := uniform_space.completion.comm_ring (B_inf_plus p)

/-- Finally, `B_dR p` is the fraction ring of `B_dR_plus p`. It can be shown that it is in fact a
field. -/
def B_dR := fraction_ring (B_dR_plus p)