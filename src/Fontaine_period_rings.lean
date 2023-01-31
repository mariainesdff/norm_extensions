/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import data.polynomial.laurent
import field_theory.is_alg_closed.algebraic_closure
import linear_algebra.adic_completion
import ring_theory.witt_vector.basic
import ring_theory.perfection
import topology.algebra.nonarchimedean.adic_topology
import Cp_def

noncomputable theory

variables (p : ℕ)  [fact p.prime]

/- Fontaine's period rings -/

open mv_polynomial

-- The first example is `K^alg`, for `K` a `p`-adic field.#check

@[nolint unused_arguments]
def K_alg {K : Type*} [field K] [algebra ℚ_[p] K]  (h_fin : finite_dimensional ℚ_[p] K) := 
algebraic_closure K 

-- B_HT
def B_HT := laurent_polynomial ℂ_[p]

-- We know present the structure for the formalization of B_dR
instance : fact ((C_p.valued_field p).v ↑p ≠ 1) := 
⟨by simp only [C_p.valuation_p, one_div, ne.def, inv_eq_one, nat.cast_eq_one,
      nat.prime.ne_one _inst_1.1, not_false_iff]⟩

def E :=  pre_tilt ℂ_[p] (C_p.valued_field p).v 𝓞_ℂ_[p]
(valuation.integer.integers _) p

instance : comm_ring (E p) := pre_tilt.comm_ring ℂ_[p] (C_p.valued_field p).v 𝓞_ℂ_[p]
(valuation.integer.integers _) p

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