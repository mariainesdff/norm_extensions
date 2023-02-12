/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import data.real.basic
import order.filter.at_top_bot
import order.liminf_limsup
import topology.metric_space.basic
import topology.algebra.order.monotone_convergence
import topology.instances.nnreal

/-!
# Limits of monotone and antitone sequences

We prove some auxiliary results about limits of `ℝ`-valued and `ℝ≥0`-valued sequences.

## Main Results

* `real.tendsto_of_is_bounded_antitone` : an antitone, bounded below sequence `f : ℕ → ℝ` has a 
  finite limit.
* `nnreal.tendsto_of_is_bounded_antitone` : an antitone sequence `f : ℕ → ℝ≥0` has a finite limit.

## Tags

glb, monotone, antitone, tendsto
-/

open_locale filter topological_space

/-- A nonempty, bounded below set of real numbers has a greatest lower bound. -/
theorem real.exists_is_glb {S : set ℝ} (hne : S.nonempty) (hbdd : bdd_below S) :
  ∃ x, is_glb S x :=
begin
  set T := - S with hT,
  have hT_ne : T.nonempty := set.nonempty_neg.mpr hne,
  have hT_bdd : bdd_above T := bdd_above_neg.mpr hbdd,
  use -classical.some (real.exists_is_lub T hT_ne hT_bdd),
  simpa [← is_lub_neg] using (classical.some_spec (real.exists_is_lub T hT_ne hT_bdd)),
end

/-- An monotone, bounded above sequence `f : ℕ → ℝ` has a finite limit. -/
lemma filter.tendsto_of_is_bounded_monotone {f : ℕ → ℝ} (h_bdd : bdd_above (set.range f))
  (h_mon : monotone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  obtain ⟨B, hB⟩ := (real.exists_is_lub ((set.range f)) (set.range_nonempty f) h_bdd),
  exact ⟨B, tendsto_at_top_is_lub h_mon hB⟩
end

/-- An antitone, bounded below sequence `f : ℕ → ℝ` has a finite limit. -/
lemma real.tendsto_of_is_bounded_antitone {f : ℕ → ℝ} (h_bdd : bdd_below (set.range f)) 
  (h_ant : antitone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  obtain ⟨B, hB⟩ := (real.exists_is_glb (set.range_nonempty f) h_bdd),
  exact ⟨B, tendsto_at_top_is_glb h_ant hB⟩,
end

/-- An antitone sequence `f : ℕ → ℝ≥0` has a finite limit. -/
lemma nnreal.tendsto_of_is_bounded_antitone {f : ℕ → nnreal} (h_ant : antitone f) : 
  ∃ r : nnreal, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  have h_bdd_0 : (0 : ℝ) ∈ lower_bounds (set.range (λ (n : ℕ), (f n : ℝ))),
  { intros r hr,
    obtain ⟨n, hn⟩ := set.mem_range.mpr hr,
    simp_rw [← hn],
    exact nnreal.coe_nonneg _ },
  have h_bdd : bdd_below (set.range (λ n, (f n : ℝ))) := ⟨0, h_bdd_0⟩,
  obtain ⟨L, hL⟩ := real.tendsto_of_is_bounded_antitone h_bdd h_ant,
  have hL0 : 0 ≤ L,
  { have h_glb : is_glb (set.range (λ n, (f n : ℝ))) L := is_glb_of_tendsto_at_top h_ant hL,
    exact (le_is_glb_iff h_glb).mpr h_bdd_0 },
  use ⟨L, hL0⟩,
  rw ← nnreal.tendsto_coe,
  exact hL,
end