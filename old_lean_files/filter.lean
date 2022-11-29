import data.real.basic
import order.filter.at_top_bot
import order.liminf_limsup
import topology.metric_space.basic
import topology.algebra.order.monotone_convergence
import topology.instances.nnreal

open_locale filter topological_space

theorem real.exists_is_glb {S : set ℝ} (hne : S.nonempty) (hbdd : bdd_below S) :
  ∃ x, is_glb S x :=
begin
  set T := - S with hT,
  have hT_ne : T.nonempty := set.nonempty_neg.mpr hne,
  have hT_bdd : bdd_above T := bdd_above_neg.mpr hbdd,
  use -classical.some (real.exists_is_lub T hT_ne hT_bdd),
  simpa [← is_lub_neg] using (classical.some_spec (real.exists_is_lub T hT_ne hT_bdd)),
end

/- lemma le_of_is_lub {α : Type*} [preorder α] (S : set α) (B : α) (hB : is_lub S B) :
  ∀ s ∈ S, s ≤ B := 
begin
  intros s hs,
  simp [is_lub, is_least, mem_upper_bounds] at hB,
  exact hB.1 s hs,
end
 -/
lemma filter.tendsto_of_is_bounded_monotone {f : ℕ → ℝ} (h_bdd : bdd_above (set.range f))
  (h_mon : monotone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  obtain ⟨B, hB⟩ := (real.exists_is_lub ((set.range f)) (set.range_nonempty f) h_bdd),
  use B,
  exact tendsto_at_top_is_lub h_mon hB,
end

lemma real.tendsto_of_is_bounded_antitone {f : ℕ → ℝ} (h_bdd : bdd_below (set.range f)) 
  (h_ant : antitone f) : ∃ r : ℝ, filter.tendsto f filter.at_top (𝓝 r) :=
begin
  obtain ⟨B, hB⟩ := (real.exists_is_glb (set.range_nonempty f) h_bdd),
  use B,
  exact tendsto_at_top_is_glb h_ant hB,
end

lemma nnreal.tendsto_of_is_bounded_antitone {f : ℕ → nnreal} (h_bdd : bdd_below (set.range f)) 
  (h_ant : antitone f) : ∃ r : nnreal, filter.tendsto f filter.at_top (𝓝 r) :=
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

