/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.SymReduce

/-! # Properties of the autocorrelation `Phi0 p = F ⋆ F̃`, `F = p·1_{H2}`

For continuous `p`: `Phi0_supp` (support in `|t₁|+|t₂|+|t₁+t₂| ≤ 2`), `Phi0_mass`
(`∫ Phi0 = (∫F)²`), `Phi0_continuous`, and `Phi0_Inv` (invariance under the three generators
when `p` is invariant). -/

open MeasureTheory Set Topology

namespace XiPrime8845.Triple.Sym
open Region Nu3

variable {p : ℝ × ℝ → ℝ}

theorem isClosed_H2 : IsClosed H2 :=
  isClosed_hexD.preimage (by fun_prop : Continuous fun u : ℝ × ℝ => (2 : ℝ) • u)

theorem mem_H2' (u : ℝ × ℝ) : u ∈ H2 ↔
    (-1 ≤ 2 * u.1 ∧ 2 * u.1 ≤ 1) ∧ (-1 ≤ 2 * u.2 ∧ 2 * u.2 ≤ 1)
      ∧ (-1 ≤ 2 * u.1 + 2 * u.2 ∧ 2 * u.1 + 2 * u.2 ≤ 1) := by
  show (2 : ℝ) • u ∈ hexD ↔ _
  rw [mem_hexD]; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

theorem H2_sub_box : H2 ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
  intro u hu
  have := (mem_H2' u).1 hu
  exact ⟨⟨by linarith [this.1.1], by linarith [this.1.2]⟩,
    ⟨by linarith [this.2.1.1], by linarith [this.2.1.2]⟩⟩

theorem integrable_F (hp : Continuous p) : Integrable (Fof p) :=
  (integrable_indicator_iff isClosed_H2.measurableSet).2
    ((hp.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set H2_sub_box)

theorem F_bound (hp : Continuous p) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u, ‖Fof p u‖ ≤ M := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn hp.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun u => ?_⟩
  by_cases hu : u ∈ H2
  · simp only [Fof, indicator_of_mem hu]
    exact (hB u (H2_sub_box hu)).trans (le_max_left _ _)
  · simp only [Fof, indicator_of_notMem hu, norm_zero]
    exact le_max_right _ _

theorem Phi0_supp (t : ℝ × ℝ) (h : Phi0 p t ≠ 0) : hexSum t ≤ 2 := by
  by_contra hc
  apply h
  unfold Phi0
  have : ∀ u, Fof p u * Fof p (u - t) = 0 := by
    intro u
    by_cases h1 : u ∈ H2
    · by_cases h2 : u - t ∈ H2
      · exfalso
        apply hc
        have a := (mem_H2_iff u).1 h1
        have b := (mem_H2_iff (u - t)).1 h2
        simp only [Prod.fst_sub, Prod.snd_sub] at b
        have e1 := abs_sub u.1 (u.1 - t.1)
        have e2 := abs_sub u.2 (u.2 - t.2)
        have e3 := abs_sub (u.1 + u.2) (u.1 - t.1 + (u.2 - t.2))
        rw [sub_sub_cancel] at e1 e2
        rw [show u.1 + u.2 - (u.1 - t.1 + (u.2 - t.2)) = t.1 + t.2 by ring] at e3
        unfold hexSum
        linarith
      · simp [Fof, indicator_of_notMem h2]
    · simp [Fof, indicator_of_notMem h1]
  simp [this]

theorem Phi0_mass (hp : Continuous p) : ∫ t, Phi0 p t = mF p ^ 2 := by
  have iF := integrable_F hp
  have iFt : Integrable fun v : ℝ × ℝ => Fof p (-v) := iF.comp_neg
  have hconv : ∀ t, Phi0 p t = (MeasureTheory.convolution (Fof p) (fun v => Fof p (-v))
      (ContinuousLinearMap.mul ℝ ℝ) volume) t := by
    intro t
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply', neg_sub]
    rfl
  simp only [hconv]
  rw [integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) iF iFt,
    integral_neg_eq_self (Fof p) volume]
  simp only [ContinuousLinearMap.mul_apply']
  unfold mF
  ring

/-! ## invariance -/

theorem Fof_inv {g : ℝ × ℝ → ℝ × ℝ} (hH : ∀ u, g u ∈ H2 ↔ u ∈ H2) (hpg : ∀ u, p (g u) = p u)
    (u : ℝ × ℝ) : Fof p (g u) = Fof p u := by
  by_cases hu : u ∈ H2
  · simp only [Fof, indicator_of_mem hu, indicator_of_mem ((hH u).2 hu), hpg]
  · simp only [Fof, indicator_of_notMem hu, indicator_of_notMem (fun h => hu ((hH u).1 h))]

theorem Phi0_inv {g : ℝ × ℝ → ℝ × ℝ} (mp : MeasurePreserving g volume volume)
    (emb : MeasurableEmbedding g) (hsub : ∀ u t, g u - g t = g (u - t))
    (hF : ∀ u, Fof p (g u) = Fof p u) (t : ℝ × ℝ) : Phi0 p (g t) = Phi0 p t := by
  unfold Phi0
  rw [← mp.integral_comp emb (fun u => Fof p u * Fof p (u - g t))]
  simp only [hsub, hF]

def gS (ξ : ℝ × ℝ) : ℝ × ℝ := (ξ.2, ξ.1)
def gN (ξ : ℝ × ℝ) : ℝ × ℝ := (-ξ.1, -ξ.2)

theorem Phi0_Inv (hsw : ∀ u : ℝ × ℝ, p (u.2, u.1) = p u)
    (hu : ∀ u : ℝ × ℝ, p (u.1, -(u.1 + u.2)) = p u) (hn : ∀ u : ℝ × ℝ, p (-u.1, -u.2) = p u) :
    Inv (Phi0 p) where
  sw := by
    intro ξ
    have mp : MeasurePreserving gS (volume : Measure (ℝ × ℝ)) volume :=
      Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    have emb : MeasurableEmbedding gS :=
      (invEquiv gS (by unfold gS; fun_prop) (fun x => rfl)).measurableEmbedding
    refine Phi0_inv (g := gS) mp emb (fun u t => rfl) (Fof_inv (fun u => ?_) hsw) ξ
    rw [mem_H2_iff, mem_H2_iff]
    simp only [gS]
    rw [add_comm u.2 u.1, add_comm |u.2| |u.1|]
  u := by
    intro ξ
    refine Phi0_inv (g := gU) mp_gU emb_gU (fun u t => ?_) (Fof_inv (fun u => ?_) hu) ξ
    · ext <;> simp [gU] <;> ring
    · rw [mem_H2_iff, mem_H2_iff]
      simp only [gU]
      rw [show u.1 + -(u.1 + u.2) = -u.2 by ring, abs_neg, abs_neg]
      constructor <;> intro h <;> linarith
  n := by
    intro ξ
    have mp : MeasurePreserving gN (volume : Measure (ℝ × ℝ)) volume := by
      have h := mp_neg
      have e : (fun ξ : ℝ × ℝ => -ξ) = gN := by funext ξ; rfl
      rwa [e] at h
    have emb : MeasurableEmbedding gN :=
      (invEquiv gN (by unfold gN; fun_prop) (fun x => by ext <;> simp [gN])).measurableEmbedding
    refine Phi0_inv (g := gN) mp emb (fun u t => ?_) (Fof_inv (fun u => ?_) hn) ξ
    · ext <;> simp [gN] <;> ring
    · rw [mem_H2_iff, mem_H2_iff]
      simp only [gN]
      rw [← neg_add, abs_neg, abs_neg, abs_neg]

/-! ## continuity -/

def Oin : Set (ℝ × ℝ) := {v | |2 * v.1| < 1 ∧ |2 * v.2| < 1 ∧ |2 * v.1 + 2 * v.2| < 1}

theorem isOpen_Oin : IsOpen Oin := by
  have : Oin = {v : ℝ × ℝ | |2 * v.1| < 1} ∩ ({v : ℝ × ℝ | |2 * v.2| < 1}
      ∩ {v : ℝ × ℝ | |2 * v.1 + 2 * v.2| < 1}) := by ext v; simp [Oin]
  rw [this]
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    ((isOpen_lt (by fun_prop) continuous_const).inter (isOpen_lt (by fun_prop) continuous_const))

theorem Oin_sub : Oin ⊆ H2 := by
  rintro v ⟨a, b, c⟩
  rw [mem_H2']
  rw [abs_lt] at a b c
  exact ⟨⟨a.1.le, a.2.le⟩, ⟨b.1.le, b.2.le⟩, ⟨c.1.le, c.2.le⟩⟩

theorem contAt_F (hp : Continuous p) {z : ℝ × ℝ} (hz : z ∈ Oin ∨ z ∉ H2) :
    ContinuousAt (Fof p) z := by
  rcases hz with hz | hz
  · refine hp.continuousAt.congr ?_
    filter_upwards [isOpen_Oin.mem_nhds hz] with v hv
    simp [Fof, indicator_of_mem (Oin_sub hv)]
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [isClosed_H2.isOpen_compl.mem_nhds hz] with v hv
    simp [Fof, indicator_of_notMem hv]

theorem ae_good (t : ℝ × ℝ) : ∀ᵐ u : ℝ × ℝ, (u - t) ∈ Oin ∨ (u - t) ∉ H2 := by
  have n1 := measure_eq_zero_iff_ae_notMem.1 (null_vert (t.1 + 1 / 2))
  have n2 := measure_eq_zero_iff_ae_notMem.1 (null_vert (t.1 - 1 / 2))
  have n3 := measure_eq_zero_iff_ae_notMem.1
    (null_graph (g := fun _ => t.2 + 1 / 2) measurable_const)
  have n4 := measure_eq_zero_iff_ae_notMem.1
    (null_graph (g := fun _ => t.2 - 1 / 2) measurable_const)
  have n5 := measure_eq_zero_iff_ae_notMem.1
    (null_graph (g := fun x => t.1 + t.2 + 1 / 2 - x) (by fun_prop))
  have n6 := measure_eq_zero_iff_ae_notMem.1
    (null_graph (g := fun x => t.1 + t.2 - 1 / 2 - x) (by fun_prop))
  filter_upwards [n1, n2, n3, n4, n5, n6] with u h1 h2 h3 h4 h5 h6
  by_cases hH : (u - t) ∈ H2
  · left
    have m := (mem_H2' (u - t)).1 hH
    simp only [Prod.fst_sub, Prod.snd_sub] at m
    show |2 * (u - t).1| < 1 ∧ |2 * (u - t).2| < 1 ∧ |2 * (u - t).1 + 2 * (u - t).2| < 1
    simp only [Prod.fst_sub, Prod.snd_sub, abs_lt]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact lt_of_le_of_ne m.1.1 fun e => h2 (show u.1 = t.1 - 1 / 2 by linarith)
    · exact lt_of_le_of_ne m.1.2 fun e => h1 (show u.1 = t.1 + 1 / 2 by linarith)
    · exact lt_of_le_of_ne m.2.1.1 fun e => h4 (show u.2 = t.2 - 1 / 2 by linarith)
    · exact lt_of_le_of_ne m.2.1.2 fun e => h3 (show u.2 = t.2 + 1 / 2 by linarith)
    · exact lt_of_le_of_ne m.2.2.1 fun e => h6 (show u.2 = t.1 + t.2 - 1 / 2 - u.1 by linarith)
    · exact lt_of_le_of_ne m.2.2.2 fun e => h5 (show u.2 = t.1 + t.2 + 1 / 2 - u.1 by linarith)
  · exact Or.inr hH

theorem Phi0_continuous (hp : Continuous p) : Continuous (Phi0 p) := by
  have iF := integrable_F hp
  obtain ⟨M, hM0, hM⟩ := F_bound hp
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  refine continuousAt_of_dominated (F := fun t u => Fof p u * Fof p (u - t))
    (bound := fun u => ‖Fof p u‖ * M) (Filter.Eventually.of_forall fun t => ?_)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun u => ?_)
    (iF.norm.mul_const M) ?_
  · exact iF.aestronglyMeasurable.mul (iF.comp_sub_right t).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · filter_upwards [ae_good t₀] with u hu
    have h1 : ContinuousAt (fun t : ℝ × ℝ => u - t) t₀ := by fun_prop
    exact continuousAt_const.mul ((contAt_F hp hu).comp_of_eq h1 rfl)

end XiPrime8845.Triple.Sym

#print axioms XiPrime8845.Triple.Sym.Phi0_continuous
#print axioms XiPrime8845.Triple.Sym.Phi0_mass
#print axioms XiPrime8845.Triple.Sym.Phi0_Inv
