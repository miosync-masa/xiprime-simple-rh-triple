/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.Jacobian
import TripleCorrelation.Nu3InclExcl

/-! # Symmetry reduction of the Fourier-side functional (real-valued, general `Φ`)

For a continuous `Φ : ℝ × ℝ → ℝ` vanishing outside `|ξ₁|+|ξ₂|+|ξ₁+ξ₂| ≤ 2` and invariant under
`(x,y) ↦ (y,x)`, `(x,y) ↦ (x, −x−y)`, `(x,y) ↦ (−x,−y)` (`Inv`):

`Φ(0) − Σ_{3 lines} ∫₋₁¹ (1−|u|) Φ + 2 ∫ K·Φ = 2·∫Φ + Φ(0) + 6·A − 12·B`  (`nu3R_eq`),

`A = ∫₀¹ (u−1)·Φ(−u,u) du`, `B = ∫_{TriH} ξ₂·Φ(ξ) dξ`, `TriH = {0 ≤ ξ₂ ≤ 1, −ξ₂ ≤ ξ₁ ≤ 0}`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Sym
open Region Nu3

structure Inv (Φ : ℝ × ℝ → ℝ) : Prop where
  sw : ∀ ξ : ℝ × ℝ, Φ (ξ.2, ξ.1) = Φ ξ
  u : ∀ ξ : ℝ × ℝ, Φ (ξ.1, -(ξ.1 + ξ.2)) = Φ ξ
  n : ∀ ξ : ℝ × ℝ, Φ (-ξ.1, -ξ.2) = Φ ξ

def gA (ξ : ℝ × ℝ) : ℝ × ℝ := (-ξ.1, ξ.1 + ξ.2)
def gC (ξ : ℝ × ℝ) : ℝ × ℝ := (-ξ.2, -ξ.1)
def gU (ξ : ℝ × ℝ) : ℝ × ℝ := (ξ.1, -(ξ.1 + ξ.2))

theorem Inv.A {Φ : ℝ × ℝ → ℝ} (h : Inv Φ) (ξ : ℝ × ℝ) : Φ (gA ξ) = Φ ξ := by
  have h1 := h.n (ξ.1, -(ξ.1 + ξ.2))
  have h2 := h.u ξ
  simp only [neg_neg] at h1
  exact h1.trans h2

theorem Inv.C {Φ : ℝ × ℝ → ℝ} (h : Inv Φ) (ξ : ℝ × ℝ) : Φ (gC ξ) = Φ ξ :=
  (h.n (ξ.2, ξ.1)).trans (h.sw ξ)

/-- an involution of the plane as a measurable equivalence. -/
def invEquiv (f : ℝ × ℝ → ℝ × ℝ) (hf : Measurable f) (hinv : ∀ x, f (f x) = x) :
    (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := f
  invFun := f
  left_inv := hinv
  right_inv := hinv
  measurable_toFun := hf
  measurable_invFun := hf

theorem mp_neg : MeasurePreserving (fun ξ : ℝ × ℝ => -ξ) (volume : Measure (ℝ × ℝ)) volume :=
  Measure.measurePreserving_neg _

theorem mp_gU : MeasurePreserving gU (volume : Measure (ℝ × ℝ)) volume := mp_U

theorem mp_gA : MeasurePreserving gA (volume : Measure (ℝ × ℝ)) volume := by
  have h := mp_neg.comp mp_gU
  have e : (fun ξ : ℝ × ℝ => -ξ) ∘ gU = gA := by funext ξ; ext <;> simp [gU, gA]
  rwa [e] at h

theorem mp_gC : MeasurePreserving gC (volume : Measure (ℝ × ℝ)) volume := by
  have h := mp_neg.comp
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have e : (fun ξ : ℝ × ℝ => -ξ) ∘ Prod.swap = gC := by funext ξ; ext <;> simp [gC]
  rwa [e] at h

theorem emb_gU : MeasurableEmbedding gU :=
  (invEquiv gU (by unfold gU; fun_prop) (fun x => by ext <;> simp [gU])).measurableEmbedding
theorem emb_gA : MeasurableEmbedding gA :=
  (invEquiv gA (by unfold gA; fun_prop) (fun x => by ext <;> simp [gA])).measurableEmbedding
theorem emb_gC : MeasurableEmbedding gC :=
  (invEquiv gC (by unfold gC; fun_prop) (fun x => by ext <;> simp [gC])).measurableEmbedding

/-! ## the three lines -/

theorem even_line {φ : ℝ → ℝ} (hφ : Continuous φ) (he : ∀ u, φ (-u) = φ u) :
    ∫ u in (-1 : ℝ)..1, (1 - |u|) * φ u = -2 * ∫ u in (0 : ℝ)..1, (u - 1) * φ u := by
  have hc : Continuous fun u : ℝ => (1 - |u|) * φ u := by fun_prop
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-1) 0)
    (hc.intervalIntegrable 0 1) (μ := volume)
  have h2 : ∫ u in (-1 : ℝ)..0, (1 - |u|) * φ u = ∫ u in (0 : ℝ)..1, (1 - |u|) * φ u := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (fun u : ℝ => (1 - |u|) * φ u)
    simp only [abs_neg, he, neg_zero] at this
    exact this.symm
  have h3 : ∫ u in (0 : ℝ)..1, (1 - |u|) * φ u = ∫ u in (0 : ℝ)..1, -((u - 1) * φ u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le zero_le_one] at hu
    show (1 - |u|) * φ u = -((u - 1) * φ u)
    rw [abs_of_nonneg hu.1]; ring
  rw [← h1, h2, h3, intervalIntegral.integral_neg]; ring

variable {Φ : ℝ × ℝ → ℝ}

noncomputable def AR (Φ : ℝ × ℝ → ℝ) : ℝ := ∫ u in (0 : ℝ)..1, (u - 1) * Φ (-u, u)
noncomputable def BR (Φ : ℝ × ℝ → ℝ) : ℝ := ∫ ξ in TriH, ξ.2 * Φ ξ

theorem lines_eq (hΦ : Continuous Φ) (inv : Inv Φ) :
    (∫ u in (-1 : ℝ)..1, (1 - |u|) * Φ (u, -u)) = -2 * AR Φ ∧
    (∫ u in (-1 : ℝ)..1, (1 - |u|) * Φ (u, 0)) = -2 * AR Φ ∧
    (∫ u in (-1 : ℝ)..1, (1 - |u|) * Φ (0, u)) = -2 * AR Φ := by
  have hφ : Continuous fun u : ℝ => Φ (-u, u) := hΦ.comp (by fun_prop)
  have e1 : ∀ u : ℝ, Φ (u, -u) = Φ (-u, u) := fun u => by
    have := inv.n (-u, u); simpa using this
  have e2 : ∀ u : ℝ, Φ (u, 0) = Φ (-u, u) := fun u => by
    have := inv.u (u, 0); simp only [add_zero] at this; rw [← this, e1]
  have e3 : ∀ u : ℝ, Φ (0, u) = Φ (-u, u) := fun u => by
    have := inv.sw (0, u); simp only at this; rw [← this, e2]
  have base := even_line hφ (fun u => by simp only [neg_neg]; exact e1 u)
  refine ⟨?_, ?_, ?_⟩
  · simp only [e1]; exact base
  · simp only [e2]; exact base
  · simp only [e3]; exact base

/-! ## the plane term -/

theorem mem_TriH (η : ℝ × ℝ) : η ∈ TriH ↔ (0 ≤ η.2 ∧ η.2 ≤ 1) ∧ (-η.2 ≤ η.1 ∧ η.1 ≤ 0) := by
  show (2 : ℝ) • η ∈ Tri ↔ _
  simp only [Tri, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem measurableSet_TriH : MeasurableSet TriH :=
  (isClosed_Tri.preimage (by fun_prop : Continuous fun u : ℝ × ℝ => (2 : ℝ) • u)).measurableSet

theorem hcs_of_supp (hsupp : ∀ ξ, Φ ξ ≠ 0 → hexSum ξ ≤ 2) : HasCompactSupport Φ := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) 2) fun ξ hξ => ?_
  by_contra h
  have h2 := hsupp ξ h
  rw [mem_closedBall_zero_iff, Prod.norm_def, not_le, lt_max_iff] at hξ
  simp only [Real.norm_eq_abs] at hξ
  unfold hexSum at h2
  have h3 := abs_nonneg (ξ.1 + ξ.2)
  have h4 := abs_nonneg ξ.1
  have h5 := abs_nonneg ξ.2
  rcases hξ with hξ | hξ <;> linarith

theorem int_w (hΦ : Continuous Φ) (hcs : HasCompactSupport Φ) {w : ℝ × ℝ → ℝ}
    (hw : Continuous w) : Integrable fun ξ => w ξ * Φ ξ :=
  (hw.mul hΦ).integrable_of_hasCompactSupport hcs.mul_left

/-- the half-plane weight reduces to the triangle `TriH`. -/
theorem half_eq (hΦ : Continuous Φ) (hsupp : ∀ ξ, Φ ξ ≠ 0 → hexSum ξ ≤ 2) (inv : Inv Φ) :
    ∫ ξ : ℝ × ℝ, max ξ.2 0 * Φ ξ = 2 * BR Φ := by
  have hcs := hcs_of_supp hsupp
  let h : ℝ × ℝ → ℝ := TriH.indicator fun η => η.2 * Φ η
  let hA : ℝ × ℝ → ℝ := TriH.indicator fun η => (η.1 + η.2) * Φ η
  let hC : ℝ × ℝ → ℝ := TriH.indicator fun η => (-η.1) * Φ η
  have ih : Integrable h := (int_w hΦ hcs (by fun_prop)).indicator measurableSet_TriH
  have iA : Integrable hA := (int_w hΦ hcs (by fun_prop)).indicator measurableSet_TriH
  have iC : Integrable hC := (int_w hΦ hcs (by fun_prop)).indicator measurableSet_TriH
  have iA' : Integrable fun ξ => hA (gA ξ) := (mp_gA.integrable_comp_emb emb_gA).2 iA
  have iC' : Integrable fun ξ => hC (gC ξ) := (mp_gC.integrable_comp_emb emb_gC).2 iC
  have sum : ∀ η, hA η + hC η = h η := by
    intro η
    by_cases hη : η ∈ TriH
    · simp only [h, hA, hC, indicator_of_mem hη]; ring
    · simp only [h, hA, hC, indicator_of_notMem hη]; ring
  have ae : (fun ξ : ℝ × ℝ => max ξ.2 0 * Φ ξ)
      =ᵐ[volume] fun ξ => h ξ + (hA (gA ξ) + hC (gC ξ)) := by
    filter_upwards [null_lines] with ξ hξ
    obtain ⟨hx, hy, hs⟩ := hξ
    by_cases h0 : Φ ξ = 0
    · have a0 : Φ (gA ξ) = 0 := by rw [inv.A, h0]
      have c0 : Φ (gC ξ) = 0 := by rw [inv.C, h0]
      have z1 : h ξ = 0 := indicator_apply_eq_zero.2 fun _ => by simp [h0]
      have z2 : hA (gA ξ) = 0 := indicator_apply_eq_zero.2 fun _ => by simp [a0]
      have z3 : hC (gC ξ) = 0 := indicator_apply_eq_zero.2 fun _ => by simp [c0]
      show max ξ.2 0 * Φ ξ = h ξ + (hA (gA ξ) + hC (gC ξ))
      rw [z1, z2, z3, h0]; ring
    · have hsum := hsupp ξ h0
      unfold hexSum at hsum
      have f1 := le_abs_self ξ.1
      have f2 := neg_le_abs ξ.1
      have f3 := le_abs_self ξ.2
      have f4 := neg_le_abs ξ.2
      have f5 := le_abs_self (ξ.1 + ξ.2)
      have f6 := neg_le_abs (ξ.1 + ξ.2)
      rcases lt_or_gt_of_ne hy with hy | hy
      · have m1 : ξ ∉ TriH := fun m => by have := (mem_TriH ξ).1 m; linarith [this.1.1]
        have m2 : gA ξ ∉ TriH := fun m => by
          have := (mem_TriH (gA ξ)).1 m; simp only [gA] at this; linarith [this.1.1, this.2.1, this.2.2]
        have m3 : gC ξ ∉ TriH := fun m => by
          have := (mem_TriH (gC ξ)).1 m; simp only [gC] at this; linarith [this.2.1, this.2.2]
        simp only [h, hA, hC, indicator_of_notMem m1, indicator_of_notMem m2,
          indicator_of_notMem m3, max_eq_right hy.le]
        ring
      · rcases lt_or_gt_of_ne hx with hx | hx
        · rcases lt_or_gt_of_ne hs with hs | hs
          · -- x < 0, x + y < 0 : gC ξ ∈ TriH
            have m1 : ξ ∉ TriH := fun m => by have := (mem_TriH ξ).1 m; linarith [this.2.1]
            have m2 : gA ξ ∉ TriH := fun m => by
              have := (mem_TriH (gA ξ)).1 m; simp only [gA] at this; linarith [this.1.1]
            have m3 : gC ξ ∈ TriH := (mem_TriH (gC ξ)).2 (by
              simp only [gC]; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)
            simp only [h, hA, hC, indicator_of_notMem m1, indicator_of_notMem m2,
              indicator_of_mem m3, max_eq_left hy.le, inv.C]
            simp only [gC]; ring
          · -- x < 0 < x + y : ξ ∈ TriH
            have m1 : ξ ∈ TriH := (mem_TriH ξ).2
              ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
            have m2 : gA ξ ∉ TriH := fun m => by
              have := (mem_TriH (gA ξ)).1 m; simp only [gA] at this; linarith [this.2.2]
            have m3 : gC ξ ∉ TriH := fun m => by
              have := (mem_TriH (gC ξ)).1 m; simp only [gC] at this; linarith [this.2.1]
            simp only [h, hA, hC, indicator_of_mem m1, indicator_of_notMem m2,
              indicator_of_notMem m3, max_eq_left hy.le]
            ring
        · -- x > 0 : gA ξ ∈ TriH
          have m1 : ξ ∉ TriH := fun m => by have := (mem_TriH ξ).1 m; linarith [this.2.2]
          have m2 : gA ξ ∈ TriH := (mem_TriH (gA ξ)).2 (by
            simp only [gA]; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)
          have m3 : gC ξ ∉ TriH := fun m => by
            have := (mem_TriH (gC ξ)).1 m; simp only [gC] at this; linarith [this.1.1]
          simp only [h, hA, hC, indicator_of_notMem m1, indicator_of_mem m2,
            indicator_of_notMem m3, max_eq_left hy.le, inv.A]
          simp only [gA]; ring
  have a1 := integral_add ih (iA'.add iC')
  have a2 := integral_add iA' iC'
  have a3 := integral_add iA iC
  simp only [Pi.add_apply] at a1
  rw [integral_congr_ae ae, a1, a2, mp_gA.integral_comp emb_gA hA, mp_gC.integral_comp emb_gC hC,
    ← a3]
  simp only [sum]
  have : ∫ η, h η = BR Φ := integral_indicator measurableSet_TriH
  rw [this]; ring

theorem abs2_eq (hΦ : Continuous Φ) (hsupp : ∀ ξ, Φ ξ ≠ 0 → hexSum ξ ≤ 2) (inv : Inv Φ) :
    ∫ ξ : ℝ × ℝ, |ξ.2| * Φ ξ = 4 * BR Φ := by
  have hcs := hcs_of_supp hsupp
  have i1 : Integrable fun ξ : ℝ × ℝ => max ξ.2 0 * Φ ξ := int_w hΦ hcs (by fun_prop)
  have i2 : Integrable fun ξ : ℝ × ℝ => max (-ξ).2 0 * Φ (-ξ) := i1.comp_neg
  have e : ∀ ξ : ℝ × ℝ, |ξ.2| * Φ ξ = max ξ.2 0 * Φ ξ + max (-ξ).2 0 * Φ (-ξ) := by
    intro ξ
    have hn : Φ (-ξ) = Φ ξ := inv.n ξ
    rw [hn]
    rcases le_total 0 ξ.2 with hh | hh
    · rw [abs_of_nonneg hh, max_eq_left hh, max_eq_right (by simpa using hh)]; ring
    · rw [abs_of_nonpos hh, max_eq_right hh, max_eq_left (by simpa using hh)]; simp
  simp only [e]
  rw [integral_add i1 i2, integral_neg_eq_self (fun ξ : ℝ × ℝ => max ξ.2 0 * Φ ξ) volume,
    half_eq hΦ hsupp inv]
  ring

theorem hexSum_eq (hΦ : Continuous Φ) (hsupp : ∀ ξ, Φ ξ ≠ 0 → hexSum ξ ≤ 2) (inv : Inv Φ) :
    ∫ ξ : ℝ × ℝ, hexSum ξ * Φ ξ = 12 * BR Φ := by
  have hcs := hcs_of_supp hsupp
  have i1 : Integrable fun ξ : ℝ × ℝ => |ξ.1| * Φ ξ := int_w hΦ hcs (by fun_prop)
  have i2 : Integrable fun ξ : ℝ × ℝ => |ξ.2| * Φ ξ := int_w hΦ hcs (by fun_prop)
  have i3 : Integrable fun ξ : ℝ × ℝ => |ξ.1 + ξ.2| * Φ ξ := int_w hΦ hcs (by fun_prop)
  have e1 : ∫ ξ : ℝ × ℝ, |ξ.1| * Φ ξ = ∫ ξ : ℝ × ℝ, |ξ.2| * Φ ξ := by
    have := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun ξ : ℝ × ℝ => |ξ.2| * Φ ξ)
    simp only [Prod.snd_swap] at this
    rw [← Measure.volume_eq_prod] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show |ξ.1| * Φ ξ = |ξ.1| * Φ ξ.swap
    rw [show ξ.swap = (ξ.2, ξ.1) from rfl, inv.sw]
  have e3 : ∫ ξ : ℝ × ℝ, |ξ.1 + ξ.2| * Φ ξ = ∫ ξ : ℝ × ℝ, |ξ.2| * Φ ξ := by
    rw [← mp_gU.integral_comp emb_gU (fun ξ : ℝ × ℝ => |ξ.2| * Φ ξ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show |ξ.1 + ξ.2| * Φ ξ = |(gU ξ).2| * Φ (gU ξ)
    simp only [gU, abs_neg, inv.u]
  have e : ∀ ξ : ℝ × ℝ, hexSum ξ * Φ ξ = |ξ.1| * Φ ξ + |ξ.2| * Φ ξ + |ξ.1 + ξ.2| * Φ ξ := by
    intro ξ; unfold hexSum; ring
  simp only [e]
  have b1 := integral_add (i1.add i2) i3
  have b2 := integral_add i1 i2
  simp only [Pi.add_apply] at b1
  rw [b1, b2, e1, e3, abs2_eq hΦ hsupp inv]
  ring

/-- the Fourier-side functional, real-valued. -/
noncomputable def nu3R (Φ : ℝ × ℝ → ℝ) : ℝ :=
  Φ (0, 0) - ((∫ u in (-1 : ℝ)..1, (1 - |u|) * Φ (u, -u)) + (∫ u in (-1 : ℝ)..1, (1 - |u|) * Φ (u, 0))
    + ∫ u in (-1 : ℝ)..1, (1 - |u|) * Φ (0, u)) + 2 * ∫ ξ : ℝ × ℝ, K ξ * Φ ξ

/-- **symmetry reduction.** -/
theorem nu3R_eq (hΦ : Continuous Φ) (hsupp : ∀ ξ, Φ ξ ≠ 0 → hexSum ξ ≤ 2) (inv : Inv Φ) :
    nu3R Φ = 2 * (∫ ξ : ℝ × ℝ, Φ ξ) + Φ (0, 0) + 6 * AR Φ - 12 * BR Φ := by
  have hcs := hcs_of_supp hsupp
  have i1 : Integrable Φ := hΦ.integrable_of_hasCompactSupport hcs
  have i2 : Integrable fun ξ : ℝ × ℝ => hexSum ξ * Φ ξ :=
    int_w hΦ hcs (by unfold hexSum; fun_prop)
  have eK : ∫ ξ : ℝ × ℝ, K ξ * Φ ξ = (∫ ξ : ℝ × ℝ, Φ ξ) - (1 / 2) * ∫ ξ : ℝ × ℝ, hexSum ξ * Φ ξ := by
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases h : Φ ξ = 0
    · simp [h]
    · have h2 := hsupp ξ h
      have : K ξ = 1 - hexSum ξ / 2 := by
        unfold K hexSum at *; exact max_eq_right (by linarith)
      simp only [this]; ring
  obtain ⟨l1, l2, l3⟩ := lines_eq hΦ inv
  unfold nu3R
  rw [l1, l2, l3, eK, hexSum_eq hΦ hsupp inv]
  ring

end XiPrime8845.Triple.Sym

#print axioms XiPrime8845.Triple.Sym.nu3R_eq
