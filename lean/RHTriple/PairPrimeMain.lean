/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairPrimeSeparation
import RHTriple.PairGammaMain

/-! The equal-centre prime pulses against Q: their two signs supply
the density |u| on the frequency line, with the same height mass
as the two-gamma term. -/

noncomputable section
open Complex MeasureTheory Filter Topology Finset

namespace XiPrime8845.RHTriple

def pairPrimeScaled (a b Q : ℝ → ℂ) (d T : ℝ) : ℂ :=
  (∫ x : ℝ, Q (x/(T*Real.log T)) *
    (pairPulse a ⌊T^d⌋₊ T x true * pairPulse b ⌊T^d⌋₊ T x false))/(Real.log T:ℂ)^2

private def peak (a b Q : ℝ → ℂ) (W c : ℝ) : ℂ :=
  ∫ y : ℝ, Q (c+y/W) * (a (-y)*b y)

private theorem peak_uniform {a b Q : ℝ → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hcb : HasCompactSupport b)
    (hQ : Continuous Q) (hcQ : HasCompactSupport Q) {e : ℝ} (he : 0 < e) :
    ∀ᶠ T : ℝ in atTop, ∀ c, ‖peak a b Q (T*Real.log T) c - Q c*pairHeightMass a b‖ ≤ e := by
  let J := fun y : ℝ => a (-y)*b y
  have hj : Continuous J := (ha.comp continuous_neg).mul hb
  have hcJ : HasCompactSupport J := hcb.mul_left
  have hi : Integrable J := hj.integrable_of_hasCompactSupport hcJ
  let A := ∫ y, ‖J y‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  let δ := e/(1+A)
  have hδ : 0 < δ := div_pos he (by positivity)
  obtain ⟨s,hs,hh⟩ := Metric.uniformContinuous_iff.mp
    (hcQ.uniformContinuous_of_continuous hQ) δ hδ
  obtain ⟨R,hR⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hcJ
  have hW : Tendsto (fun T : ℝ => T*Real.log T) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  filter_upwards [hW.eventually_gt_atTop ((max R 0)/s), eventually_gt_atTop (1:ℝ)]
    with T hTs hT
  intro c
  let W := T*Real.log T
  have hw : 0 < W := mul_pos (by linarith) (Real.log_pos hT)
  let F (x : ℝ) := Q (c+x/W)*J x
  have hF : Continuous F := (hQ.comp (continuous_const.add (continuous_id.div_const _))).mul hj
  have hFi : Integrable F := hF.integrable_of_hasCompactSupport hcJ.mul_left
  unfold peak pairHeightMass
  change ‖(∫ x, F x)-Q c*(∫ x, J x)‖ ≤ _
  rw [← integral_const_mul, ← integral_sub hFi (hi.const_mul _)]
  refine (norm_integral_le_integral_norm _).trans
    ((integral_mono (hFi.sub (hi.const_mul _)).norm (hi.norm.const_mul δ) ?_).trans ?_)
  · intro x
    by_cases hx : J x = 0
    · simp [F,hx]
    have hg : |x| ≤ R := hR _ hx
    have hgap : dist (c+x/W) c < s := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_div, abs_of_pos hw, div_lt_iff₀ hw]
      exact (hg.trans (le_max_left _ _)).trans_lt (by
        have H := (div_lt_iff₀ hs).mp hTs
        simpa [W, mul_comm] using H)
    have H := (hh hgap).le
    rw [dist_eq_norm] at H
    change ‖F x - Q c*J x‖ ≤ δ*‖J x‖
    rw [show F x-Q c*J x = (Q (c+x/W)-Q c)*J x by unfold F; ring, norm_mul]
    exact mul_le_mul_of_nonneg_right H (norm_nonneg _)
  · rw [integral_const_mul]
    change δ*A ≤ e
    unfold δ
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith

private theorem primePeak_integral {a b Q : ℝ → ℂ} (a₀ W : ℝ) :
    (∫ x : ℝ, Q (x/W)*(a (a₀-x)*b (x-a₀))) = peak a b Q W (a₀/W) := by
  rw [← integral_add_right_eq_self (fun x => Q (x/W)*(a (a₀-x)*b (x-a₀))) a₀]
  unfold peak
  apply integral_congr_ae
  filter_upwards [] with x
  rw [add_sub_cancel_right, show a₀-(x+a₀) = -x by ring, add_div, add_comm (x/W)]

private def primeModel (Q : ℝ → ℂ) (d T : ℝ) : ℂ :=
  (∑ i ∈ pairPulseIndex ⌊T^d⌋₊, (pairedWeight i.2:ℂ) *
    Q (signedLog i.1 i.2/Real.log T))/(Real.log T:ℂ)^2

set_option maxHeartbeats 700000 in
theorem pairPrimeScaled_sub_model_tendsto {a b Q : ℝ → ℂ}
    (ha : Continuous a) (hca : HasCompactSupport a)
    (hb : Continuous b) (hcb : HasCompactSupport b)
    (hQ : Continuous Q) (hcQ : HasCompactSupport Q) {d : ℝ} (hd : 0 < d) (hd1 : d < 1) :
    Tendsto (fun T => pairPrimeScaled a b Q d T - primeModel Q d T * pairHeightMass a b)
      atTop (𝓝 0) := by
  obtain ⟨R₁,h₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hca
  obtain ⟨R₂,h₂⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hcb
  let R := max (max R₁ R₂) 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs₁ (x : ℝ) (hx : a x ≠ 0) : |x| ≤ R := (h₁ x hx).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hs₂ (x : ℝ) (hx : b x ≠ 0) : |x| ≤ R := (h₂ x hx).trans
    ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨A,hA,hMass⟩ := primePairMass_eventually_bounded hd
  rw [Metric.tendsto_nhds]
  intro ε hε
  let e := ε/(4*(1+A))
  have he : 0 < e := div_pos hε (by positivity)
  filter_upwards [pairPulse_product_eventually_diagonal hd1 hR hs₁ hs₂,
    peak_uniform ha hb hcb hQ hcQ he, Real.tendsto_log_atTop.eventually hMass,
    eventually_gt_atTop (1:ℝ)] with T hDiag hPeak hM hT
  let L := Real.log T
  let W := T*L
  let N := ⌊T^d⌋₊
  have hL : 0 < L := Real.log_pos hT
  have ht : 0 < T := by linarith
  have hef (i : Bool × ℕ) : T*signedLog i.1 i.2/W = signedLog i.1 i.2/L := by
    unfold W
    field_simp
  let F (i : Bool × ℕ) (x : ℝ) := Q (x/W)*((pairedWeight i.2:ℂ)*
    (a (T*signedLog i.1 i.2-x)*b (x-T*signedLog i.1 i.2)))
  have hiF (i : Bool × ℕ) : Integrable (F i) := by
    have hc : Continuous (F i) := by unfold F; fun_prop
    have hh := hcb.comp_homeomorph (Homeomorph.addRight (-(T*signedLog i.1 i.2)))
    change HasCompactSupport (fun x : ℝ => b (x+ -(T*signedLog i.1 i.2))) at hh
    have hh' : HasCompactSupport (fun x : ℝ => b (x - T*signedLog i.1 i.2)) := by
      simpa only [sub_eq_add_neg] using hh
    have hinner : HasCompactSupport (fun x : ℝ =>
        a (T*signedLog i.1 i.2-x)*b (x-T*signedLog i.1 i.2)) := hh'.mul_left
    have hmid : HasCompactSupport (fun x : ℝ => (pairedWeight i.2:ℂ)*
        (a (T*signedLog i.1 i.2-x)*b (x-T*signedLog i.1 i.2))) := hinner.mul_left
    exact hc.integrable_of_hasCompactSupport hmid.mul_left
  have hiF_eq (i : Bool × ℕ) : (∫ x, F i x) =
      (pairedWeight i.2:ℂ)*peak a b Q W (signedLog i.1 i.2/L) := by
    rw [← hef, ← primePeak_integral _ _, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    unfold F
    ring
  have hSum : pairPrimeScaled a b Q d T =
      (∑ i ∈ pairPulseIndex N, (pairedWeight i.2:ℂ)*
        peak a b Q W (signedLog i.1 i.2/L))/(L:ℂ)^2 := by
    unfold pairPrimeScaled
    simp_rw [hDiag, mul_sum]
    change (∫ x, ∑ i ∈ pairPulseIndex N, F i x)/(L:ℂ)^2 = _
    rw [integral_finsetSum _ (fun i _ => hiF i)]
    simp_rw [hiF_eq]
  let E (i : Bool × ℕ) := peak a b Q W (signedLog i.1 i.2/L) -
    Q (signedLog i.1 i.2/L)*pairHeightMass a b
  have hErr : pairPrimeScaled a b Q d T - primeModel Q d T*pairHeightMass a b =
      (∑ i ∈ pairPulseIndex N, (pairedWeight i.2:ℂ)*E i)/(L:ℂ)^2 := by
    rw [hSum, primeModel, div_mul_eq_mul_div, ← sub_div, sum_mul, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    unfold E
    ring
  have hp : (∑ i ∈ pairPulseIndex N, pairedWeight i.2) / L^2 ≤ 2*A := by
    have hh : N = ⌊Real.exp (d*L)⌋₊ := by
      unfold N L
      rw [Real.rpow_def_of_pos ht, mul_comm]
    rw [show (∑ i ∈ pairPulseIndex N, pairedWeight i.2) =
      2*(∑ n ∈ Ioc 0 ⌊Real.exp (d*L)⌋₊, pairedWeight n) by
        unfold pairPulseIndex
        rw [Finset.product_eq_sprod, Finset.sum_product univ (Icc 2 N) (fun i : Bool × ℕ => pairedWeight i.2)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
        rw [hh]
        congr 1
        apply Finset.sum_subset
        · intro n hhn
          simp only [mem_Icc,mem_Ioc] at hhn ⊢
          omega
        · intro n hn hnn
          have h := mem_Ioc.mp hn
          have he : n = 1 := by simp only [mem_Icc] at hnn; omega
          simp [he, pairedWeight]]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hM (by norm_num)
  rw [dist_zero_right, hErr, norm_div, norm_pow, norm_real, Real.norm_of_nonneg hL.le]
  have hnorm : ‖∑ i ∈ pairPulseIndex N, (pairedWeight i.2:ℂ)*E i‖ ≤
      (∑ i ∈ pairPulseIndex N, pairedWeight i.2)*e := by
    refine (norm_sum_le _ _).trans ?_
    rw [sum_mul]
    apply sum_le_sum
    intro i _
    rw [norm_mul, norm_real, Real.norm_of_nonneg (pairedWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hPeak _) (pairedWeight_nonneg _)
  refine (div_le_div_of_nonneg_right hnorm (by positivity)).trans_lt ?_
  rw [mul_comm _ e, mul_div_assoc]
  refine (mul_le_mul_of_nonneg_left hp he.le).trans_lt ?_
  unfold e
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith only [mul_nonneg hA hε.le, hε]

private theorem primeModel_tendsto {Q : ℝ → ℂ} (hQ : ContDiff ℝ 1 Q)
    (hcQ : HasCompactSupport Q) {d : ℝ} (hd : 0 < d)
    (hs : ∀ u, d ≤ |u| → Q u = 0) :
    Tendsto (primeModel Q d) atTop (𝓝 (∫ u : ℝ, Q u*((|u|:ℝ):ℂ))) := by
  let QR : ℝ → ℂ := fun u => Q (-u)
  have hQR : ContDiff ℝ 1 QR := hQ.comp (contDiff_id.neg)
  have hcQR : HasCompactSupport QR := hcQ.comp_homeomorph (Homeomorph.neg ℝ)
  have P := primePairWeight_complex_tendsto hQ hcQ hd (fun u hu =>
    hs u (hu.trans (le_abs_self _)))
  have N := primePairWeight_complex_tendsto hQR hcQR hd (fun u hu =>
    hs (-u) (by rw [abs_neg]; exact hu.trans (le_abs_self _)))
  have hm : (∫ u in (0:ℝ)..d, QR u*(u:ℂ)) + (∫ u in (0:ℝ)..d, Q u*(u:ℂ)) =
      ∫ u : ℝ, Q u*((|u|:ℝ):ℂ) := by
    let f : ℝ → ℂ := fun u => Q u*((|u|:ℝ):ℂ)
    have hf : Continuous f := hQ.continuous.mul (Complex.continuous_ofReal.comp continuous_abs)
    have he : (∫ u in (-d)..d, f u) = ∫ u : ℝ, f u := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hdu : d ≤ |u| := by
        by_contra! h
        exact hu ⟨(abs_lt.mp h).1,(abs_lt.mp h).2.le⟩
      simp [f,hs _ hdu]
    rw [← he, ← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-d) 0) (hf.intervalIntegrable 0 d)]
    congr 1
    · rw [← show (∫ u in (0:ℝ)..d, f (-u)) = ∫ u in (-d)..0, f u from
          by simpa only [neg_zero] using intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := d) f]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hd.le] at hu
      simp [QR,f,abs_of_nonneg hu.1]
    · apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hd.le] at hu
      simp [f,abs_of_nonneg hu.1]
  have H := (N.comp Real.tendsto_log_atTop).add (P.comp Real.tendsto_log_atTop)
  rw [hm] at H
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have ht : 0 < T := zero_lt_one.trans hT
  have hN : ⌊T^d⌋₊ = ⌊Real.exp (d*Real.log T)⌋₊ := by rw [Real.rpow_def_of_pos ht, mul_comm]
  unfold primeModel pairPulseIndex
  rw [Finset.product_eq_sprod, Finset.sum_product univ (Icc 2 _) (fun i : Bool × ℕ =>
    (pairedWeight i.2:ℂ)*Q (signedLog i.1 i.2/Real.log T)), hN]
  simp only [Function.comp_apply, Fintype.sum_bool, signedLog, Bool.false_eq_true, if_false, if_true, neg_div]
  rw [← add_div]
  congr 1
  have extend (f : ℕ → ℂ) (h1 : f 1 = 0) :
      (∑ n ∈ Icc 2 ⌊Real.exp (d*Real.log T)⌋₊, f n) =
        ∑ n ∈ Ioc 0 ⌊Real.exp (d*Real.log T)⌋₊, f n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [mem_Icc,mem_Ioc] at hn ⊢
      omega
    · intro n hn hnn
      have h := mem_Ioc.mp hn
      have he : n = 1 := by simp only [mem_Icc] at hnn; omega
      rw [he,h1]
  have e₁ := extend (fun n => (pairedWeight n:ℂ)*QR (Real.log n/Real.log T)) (by simp [pairedWeight])
  have e₂ := extend (fun n => (pairedWeight n:ℂ)*Q (Real.log n/Real.log T)) (by simp [pairedWeight])
  unfold QR at e₁ ⊢
  rw [e₁,e₂,add_comm]

theorem pairPrimeScaled_normalized_tendsto {a b Q : ℝ → ℂ}
    (ha : Continuous a) (hca : HasCompactSupport a)
    (hb : Continuous b) (hcb : HasCompactSupport b)
    (hQ : ContDiff ℝ 1 Q) (hcQ : HasCompactSupport Q) {d : ℝ} (hd : 0 < d) (hd1 : d < 1)
    (hs : ∀ u, d ≤ |u| → Q u = 0) :
    Tendsto (pairPrimeScaled a b Q d) atTop
      (𝓝 ((∫ u : ℝ, Q u*((|u|:ℝ):ℂ))*pairHeightMass a b)) := by
  have H := (pairPrimeScaled_sub_model_tendsto ha hca hb hcb hQ.continuous hcQ hd hd1).add
    ((primeModel_tendsto hQ hcQ hd hs).mul_const (pairHeightMass a b))
  simpa only [sub_add_cancel, zero_add] using H

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pairPrimeScaled_sub_model_tendsto
#print axioms XiPrime8845.RHTriple.pairPrimeScaled_normalized_tendsto
