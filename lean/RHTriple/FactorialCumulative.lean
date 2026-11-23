/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.FactorialDyadic
import Zeta23.Assembly

/-! Cumulative upper bounds for the third factorial count. The bounded
initial interval is paid once, after dyadic summation. -/

noncomputable section
open Filter Topology

namespace XiPrime8845.RHTriple
open Zeta23

theorem zetaNcount_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Zeta23.Ncount a c = Zeta23.Ncount a b + Zeta23.Ncount b c := by
  exact Assembly.N_add zetaZeroConfig hab hbc

theorem zetaNcount_dyadic_tendsto :
    Tendsto (fun T => (Zeta23.Ncount T (2*T):ℝ)) atTop atTop :=
  Assembly.tendsto_N_atTop zetaZeroConfig (RvM.riemannVonMangoldt gammaFacts)

theorem zetaNcount_cumulative_tendsto : Tendsto (fun T => (Zeta23.Ncount 0 T:ℝ)) atTop atTop := by
  have H := zetaNcount_dyadic_tendsto.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
  apply tendsto_atTop_mono' _ ?_ H
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  change (Zeta23.Ncount (T/2) (2*(T/2)):ℝ) ≤ (Zeta23.Ncount 0 T:ℝ)
  have hEq : Zeta23.Ncount 0 T = Zeta23.Ncount 0 (T/2)+Zeta23.Ncount (T/2) T :=
    zetaNcount_add (by linarith) (by linarith)
  rw [show 2*(T/2)=T by ring,hEq,
    Nat.cast_add]
  linarith [Nat.cast_nonneg (α := ℝ) (Zeta23.Ncount 0 (T/2))]

theorem cumulative_upper_of_dyadic {f g : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ {a b d}, a ≤ b → b ≤ d → f a d = f a b + f b d)
    (hg : ∀ {a b d}, a ≤ b → b ≤ d → g a d = g a b + g b d)
    (hfn : ∀ a b, 0 ≤ f a b) (hgn : ∀ a b, 0 ≤ g a b)
    (htop : Tendsto (fun T => g 0 T) atTop atTop)
    (h : UpperWithMargin (fun T => f T (2*T)) (fun T => g T (2*T)) c) :
    UpperWithMargin (f 0) (g 0) c := by
  intro e he
  obtain ⟨U,hU⟩ := eventually_atTop.mp (h (e/2) (by positivity))
  let A := max U 1
  have hA : 0 < A := one_pos.trans_le (le_max_right _ _)
  have hstep (t : ℝ) (ht : A ≤ t) : f t (2*t) ≤ (c+e/2)*g t (2*t) :=
    hU t ((le_max_left _ _).trans ht)
  have hb (n : ℕ) (t : ℝ) (ht : A ≤ t) : f t (2^n*t) ≤ (c+e/2)*g t (2^n*t) := by
    induction n with
    | zero =>
      have hf0 := hf (a := t) le_rfl le_rfl
      have hg0 := hg (a := t) le_rfl le_rfl
      simp only [pow_zero,one_mul]
      rw [show f t t=0 by linarith,show g t t=0 by linarith,mul_zero]
    | succ n ih =>
      have ht0 := hA.le.trans ht
      have h1 : t ≤ 2^n*t := by
        simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) ht0
      have h2 : (2^n:ℝ)*t ≤ 2^(n+1)*t := by
        calc
          _ ≤ 2*(2^n*t) := by nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) n) ht0]
          _ = _ := by rw [pow_succ]; ring
      have hs := hstep _ (ht.trans h1)
      rw [show 2*(2^n*t)=2^(n+1)*t by rw [pow_succ]; ring] at hs
      rw [hf h1 h2,hg h1 h2,mul_add]
      exact add_le_add ih hs
  filter_upwards [eventually_ge_atTop A, htop.eventually_ge_atTop (f 0 (2*A)/(e/2))]
    with T hT hTop
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near ((one_le_div hA).2 hT) (by norm_num : (1:ℝ)<2)
  let t := T/(2^n:ℝ)
  have hp : 0 < (2^n:ℝ) := by positivity
  have hAt : A ≤ t := (le_div_iff₀ hp).2 (by
    have H := (le_div_iff₀ hA).mp hlo
    linarith only [H])
  have htA : t ≤ 2*A := (div_le_iff₀ hp).2 (by
    have H := (div_lt_iff₀ hA).mp hhi
    rw [pow_succ] at H
    nlinarith only [H])
  have hEq : (2^n:ℝ)*t = T := by dsimp [t]; field_simp
  have ht0 := hA.le.trans hAt
  have htT : t ≤ T := by
    rw [← hEq]
    simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) ht0
  have hm := hb n t hAt
  rw [hEq] at hm
  have hfirst : f 0 t ≤ f 0 (2*A) := by rw [hf ht0 htA]; linarith [hfn t (2*A)]
  have hlast : g t T ≤ g 0 T := by rw [hg ht0 htT]; linarith [hgn 0 t]
  have hconst : f 0 (2*A) ≤ (e/2)*g 0 T := by
    simpa only [mul_comm] using (div_le_iff₀ (show 0<e/2 by positivity)).mp hTop
  rw [hf ht0 htT]
  calc
    _ ≤ f 0 (2*A) + (c+e/2)*g t T := add_le_add hfirst hm
    _ ≤ (e/2)*g 0 T + (c+e/2)*g 0 T :=
      add_le_add hconst (mul_le_mul_of_nonneg_left hlast (by positivity))
    _ = _ := by ring

theorem zetaM3_cumulative_upper {c : ℝ} (hc : 0 ≤ c) (h : DyadicM3Upper c) :
    UpperWithMargin (fun T => (zetaM3 0 T:ℝ)) (fun T => (Zeta23.Ncount 0 T:ℝ)) c := by
  apply cumulative_upper_of_dyadic (f := fun a b => (zetaM3 a b:ℝ))
    (g := fun a b => (Zeta23.Ncount a b:ℝ)) hc ?_ ?_
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _) zetaNcount_cumulative_tendsto h
  · intro a b d hab hbd
    exact_mod_cast zetaM3_add hab hbd
  · intro a b d hab hbd
    exact_mod_cast zetaNcount_add hab hbd

theorem limsup_countRatio_le {f N : ℝ → ℝ} {c : ℝ} (hf : ∀ T, 0 ≤ f T)
    (hN : Tendsto N atTop atTop) (h : UpperWithMargin f N c) :
    limsup (fun T => f T/N T) atTop ≤ c := by
  have H (e : ℝ) (he : 0 < e) : ∀ᶠ T in atTop, f T/N T ≤ c+e := by
    filter_upwards [h e he, hN.eventually_gt_atTop 0] with T hT hn
    exact (div_le_iff₀ hn).2 hT
  apply le_of_forall_pos_le_add
  intro e he
  apply limsup_le_of_le ?_ (H e he)
  apply isCoboundedUnder_le_of_eventually_le (x := 0) atTop
  filter_upwards [hN.eventually_gt_atTop 0] with T hT
  exact div_nonneg (hf T) hT.le

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.zetaM3_cumulative_upper
#print axioms XiPrime8845.RHTriple.limsup_countRatio_le
