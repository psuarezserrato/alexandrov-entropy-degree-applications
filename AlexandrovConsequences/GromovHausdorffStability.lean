import AlexandrovConsequences.Foundation

/-!
# Gromov–Hausdorff Volume and Entropy-Volume Stability

This file formalizes **Corollary 1.11** (`cor:gh-stability`) and **Corollary 1.12**
(`cor:gh-stability2`) of P. Suárez-Serrato, *"The entropy-degree theorem for Alexandrov spaces"*
(`arXiv:2606.30403`, §1.3 & §7.8–7.9), using Mathlib's `Filter.Tendsto` on `Filter.atTop`.

## Main Results
1. **Reviron Entropy Lower-Semicontinuity Product Lemma (`limit_entropy_pow_le_of_eventually_add_eps`)**:
   If $\mathrm{Vol}(M_i) \to V_X > 0$, $h(\widetilde{M}_i)^N \mathrm{Vol}(M_i) \to L$, and Reviron's
   entropy lower-semicontinuity $h(\widetilde{X}) \le \liminf_{i \to \infty} h(\widetilde{M}_i)$ holds
   (`∀ ε > 0, ∀ᶠ i in atTop, h_lim ≤ h_seq i + ε`), then
   $$h(\widetilde{X})^N \, V_X \le L.$$
2. **Corollary 1.11 (`cor:gh-stability`, `gh_hyperbolic_volume_stability`)**:
   If closed $N$-manifolds $(M_i)$ with $\mathrm{sec} \ge -1$ converge in Gromov–Hausdorff distance
   to $(X, \mathsf{d})$ with $\mathrm{Vol}(M_i) \to k\,\mathrm{Vol}(Y)$ ($k \ge 1$) and Perelman
   stability transfers $|\deg(f_i)| = [\pi_1(Y) : (f_i)_* \pi_1(M_i)] = k$ for large $i$, then
   $\mathrm{Vol}(X) = k\,\mathrm{Vol}(Y)$, $h(\widetilde{X}) = N - 1$, $\mathcal{S}_X = \emptyset$,
   and $X$ is isometric to a smooth hyperbolic degree-$k$ cover of $Y$ ($Y$ itself when $k = 1$).
3. **Corollary 1.12 (`cor:gh-stability2`, `gh_locally_symmetric_entropy_volume_stability`)**:
   For general rank-one locally symmetric targets $Y$ (including $\mathbb{O}\mathbf{H}^2$), if
   $h(\widetilde{M}_i)^N \mathrm{Vol}(M_i) \to k\,h(\widetilde{Y})^N \mathrm{Vol}(Y)$, Colding–Cheeger
   gives $\mathrm{Vol}(M_i) \to \mathrm{Vol}(X) > 0$, and Reviron's lower-semicontinuity holds, then
   $$h(\widetilde{X})^N \mathrm{Vol}(X) = k \, h(\widetilde{Y})^N \mathrm{Vol}(Y),$$
   forcing $\mathcal{S}_X = \emptyset$ and global homothety $(X, (h(\widetilde{X})/h(\widetilde{Y}))\mathsf{d}_X) \cong \widehat{Y}$.
-/

noncomputable section

open MeasureTheory Set Filter RCDEntropyDegree.MetricMeasure RCDEntropyDegree.RCD
open scoped Topology

namespace AlexandrovConsequences

section EntropyLowerSemicontinuityLimit

/-- **Reviron Entropy Lower-Semicontinuity Product Lemma (`[Reviron08]`)**:
Suppose a non-collapsed converging sequence satisfies:
1. volume convergence `Tendsto vol_seq atTop (nhds vol_lim)` with `0 < vol_lim`,
2. entropy-volume product convergence `Tendsto (fun i => (h_seq i) ^ N * vol_seq i) atTop (nhds L)`, and
3. Reviron's lower-semicontinuity `∀ ε > 0, ∀ᶠ i in atTop, h_lim ≤ h_seq i + ε` with `0 ≤ h_lim`
   and `∀ i, 0 ≤ h_seq i`.
Then the limit entropy-volume product satisfies
$$h_{\mathrm{lim}}^N \, \mathrm{vol}_{\mathrm{lim}} \le L.$$ -/
theorem limit_entropy_pow_le_of_eventually_add_eps
    {N : ℕ} {h_lim vol_lim L : ℝ}
    (hh_lim : 0 ≤ h_lim) (hvol_lim : 0 < vol_lim)
    (h_seq vol_seq : ℕ → ℝ)
    (hh_seq_nonneg : ∀ i, 0 ≤ h_seq i)
    (h_vol_tendsto : Tendsto vol_seq atTop (𝓝 vol_lim))
    (h_prod_tendsto : Tendsto (fun i => (h_seq i) ^ N * vol_seq i) atTop (𝓝 L))
    (h_reviron_lsc : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, h_lim ≤ h_seq i + ε) :
    h_lim ^ N * vol_lim ≤ L := by
  have h_quot_tendsto : Tendsto (fun i => (h_seq i) ^ N) atTop (𝓝 (L / vol_lim)) := by
    have h_div : Tendsto (fun i => ((h_seq i) ^ N * vol_seq i) / vol_seq i)
        atTop (𝓝 (L / vol_lim)) :=
      h_prod_tendsto.div h_vol_tendsto hvol_lim.ne'
    have h_ev_vol_pos : ∀ᶠ i in atTop, vol_seq i ≠ 0 := by
      filter_upwards [h_vol_tendsto.eventually (Ioi_mem_nhds hvol_lim)] with i hi
      exact ne_of_gt hi
    refine h_div.congr' ?_
    filter_upwards [h_ev_vol_pos] with i hne
    exact mul_div_cancel_right₀ ((h_seq i) ^ N) hne
  have h_pow_le_div : ∀ ε : ℝ, 0 < ε → (max (h_lim - ε) 0) ^ N ≤ L / vol_lim := by
    intro ε hε
    have h_ev_pow : ∀ᶠ i in atTop, (max (h_lim - ε) 0) ^ N ≤ (h_seq i) ^ N := by
      filter_upwards [h_reviron_lsc ε hε] with i hi
      have h_base : max (h_lim - ε) 0 ≤ h_seq i :=
        max_le (by linarith) (hh_seq_nonneg i)
      exact pow_le_pow_left₀ (le_max_right _ _) h_base N
    exact ge_of_tendsto h_quot_tendsto h_ev_pow
  have h_cont : Continuous (fun ε : ℝ => (max (h_lim - ε) 0) ^ N) :=
    ((continuous_const.sub continuous_id).max continuous_const).pow N
  have h_lim_tendsto :
      Tendsto (fun ε : ℝ => (max (h_lim - ε) 0) ^ N) (𝓝[>] 0) (𝓝 (h_lim ^ N)) := by
    have h0 : (max (h_lim - 0) 0) ^ N = h_lim ^ N := by
      rw [sub_zero, max_eq_left hh_lim]
    rw [← h0]
    exact h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_le_div : h_lim ^ N ≤ L / vol_lim :=
    le_of_tendsto h_lim_tendsto (eventually_nhdsWithin_iff.mpr (Eventually.of_forall h_pow_le_div))
  exact (le_div_iff₀ hvol_lim).mp h_le_div

end EntropyLowerSemicontinuityLimit

section GromovHausdorffStabilityTheorems

/-- **Corollary 1.11 (`cor:gh-stability`, Gromov–Hausdorff Volume Stability)**:
Let $(M_i)$ be closed oriented Riemannian $N$-manifolds ($N \ge 3$) with $\mathrm{sec}(M_i) \ge -1$
converging in Gromov–Hausdorff distance to a non-collapsed Alexandrov space $(X, \mathsf{d})$
($0 < \mathrm{Vol}(X)$, $0 \le h(\widetilde{X}) \le N - 1$) such that $\mathrm{Vol}(M_i) \to k\,\mathrm{Vol}(Y)$
($k \ge 1$) and Perelman stability gives maps $f_i : M_i \to Y$ with
$|\deg(f_i)| = [\pi_1(Y) : (f_i)_* \pi_1(M_i)] = k$ eventually homotopic through homeomorphisms
$\phi_i : X \xrightarrow{\sim} M_i$ to $f : X \to Y$.
Then $\mathrm{Vol}(X) = k\,\mathrm{Vol}(Y)$, $h(\widetilde{X}) = N - 1$, $\mathcal{S}_X = \emptyset$,
and $(X, \mathsf{d})$ is globally isometric onto the degree-$k$ hyperbolic cover $\widehat{Y}$
($Y$ itself when $k = 1$). -/
theorem gh_hyperbolic_volume_stability
    {X Yhat : Type*} [MetricSpace X] [MetricSpace Yhat]
    {N k : ℕ} (hN : 3 ≤ N) (hk : 1 ≤ k)
    {S_X : Set X} {Fhat_inf : X → Yhat}
    {h_Xtilde vol_X vol_Y : ℝ}
    (hh_nonneg : 0 ≤ h_Xtilde) (hh_le : h_Xtilde ≤ (N - 1 : ℝ))
    (hvol_X_pos : 0 < vol_X) (_hvol_Y_pos : 0 < vol_Y)
    (vol_M : ℕ → ℝ) (deg_seq : ℕ → ℤ) (index_seq : ℕ → ℕ)
    {deg_X : ℤ} {index_X : ℕ}
    (h_colding_cheeger : Tendsto vol_M atTop (𝓝 vol_X))
    (h_asymptotic_vol : Tendsto vol_M atTop (𝓝 ((k : ℝ) * vol_Y)))
    (h_perelman :
      ∀ᶠ i in atTop,
        |(deg_seq i : ℝ)| = (k : ℝ) ∧ index_seq i = k ∧
          deg_X = deg_seq i ∧ index_X = index_seq i)
    (h_th1_ineq : |(deg_X : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y ≤ h_Xtilde ^ N * vol_X)
    (h_th1_rigidity :
      h_Xtilde ^ N * vol_X = |(deg_X : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y →
      1 ≤ index_X →
      |(deg_X : ℝ)| = (index_X : ℝ) →
      S_X = ∅ ∧
      Function.Surjective Fhat_inf ∧
      (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xtilde / (N - 1 : ℝ)) * dist x₁ x₂)) :
    vol_X = (k : ℝ) * vol_Y ∧
    |(deg_X : ℝ)| = (k : ℝ) ∧
    index_X = k ∧
    h_Xtilde = (N - 1 : ℝ) ∧
    h_Xtilde ^ N * vol_X = (k : ℝ) * (N - 1 : ℝ) ^ N * vol_Y ∧
    S_X = ∅ ∧
    Function.Surjective Fhat_inf ∧
    (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = dist x₁ x₂) := by
  have hvol_eq : vol_X = (k : ℝ) * vol_Y :=
    tendsto_nhds_unique h_colding_cheeger h_asymptotic_vol
  obtain ⟨i₀, hi₀_deg, hi₀_idx, hdeg_eq, hidx_eq⟩ := h_perelman.exists
  have hdeg_X : |(deg_X : ℝ)| = (k : ℝ) := by rw [hdeg_eq, hi₀_deg]
  have hidx_X : index_X = k := by rw [hidx_eq, hi₀_idx]
  have hidx_pos : 1 ≤ index_X := by rw [hidx_X]; exact hk
  have hidx_deg_eq : |(deg_X : ℝ)| = (index_X : ℝ) := by rw [hdeg_X, hidx_X]
  have hh0_pos : (0 : ℝ) < (N - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN_ne0 : N ≠ 0 := by omega
  have hpow_lower : (N - 1 : ℝ) ^ N * vol_X ≤ h_Xtilde ^ N * vol_X := by
    calc
      (N - 1 : ℝ) ^ N * vol_X
        = (N - 1 : ℝ) ^ N * ((k : ℝ) * vol_Y) := by rw [hvol_eq]
      _ = |(deg_X : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y := by rw [hdeg_X]; ring
      _ ≤ h_Xtilde ^ N * vol_X := h_th1_ineq
  have hpow_le : h_Xtilde ^ N ≤ (N - 1 : ℝ) ^ N :=
    pow_le_pow_left₀ hh_nonneg hh_le N
  have hpow_ge : (N - 1 : ℝ) ^ N ≤ h_Xtilde ^ N :=
    le_of_mul_le_mul_right hpow_lower hvol_X_pos
  have hh_X_eq : h_Xtilde = (N - 1 : ℝ) :=
    (pow_left_inj₀ hh_nonneg hh0_pos.le hN_ne0).mp (le_antisymm hpow_le hpow_ge)
  have hent_eq_k : h_Xtilde ^ N * vol_X = (k : ℝ) * (N - 1 : ℝ) ^ N * vol_Y := by
    rw [hh_X_eq, hvol_eq]
    ring
  have hent_eq_deg : h_Xtilde ^ N * vol_X = |(deg_X : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y := by
    rw [hdeg_X]
    exact hent_eq_k
  obtain ⟨hS_empty, h_surj, h_isom_c⟩ := h_th1_rigidity hent_eq_deg hidx_pos hidx_deg_eq
  have hc1 : h_Xtilde / (N - 1 : ℝ) = 1 := by rw [hh_X_eq, div_self hh0_pos.ne']
  have h_isom : ∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = dist x₁ x₂ := by
    intro x₁ x₂
    have h := h_isom_c x₁ x₂
    rwa [hc1, one_mul] at h
  exact ⟨hvol_eq, hdeg_X, hidx_X, hh_X_eq, hent_eq_k, hS_empty, h_surj, h_isom⟩

/-- **Corollary 1.12 (`cor:gh-stability2`, Locally Symmetric GH Entropy-Volume Stability)**:
Let $Y$ be any closed orientable negatively curved locally symmetric $N$-manifold ($N \ge 3$,
including $\mathbb{O}\mathbf{H}^2$), and suppose non-collapsed $N$-manifolds $(M_i)$ with
lower curvature bound $\mathrm{sec} \ge -1$ converge in Gromov–Hausdorff distance to $(X, \mathsf{d})$
with $\mathrm{Vol}(M_i) \to \mathrm{Vol}(X) > 0$,
$$h(\widetilde{M}_i)^N \mathrm{Vol}(M_i) \to k \, h(\widetilde{Y})^N \mathrm{Vol}(Y) \quad (k \ge 1),$$
Reviron's entropy lower-semicontinuity $h(\widetilde{X}) \le \liminf_i h(\widetilde{M}_i)$,
and Perelman stability transferring $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)] = k$.
Then:
1. $h(\widetilde{X})^N \mathrm{Vol}(X) = k \, h(\widetilde{Y})^N \mathrm{Vol}(Y)$ and $h(\widetilde{X}) > 0$,
2. $\mathcal{S}_X = \emptyset$ ($X$ is smooth), and
3. after rescaling $\mathsf{d}_X$ by $c = h(\widetilde{X}) / h(\widetilde{Y}) > 0$, $(X, c\,\mathsf{d}_X)$
   is globally isometric to the smooth degree-$k$ cover $\widehat{Y} \to Y$. -/
theorem gh_locally_symmetric_entropy_volume_stability
    {X Yhat : Type*} [MetricSpace X] [MetricSpace Yhat]
    {N k : ℕ} (hN : 3 ≤ N) (hk : 1 ≤ k)
    {S_X : Set X} {Fhat_inf : X → Yhat}
    {h_Xtilde h_Ytilde vol_X vol_Y : ℝ}
    (hh_X_nonneg : 0 ≤ h_Xtilde) (hh_Y_pos : 0 < h_Ytilde)
    (hvol_X_pos : 0 < vol_X) (hvol_Y_pos : 0 < vol_Y)
    (h_M vol_M : ℕ → ℝ) (deg_seq : ℕ → ℤ) (index_seq : ℕ → ℕ)
    {deg_X : ℤ} {index_X : ℕ}
    (hh_M_nonneg : ∀ i, 0 ≤ h_M i)
    (h_colding_cheeger : Tendsto vol_M atTop (𝓝 vol_X))
    (h_prod_tendsto :
      Tendsto (fun i => (h_M i) ^ N * vol_M i) atTop (𝓝 ((k : ℝ) * h_Ytilde ^ N * vol_Y)))
    (h_reviron_lsc : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, h_Xtilde ≤ h_M i + ε)
    (h_perelman :
      ∀ᶠ i in atTop,
        |(deg_seq i : ℝ)| = (k : ℝ) ∧ index_seq i = k ∧
          deg_X = deg_seq i ∧ index_X = index_seq i)
    (h_th1_ineq : |(deg_X : ℝ)| * h_Ytilde ^ N * vol_Y ≤ h_Xtilde ^ N * vol_X)
    (h_th1_rigidity :
      h_Xtilde ^ N * vol_X = |(deg_X : ℝ)| * h_Ytilde ^ N * vol_Y →
      0 < h_Xtilde →
      1 ≤ index_X →
      |(deg_X : ℝ)| = (index_X : ℝ) →
      S_X = ∅ ∧
      Function.Surjective Fhat_inf ∧
      (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xtilde / h_Ytilde) * dist x₁ x₂)) :
    let c := h_Xtilde / h_Ytilde
    h_Xtilde ^ N * vol_X = (k : ℝ) * h_Ytilde ^ N * vol_Y ∧
    0 < h_Xtilde ∧
    0 < c ∧
    |(deg_X : ℝ)| = (k : ℝ) ∧
    index_X = k ∧
    S_X = ∅ ∧
    Function.Surjective Fhat_inf ∧
    (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = c * dist x₁ x₂) := by
  intro c
  obtain ⟨i₀, hi₀_deg, hi₀_idx, hdeg_eq, hidx_eq⟩ := h_perelman.exists
  have hdeg_X : |(deg_X : ℝ)| = (k : ℝ) := by rw [hdeg_eq, hi₀_deg]
  have hidx_X : index_X = k := by rw [hidx_eq, hi₀_idx]
  have hidx_pos : 1 ≤ index_X := by rw [hidx_X]; exact hk
  have hidx_deg_eq : |(deg_X : ℝ)| = (index_X : ℝ) := by rw [hdeg_X, hidx_X]
  have h_upper : h_Xtilde ^ N * vol_X ≤ (k : ℝ) * h_Ytilde ^ N * vol_Y :=
    limit_entropy_pow_le_of_eventually_add_eps hh_X_nonneg hvol_X_pos h_M vol_M
      hh_M_nonneg h_colding_cheeger h_prod_tendsto h_reviron_lsc
  have h_lower : (k : ℝ) * h_Ytilde ^ N * vol_Y ≤ h_Xtilde ^ N * vol_X := by
    rw [← hdeg_X]
    exact h_th1_ineq
  have hent_eq_k : h_Xtilde ^ N * vol_X = (k : ℝ) * h_Ytilde ^ N * vol_Y :=
    le_antisymm h_upper h_lower
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h_rhs_pos : 0 < (k : ℝ) * h_Ytilde ^ N * vol_Y :=
    mul_pos (mul_pos hk_pos (pow_pos hh_Y_pos N)) hvol_Y_pos
  have hh_X_pow_pos : 0 < h_Xtilde ^ N := by
    have hprod_pos : 0 < h_Xtilde ^ N * vol_X := by linarith
    exact (mul_pos_iff_of_pos_right hvol_X_pos).mp hprod_pos
  have hh_X_pos : 0 < h_Xtilde := by
    refine lt_of_le_of_ne hh_X_nonneg ?_
    intro h0
    have hN0 : N ≠ 0 := by omega
    rw [← h0, zero_pow hN0] at hh_X_pow_pos
    exact lt_irrefl 0 hh_X_pow_pos
  have hc_pos : 0 < c := div_pos hh_X_pos hh_Y_pos
  have hent_eq_deg : h_Xtilde ^ N * vol_X = |(deg_X : ℝ)| * h_Ytilde ^ N * vol_Y := by
    rw [hdeg_X]
    exact hent_eq_k
  obtain ⟨hS_empty, h_surj, h_isom⟩ :=
    h_th1_rigidity hent_eq_deg hh_X_pos hidx_pos hidx_deg_eq
  exact ⟨hent_eq_k, hh_X_pos, hc_pos, hdeg_X, hidx_X, hS_empty, h_surj, h_isom⟩

end GromovHausdorffStabilityTheorems

end AlexandrovConsequences
