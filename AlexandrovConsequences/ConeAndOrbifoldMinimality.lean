import AlexandrovConsequences.Foundation

/-!
# Simplicial Volume of Cone-Manifolds, Global Cone-Metric Minimality & Orbifold Minimality

This file formalizes **Corollaries 1.13, 1.14, and 1.15** of
P. Suárez-Serrato, *"The entropy-degree theorem for Alexandrov spaces"* (`arXiv:2606.30403`,
§1.4 & §7.10–7.12).

## Main Results
1. **Corollary 1.13 (`cor:cone-simplicial-volume`)**:
   - `alexandrov_simplicial_volume_bound`: $\mathcal{H}^N(X) \ge |\deg(f)| \, v_N \|Y\|$.
   - `alexandrov_homotopy_simplicial_rigidity`: For a homotopy equivalence ($|\deg(f)| = 1$,
     $[\pi_1(Y) : f_* \pi_1(X)] = 1$, $\|X\| = \|Y\|$), $\mathcal{H}^N(X) \ge v_N \|X\|$, with equality
     forcing $h(\overline{X}) = N - 1$, $\mathcal{S}_X = \emptyset$, and global isometry $X \cong Y$.
   - `hyperbolic_cone_manifold_strict_simplicial_bound`: When $\mathcal{S}_X \neq \emptyset$
     (e.g., hyperbolic cone-manifold with some cone angle $\alpha_i < 2\pi$), strict inequality
     $\mathcal{H}^N(X) > v_N \|X\|$ holds.
2. **Corollary 1.14 (`cor:cone-manifold-volume`, `hyperbolic_cone_metric_strict_volume_minimality`)**:
   - For any closed hyperbolic $N$-manifold $(M, g_{\mathrm{hyp}})$ ($N \ge 3$) and any hyperbolic
     cone-metric $g_{\mathrm{cone}}$ on $M$ with all cone angles $\le 2\pi$ and $\mathcal{S}_X \neq \emptyset$,
     applying Corollary 1.13 to $\mathrm{id}_M : (M, g_{\mathrm{cone}}) \to (M, g_{\mathrm{hyp}})$ gives
     the global, path-independent volume minimum:
     $$\mathcal{H}^N(M, g_{\mathrm{cone}}) > \mathrm{Vol}(M, g_{\mathrm{hyp}}).$$
3. **Corollary 1.15 (`cor:orbifold-volume-minimality`, Selberg Finite Cover Cone-Angle Unwrapping)**:
   - `unwrapped_cone_angle_le_two_pi_iff`, `unwrapped_cone_angle_lt_two_pi_iff`:
     In a regular Selberg finite manifold cover $p : M \to \mathcal{O}$ of degree $d \ge 1$ with
     isotropy orders $m_i \ge 1$, cone angle $\alpha_i \le 2\pi / m_i$ unwraps to lifted cone angle
     $m_i \alpha_i \le 2\pi$ (and $\alpha_i < 2\pi / m_i \iff m_i \alpha_i < 2\pi$).
   - `orbifold_cone_metric_volume_minimality`: $\mathcal{H}^N(|\mathcal{O}|, g_{\mathrm{cone}}) \ge \mathrm{Vol}(\mathcal{O}, g_{\mathrm{sym}})$.
   - `orbifold_cone_metric_strict_volume_minimality`: If $\exists i, \alpha_i < 2\pi / m_i$, then
     $$\mathcal{H}^N(|\mathcal{O}|, g_{\mathrm{cone}}) > \mathrm{Vol}(\mathcal{O}, g_{\mathrm{sym}}).$$
-/

noncomputable section

open MeasureTheory Set Filter RCDEntropyDegree.MetricMeasure RCDEntropyDegree.RCD

namespace AlexandrovConsequences

section SimplicialVolumeConeManifolds

/-- **Corollary 1.13 Part 1 (`cor:cone-simplicial-volume`, Simplicial Volume Bound via $v_N$)**:
Let $X$ be a closed orientable $N$-dimensional Alexandrov space without boundary ($N \ge 3$,
$0 \le h(\overline{X}) \le N - 1$) and $f : X \to Y$ a continuous map to a closed orientable
hyperbolic $N$-manifold ($\mathrm{Vol}(Y) = v_N \|Y\|$). Then
$$|\deg(f)| \, v_N \|Y\| \le \mathcal{H}^N(X).$$ -/
theorem alexandrov_simplicial_volume_bound
    {N : ℕ} (hN : 3 ≤ N) {deg_f : ℤ} {h_Xbar vol_X vol_Y v_N simpl_Y : ℝ}
    (hh_nonneg : 0 ≤ h_Xbar) (hh_le : h_Xbar ≤ (N - 1 : ℝ))
    (hvol_X : 0 ≤ vol_X)
    (h_gromov_prop : vol_Y = v_N * simpl_Y)
    (h_ineq : |(deg_f : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y ≤ h_Xbar ^ N * vol_X) :
    |(deg_f : ℝ)| * v_N * simpl_Y ≤ vol_X := by
  have hh0_pos : (0 : ℝ) < (N - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hvol := same_entropy_volume_degree_bound hh0_pos hh_nonneg hh_le hvol_X h_ineq
  rw [h_gromov_prop] at hvol
  linarith

/-- **Corollary 1.13 Part 2 (`cor:cone-simplicial-volume`, Homotopy-Equivalence Rigidity)**:
When $f : X \to Y$ is a homotopy equivalence ($|\deg(f)| = 1 = [\pi_1(Y) : f_* \pi_1(X)]$ and
$\|X\| = \|Y\|$), $\mathcal{H}^N(X) \ge v_N \|X\|$, and equality $\mathcal{H}^N(X) = v_N \|X\|$
forces $h(\overline{X}) = N - 1$, $\mathcal{S}_X = \emptyset$, and global isometry $X \cong Y$. -/
theorem alexandrov_homotopy_simplicial_rigidity
    {X Yhat : Type*} [MetricSpace X] [MetricSpace Yhat]
    {N : ℕ} (hN : 3 ≤ N)
    {S_X : Set X} {Fhat_inf : X → Yhat}
    {h_Xbar vol_X vol_Y v_N simpl_X simpl_Y : ℝ}
    (hh_nonneg : 0 ≤ h_Xbar) (hh_le : h_Xbar ≤ (N - 1 : ℝ))
    (hvol_X_pos : 0 < vol_X)
    (h_gromov_prop : vol_Y = v_N * simpl_Y)
    (h_homotopy_simpl : simpl_X = simpl_Y)
    (h_ineq : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y ≤ h_Xbar ^ N * vol_X)
    (h_th1_rigidity :
      h_Xbar ^ N * vol_X = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y →
      S_X = ∅ ∧
      Function.Surjective Fhat_inf ∧
      (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xbar / (N - 1 : ℝ)) * dist x₁ x₂)) :
    v_N * simpl_X ≤ vol_X ∧
      (vol_X = v_N * simpl_X →
        h_Xbar = (N - 1 : ℝ) ∧
        S_X = ∅ ∧
        Function.Surjective Fhat_inf ∧
        (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = dist x₁ x₂)) := by
  have hbound : v_N * simpl_X ≤ vol_X := by
    have h1 := alexandrov_simplicial_volume_bound hN hh_nonneg hh_le hvol_X_pos.le h_gromov_prop h_ineq
    rw [h_homotopy_simpl]
    simpa using h1
  refine ⟨hbound, ?_⟩
  intro hvol_eq
  have hh0_pos : (0 : ℝ) < (N - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN_ne0 : N ≠ 0 := by omega
  have hvol_XY : vol_X = vol_Y := by rw [hvol_eq, h_gromov_prop, h_homotopy_simpl]
  have hpow_lower : (N - 1 : ℝ) ^ N * vol_X ≤ h_Xbar ^ N * vol_X := by
    calc
      (N - 1 : ℝ) ^ N * vol_X
        = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y := by rw [hvol_XY]; norm_num
      _ ≤ h_Xbar ^ N * vol_X := h_ineq
  have hpow_le : h_Xbar ^ N ≤ (N - 1 : ℝ) ^ N := pow_le_pow_left₀ hh_nonneg hh_le N
  have hpow_ge : (N - 1 : ℝ) ^ N ≤ h_Xbar ^ N := le_of_mul_le_mul_right hpow_lower hvol_X_pos
  have hh_eq : h_Xbar = (N - 1 : ℝ) :=
    (pow_left_inj₀ hh_nonneg hh0_pos.le hN_ne0).mp (le_antisymm hpow_le hpow_ge)
  have hent_eq : h_Xbar ^ N * vol_X = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y := by
    rw [hh_eq, hvol_XY]
    norm_num
  obtain ⟨hS, hsurj, hisom⟩ := h_th1_rigidity hent_eq
  have hc1 : h_Xbar / (N - 1 : ℝ) = 1 := by rw [hh_eq, div_self hh0_pos.ne']
  refine ⟨hh_eq, hS, hsurj, ?_⟩
  intro x₁ x₂
  have h := hisom x₁ x₂
  rwa [hc1, one_mul] at h

/-- **Corollary 1.13 Part 3 (`cor:cone-simplicial-volume`, Strict Bound for Singular Cone-Manifolds)**:
If $X$ is homotopy equivalent to $Y$ ($0 \le h(\overline{X}) \le N - 1$) and has nonempty singular set
$\mathcal{S}_X \neq \emptyset$ (for instance a hyperbolic cone-manifold with some cone angle
$\alpha_i < 2\pi$), then
$$v_N \|X\| < \mathcal{H}^N(X).$$ -/
theorem hyperbolic_cone_manifold_strict_simplicial_bound
    {X : Type*} {N : ℕ} (hN : 3 ≤ N) {S_X : Set X}
    {h_Xbar vol_X vol_Y v_N simpl_X simpl_Y : ℝ}
    (hh_nonneg : 0 ≤ h_Xbar) (hh_le : h_Xbar ≤ (N - 1 : ℝ))
    (hvol_X : 0 ≤ vol_X)
    (hS_ne : S_X.Nonempty)
    (h_gromov_prop : vol_Y = v_N * simpl_Y)
    (h_homotopy_simpl : simpl_X = simpl_Y)
    (h_ineq : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y ≤ h_Xbar ^ N * vol_X)
    (h_rigidity : h_Xbar ^ N * vol_X = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_Y → S_X = ∅) :
    v_N * simpl_X < vol_X := by
  have hh0_pos : (0 : ℝ) < (N - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have h_strict := strict_entropy_volume_of_singularSet_nonempty
    h_ineq hS_ne (le_refl 1) (by norm_num) h_rigidity
  have h_vol : |((1 : ℤ) : ℝ)| * vol_Y < vol_X :=
    same_entropy_strict_volume_degree_bound hh0_pos hh_nonneg hh_le hvol_X h_strict
  rw [h_gromov_prop, ← h_homotopy_simpl] at h_vol
  simpa using h_vol

end SimplicialVolumeConeManifolds

section ConeMetricAndOrbifoldMinimality

/-- **Corollary 1.14 (`cor:cone-manifold-volume`, Global Volume Minimality for Cone-Metrics)**:
Let $(M, g_{\mathrm{hyp}})$ be a closed oriented hyperbolic $N$-manifold ($N \ge 3$), and let
$g_{\mathrm{cone}}$ be any hyperbolic cone-metric on $M$ whose cone angles satisfy $\alpha_i \le 2\pi$
(hence $\mathrm{curv} \ge -1$ and $h(M, g_{\mathrm{cone}}) \le N - 1$) and whose singular locus is
nonempty ($\mathcal{S}_{\mathrm{cone}} \neq \emptyset$). Applying Corollary 1.13 to $\mathrm{id}_M$
yields the global, path-independent strict volume minimum:
$$\mathrm{Vol}(M, g_{\mathrm{hyp}}) < \mathcal{H}^N(M, g_{\mathrm{cone}}).$$ -/
theorem hyperbolic_cone_metric_strict_volume_minimality
    {X : Type*} {N : ℕ} (hN : 3 ≤ N) {S_cone : Set X}
    {h_cone vol_cone vol_hyp v_N simpl_M : ℝ}
    (hh_nonneg : 0 ≤ h_cone) (hh_le : h_cone ≤ (N - 1 : ℝ))
    (hvol_cone : 0 ≤ vol_cone)
    (hS_ne : S_cone.Nonempty)
    (h_gromov_prop : vol_hyp = v_N * simpl_M)
    (h_ineq : |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_hyp ≤ h_cone ^ N * vol_cone)
    (h_rigidity : h_cone ^ N * vol_cone = |((1 : ℤ) : ℝ)| * (N - 1 : ℝ) ^ N * vol_hyp → S_cone = ∅) :
    vol_hyp < vol_cone := by
  have h := hyperbolic_cone_manifold_strict_simplicial_bound hN hh_nonneg hh_le hvol_cone hS_ne
    h_gromov_prop rfl h_ineq h_rigidity
  rwa [← h_gromov_prop] at h

/-- **Selberg Cover Cone-Angle Unwrapping (Non-Strict)**:
Along a regular finite manifold cover $p : M \to \mathcal{O}$ of degree $d \ge 1$ with local
isotropy orders $m_i \ge 1$, the lifted cone angle satisfies $m_i \alpha_i \le 2\pi$ if and only
if $\alpha_i \le 2\pi / m_i$. -/
theorem unwrapped_cone_angle_le_two_pi_iff
    {m : ℕ} (hm : 1 ≤ m) {α : ℝ} :
    (m : ℝ) * α ≤ 2 * Real.pi ↔ α ≤ 2 * Real.pi / (m : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact (le_div_iff₀' hm_pos).symm

/-- **Selberg Cover Cone-Angle Unwrapping (Strict)**:
Along a regular finite manifold cover $p : M \to \mathcal{O}$ with local isotropy orders $m_i \ge 1$,
the lifted cone angle satisfies $m_i \alpha_i < 2\pi$ if and only if $\alpha_i < 2\pi / m_i$. -/
theorem unwrapped_cone_angle_lt_two_pi_iff
    {m : ℕ} (hm : 1 ≤ m) {α : ℝ} :
    (m : ℝ) * α < 2 * Real.pi ↔ α < 2 * Real.pi / (m : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact (lt_div_iff₀' hm_pos).symm

/-- **Corollary 1.15 Part 1 (`cor:orbifold-volume-minimality`, Orbifold Cone-Metric Minimality)**:
Let $\mathcal{O}$ be a compact orientable hyperbolic or negatively curved locally symmetric
$N$-orbifold ($N \ge 3$) with isotropy orders $m_i \ge 1$, and let $g_{\mathrm{cone}}$ be a
singular cone-metric on $|\mathcal{O}|$ satisfying $K_{\mathrm{reg}} \ge -\kappa_0^2$ and
$\alpha_i \le 2\pi / m_i$ along all singular strata. Passing to a torsion-free Selberg finite
manifold cover $p : M \to \mathcal{O}$ of degree $d \ge 1$ unwraps every lifted cone angle to
$m_i \alpha_i \le 2\pi$ (hence $0 \le h(\widetilde{M}, \hat{g}_{\mathrm{cone}}) \le h(\widetilde{\mathcal{O}}, g_{\mathrm{sym}})$),
so Theorem 1.1 applied to $\mathrm{id}_M$ and cancellation of $d \ge 1$ yield
$$\mathrm{Vol}(\mathcal{O}, g_{\mathrm{sym}}) \le \mathcal{H}^N(|\mathcal{O}|, g_{\mathrm{cone}}).$$ -/
theorem orbifold_cone_metric_volume_minimality
    {ι : Type*} {N d : ℕ} (_hN : 3 ≤ N) (hd : 1 ≤ d)
    (m : ι → ℕ) (α : ι → ℝ)
    (hm : ∀ i, 1 ≤ m i)
    (h_angle_le : ∀ i, α i ≤ 2 * Real.pi / (m i : ℝ))
    {h_M_cone h_sym vol_O_cone vol_O_sym vol_M_cone vol_M_sym : ℝ}
    (h_unwrap_entropy :
      (∀ i, (m i : ℝ) * α i ≤ 2 * Real.pi) → 0 ≤ h_M_cone ∧ h_M_cone ≤ h_sym)
    (hh_sym_pos : 0 < h_sym)
    (hvol_M_cone_nonneg : 0 ≤ vol_M_cone)
    (h_cover_cone : vol_M_cone = (d : ℝ) * vol_O_cone)
    (h_cover_sym : vol_M_sym = (d : ℝ) * vol_O_sym)
    (h_ineq_cover : |((1 : ℤ) : ℝ)| * h_sym ^ N * vol_M_sym ≤ h_M_cone ^ N * vol_M_cone) :
    vol_O_sym ≤ vol_O_cone := by
  have h_lifted_le : ∀ i, (m i : ℝ) * α i ≤ 2 * Real.pi := fun i =>
    (unwrapped_cone_angle_le_two_pi_iff (hm i)).mpr (h_angle_le i)
  obtain ⟨hh_nonneg, hh_le⟩ := h_unwrap_entropy h_lifted_le
  have h_cover_vol : |((1 : ℤ) : ℝ)| * vol_M_sym ≤ vol_M_cone :=
    same_entropy_volume_degree_bound hh_sym_pos hh_nonneg hh_le hvol_M_cone_nonneg h_ineq_cover
  have h_M : vol_M_sym ≤ vol_M_cone := by simpa using h_cover_vol
  rw [h_cover_sym, h_cover_cone] at h_M
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact le_of_mul_le_mul_left h_M hd_pos

/-- **Corollary 1.15 Part 2 (`cor:orbifold-volume-minimality`, Strict Orbifold Minimality)**:
If additionally some stratum has genuine cone defect $\alpha_i < 2\pi / m_i$ (forcing unwrapped
cone angle $m_i \alpha_i < 2\pi$ and hence $\mathcal{S}_{M, \hat{g}_{\mathrm{cone}}} \neq \emptyset$
on the Selberg cover $M$), Theorem 1.1 forbids equality on $M$, so dividing by $d \ge 1$ gives
$$\mathrm{Vol}(\mathcal{O}, g_{\mathrm{sym}}) < \mathcal{H}^N(|\mathcal{O}|, g_{\mathrm{cone}}).$$ -/
theorem orbifold_cone_metric_strict_volume_minimality
    {ι M : Type*} {N d : ℕ} (_hN : 3 ≤ N) (hd : 1 ≤ d)
    (m : ι → ℕ) (α : ι → ℝ)
    (hm : ∀ i, 1 ≤ m i)
    (h_angle_le : ∀ i, α i ≤ 2 * Real.pi / (m i : ℝ))
    (h_angle_strict : ∃ i, α i < 2 * Real.pi / (m i : ℝ))
    {S_M_cone : Set M}
    {h_M_cone h_sym vol_O_cone vol_O_sym vol_M_cone vol_M_sym : ℝ}
    (h_unwrap_entropy :
      (∀ i, (m i : ℝ) * α i ≤ 2 * Real.pi) → 0 ≤ h_M_cone ∧ h_M_cone ≤ h_sym)
    (h_unwrap_singular :
      (∃ i, (m i : ℝ) * α i < 2 * Real.pi) → S_M_cone.Nonempty)
    (hh_sym_pos : 0 < h_sym)
    (hvol_M_cone_nonneg : 0 ≤ vol_M_cone)
    (h_cover_cone : vol_M_cone = (d : ℝ) * vol_O_cone)
    (h_cover_sym : vol_M_sym = (d : ℝ) * vol_O_sym)
    (h_ineq_cover : |((1 : ℤ) : ℝ)| * h_sym ^ N * vol_M_sym ≤ h_M_cone ^ N * vol_M_cone)
    (h_rigidity_cover :
      h_M_cone ^ N * vol_M_cone = |((1 : ℤ) : ℝ)| * h_sym ^ N * vol_M_sym → S_M_cone = ∅) :
    vol_O_sym < vol_O_cone := by
  have h_lifted_le : ∀ i, (m i : ℝ) * α i ≤ 2 * Real.pi := fun i =>
    (unwrapped_cone_angle_le_two_pi_iff (hm i)).mpr (h_angle_le i)
  have h_lifted_strict : ∃ i, (m i : ℝ) * α i < 2 * Real.pi := by
    obtain ⟨i, hi⟩ := h_angle_strict
    exact ⟨i, (unwrapped_cone_angle_lt_two_pi_iff (hm i)).mpr hi⟩
  obtain ⟨hh_nonneg, hh_le⟩ := h_unwrap_entropy h_lifted_le
  have hS_ne : S_M_cone.Nonempty := h_unwrap_singular h_lifted_strict
  have h_strict_ent : |((1 : ℤ) : ℝ)| * h_sym ^ N * vol_M_sym < h_M_cone ^ N * vol_M_cone :=
    strict_entropy_volume_of_singularSet_nonempty h_ineq_cover hS_ne
      (le_refl 1) (by norm_num) h_rigidity_cover
  have h_cover_vol : |((1 : ℤ) : ℝ)| * vol_M_sym < vol_M_cone :=
    same_entropy_strict_volume_degree_bound hh_sym_pos hh_nonneg hh_le hvol_M_cone_nonneg h_strict_ent
  have h_M : vol_M_sym < vol_M_cone := by simpa using h_cover_vol
  rw [h_cover_sym, h_cover_cone] at h_M
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact lt_of_mul_lt_mul_left h_M hd_pos.le

end ConeMetricAndOrbifoldMinimality

end AlexandrovConsequences
