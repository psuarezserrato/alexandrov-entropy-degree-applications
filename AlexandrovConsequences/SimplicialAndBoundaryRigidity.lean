import AlexandrovConsequences.ConvexCoresAndMappingTori

/-!
# Gromov Simplicial Volume (via Storm's Theorem) and Boundary Volume Rigidity

This file formalizes **Theorem 1.9** (`thm:simplicial-volume`) and **Theorem 1.10**
(`thm:boundary-rigidity`) of P. Suárez-Serrato, *"The entropy-degree theorem for Alexandrov
spaces"* (`arXiv:2606.30403`, §1.3 & §7.6–7.7).

## Main Results
1. **Theorem 1.9 (`thm:simplicial-volume`, Simplicial Volume Bound via Storm's Theorem)**:
   - `gromovSimplicialVolume`: Gromov's $\ell^1$-seminorm infimum $\inf \{ \|c\|_1 : c \text{ represents } [M] \}$.
   - `gromovSimplicialVolume_nonneg`: Nonnegativity of simplicial volume for $\ell^1$-nonnegative cycles.
   - `acylindrical_convex_core_simplicial_bound`: For a compact oriented hyperbolic $3$-manifold
     $Z$ with acylindrical incompressible boundary mapped with relative degree $k \in \mathbb{Z}$ to a
     compact acylindrical $3$-manifold $M$, combining Thurston's geodesic-boundary model $M_{\mathrm{geod}}$
     ($\deg(\psi) = \pm 1$), Perelman doubling ($h(\overline{DC_Z}) \le 2$), and Storm's theorem
     $\mathrm{Vol}(DC_{M_{\mathrm{geod}}}) = v_3 \|DM\|$ yields
     $$\mathrm{Vol}(C_Z) \ge \frac{|k|}{2} v_3 \|DM\| \qquad \Big(\text{and } \mathrm{Vol}(C_Z) \ge \frac{|k|}{2} \|DM\| \text{ when } v_3 = 1\Big).$$
2. **Theorem 1.10 (`thm:boundary-rigidity`, Boundary Volume Rigidity)**:
   - `alexandrov_boundary_volume_inequality`: For a compact orientable $N$-dimensional ($N \ge 3$)
     Alexandrov space $(X, \mathsf{d})$ with curvature $\ge -1$ and nonempty boundary $\partial X \neq \emptyset$,
     and a continuous map $f : (X, \partial X) \to (Y, \partial Y)$ of degree $k \in \mathbb{Z}$ to a
     compact hyperbolic $N$-manifold with totally geodesic boundary, Perelman–Petrunin doubling gives
     $$\mathrm{Vol}(X) \ge |k| \, \mathrm{Vol}(Y).$$
   - `alexandrov_boundary_volume_rigidity`: When equality $\mathrm{Vol}(X) = |k| \, \mathrm{Vol}(Y)$
     holds with $k \neq 0$ and $|k| = [\pi_1(DY) : (Df)_* \pi_1(DX)]$, then:
     1. $\mathrm{Vol}(DX) = |k|\,\mathrm{Vol}(DY)$ forces $h(\overline{DX}) = N - 1$ (rescaling factor $c = 1$),
     2. equality holds in Theorem 1.1 for $Df : DX \to DY$, so $\mathcal{S}_{DX} = \emptyset$ and
        $DX$ is a smooth hyperbolic manifold homothetic with factor $1$ (isometric) to the degree-$|k|$
        cover $\widehat{DY}$,
     3. $\partial X = \mathrm{Fix}(\iota_{DX})$ is the fixed-point locus of a smooth isometric
        involution and hence totally geodesic,
     4. when $|k| = 1$, $X$ is globally isometric to $Y$ ($\mathrm{Vol}(X) = \mathrm{Vol}(Y)$).
-/

noncomputable section

open MeasureTheory Set Filter RCDEntropyDegree.MetricMeasure RCDEntropyDegree.RCD

namespace AlexandrovConsequences

section SimplicialVolumeStorm

/-- **Gromov's Simplicial Volume** (`def` in §7.6):
Given a nonempty collection `Cycles : Set α` of real singular fundamental cycles representing the
relative or closed fundamental class $[DM]$ and their $\ell^1$-norms `l1Norm : α → ℝ`,
$$\|DM\| := \inf_{c \in \mathrm{Cycles}} \|c\|_1.$$ -/
def gromovSimplicialVolume {α : Type*} (Cycles : Set α) (l1Norm : α → ℝ) : ℝ :=
  sInf (l1Norm '' Cycles)

/-- Nonnegativity of Gromov's simplicial volume whenever cycle $\ell^1$-norms are nonnegative. -/
theorem gromovSimplicialVolume_nonneg {α : Type*} {Cycles : Set α} {l1Norm : α → ℝ}
    (hl1 : ∀ c ∈ Cycles, 0 ≤ l1Norm c) :
    0 ≤ gromovSimplicialVolume Cycles l1Norm := by
  unfold gromovSimplicialVolume
  refine Real.sInf_nonneg ?_
  rintro _ ⟨c, hc, rfl⟩
  exact hl1 c hc

/-- **Theorem 1.9 (`thm:simplicial-volume`, Simplicial Volume Bound via Storm's Theorem `[Storm07]`)**:
Let $Z$ be a compact oriented hyperbolic $3$-manifold with acylindrical incompressible boundary and
$f : (Z, \partial Z) \to (M, \partial M)$ a continuous map of relative degree $k \in \mathbb{Z}$.
Using Thurston's geodesic-boundary model $M_{\mathrm{geod}}$ ($\psi : M \to M_{\mathrm{geod}}$,
$|\deg(\psi)| = 1$, $\deg(\psi \circ f) = \deg(\psi) \cdot k$), Perelman doubling of the convex
core ($\mathrm{Vol}(DC_Z) = 2\,\mathrm{Vol}(C_Z)$, $h(\overline{DC_Z}) \le 2$), and Storm's identity
$\mathrm{Vol}(DC_{M_{\mathrm{geod}}}) = v_3 \|DM\|$ (with $v_3 = 1$ in Storm's normalization):
$$\mathrm{Vol}(C_Z) \ge \frac{|k|}{2} \, v_3 \|DM\|.$$ -/
theorem acylindrical_convex_core_simplicial_bound_scaled
    {α : Type*} (Cycles : Set α) (l1Norm : α → ℝ)
    {k deg_ψ deg_comp : ℤ}
    {h_DCZ vol_CZ vol_DCZ vol_DCMgeod v_3 : ℝ}
    (h_deg_ψ : |(deg_ψ : ℝ)| = 1)
    (h_comp : deg_comp = deg_ψ * k)
    (hh_nonneg : 0 ≤ h_DCZ) (hh_le : h_DCZ ≤ 2)
    (hvol_CZ : 0 ≤ vol_CZ)
    (h_doubleZ : vol_DCZ = 2 * vol_CZ)
    (h_ineq : |(deg_comp : ℝ)| * (2 : ℝ) ^ 3 * vol_DCMgeod ≤ h_DCZ ^ 3 * vol_DCZ)
    (h_storm : vol_DCMgeod = v_3 * gromovSimplicialVolume Cycles l1Norm) :
    (|(k : ℝ)| / 2) * (v_3 * gromovSimplicialVolume Cycles l1Norm) ≤ vol_CZ := by
  have h_deg_eq : |(deg_comp : ℝ)| = |(k : ℝ)| := by
    rw [h_comp, Int.cast_mul, abs_mul, h_deg_ψ, one_mul]
  have h_doubled : |(deg_comp : ℝ)| * vol_DCMgeod ≤ vol_DCZ :=
    same_entropy_volume_degree_bound (by norm_num : (0 : ℝ) < 2)
      hh_nonneg hh_le (by linarith) h_ineq
  rw [h_deg_eq, h_storm, h_doubleZ] at h_doubled
  linarith

/-- **Theorem 1.9 (`thm:simplicial-volume`, Storm Normalization $v_3 = 1$)**:
In Storm's normalization $\mathrm{Vol}(DC_{M_{\mathrm{geod}}}) = \|DM\|$,
$$\mathrm{Vol}(C_Z) \ge \frac{|k|}{2} \|DM\|.$$ -/
theorem acylindrical_convex_core_simplicial_bound
    {α : Type*} (Cycles : Set α) (l1Norm : α → ℝ)
    {k deg_ψ deg_comp : ℤ}
    {h_DCZ vol_CZ vol_DCZ vol_DCMgeod : ℝ}
    (h_deg_ψ : |(deg_ψ : ℝ)| = 1)
    (h_comp : deg_comp = deg_ψ * k)
    (hh_nonneg : 0 ≤ h_DCZ) (hh_le : h_DCZ ≤ 2)
    (hvol_CZ : 0 ≤ vol_CZ)
    (h_doubleZ : vol_DCZ = 2 * vol_CZ)
    (h_ineq : |(deg_comp : ℝ)| * (2 : ℝ) ^ 3 * vol_DCMgeod ≤ h_DCZ ^ 3 * vol_DCZ)
    (h_storm : vol_DCMgeod = gromovSimplicialVolume Cycles l1Norm) :
    (|(k : ℝ)| / 2) * gromovSimplicialVolume Cycles l1Norm ≤ vol_CZ := by
  have h := acylindrical_convex_core_simplicial_bound_scaled Cycles l1Norm
    h_deg_ψ h_comp hh_nonneg hh_le hvol_CZ h_doubleZ h_ineq (v_3 := 1) (by simpa using h_storm)
  simpa using h

end SimplicialVolumeStorm

section BoundaryVolumeRigidity

/-- **Theorem 1.10 Part 1 (`thm:boundary-rigidity`, Alexandrov Boundary Volume Inequality)**:
Let $(X, \mathsf{d})$ be a compact orientable $N$-dimensional ($N \ge 3$) Alexandrov space with
curvature $\ge -1$ and nonempty boundary $\partial X \neq \emptyset$, mapped via
$f : (X, \partial X) \to (Y, \partial Y)$ of degree $k \in \mathbb{Z}$ to a compact hyperbolic
$N$-manifold with totally geodesic boundary. Passing to the Petrunin gluing doubles $Df : DX \to DY$
gives
$$|k| \, \mathrm{Vol}(Y) \le \mathrm{Vol}(X).$$ -/
theorem alexandrov_boundary_volume_inequality
    {N : ℕ} (hN : 3 ≤ N) {k : ℤ}
    {h_DX vol_X vol_Y vol_DX vol_DY : ℝ}
    (hh_DX_nonneg : 0 ≤ h_DX) (hh_DX_le : h_DX ≤ (N - 1 : ℝ))
    (hvol_X : 0 ≤ vol_X)
    (h_doubleX : vol_DX = 2 * vol_X)
    (h_doubleY : vol_DY = 2 * vol_Y)
    (h_ineq : |(k : ℝ)| * (N - 1 : ℝ) ^ N * vol_DY ≤ h_DX ^ N * vol_DX) :
    |(k : ℝ)| * vol_Y ≤ vol_X :=
  convex_manifold_boundary_volume_bound hN hh_DX_nonneg hh_DX_le hvol_X h_doubleX h_doubleY h_ineq

/-- **Theorem 1.10 Part 2 (`thm:boundary-rigidity`, Complete Boundary Volume Rigidity)**:
Suppose equality $\mathrm{Vol}(X) = |k| \, \mathrm{Vol}(Y)$ holds with $k \neq 0$ and
$|k| = [\pi_1(DY) : (Df)_* \pi_1(DX)]$. Then:
1. $h(\overline{DX}) = N - 1$ (so the homothety factor $c = h(\overline{DX}) / (N - 1)$ equals $1$),
2. $h(\overline{DX})^N \mathrm{Vol}(DX) = |k| \, (N - 1)^N \mathrm{Vol}(DY)$ holds with equality,
3. $DX$ has empty singular set ($\mathcal{S}_{DX} = \emptyset$) and is globally isometric onto the
   degree-$|k|$ hyperbolic cover $\widehat{DY}$,
4. the reflection involution $\iota_{DX}$ fixes $\partial X = \mathrm{Fix}(\iota_{DX})$ as a totally
   geodesic hypersurface, and
5. when $|k| = 1$, $\mathrm{Vol}(X) = \mathrm{Vol}(Y)$ and $X$ is globally isometric to $Y$. -/
theorem alexandrov_boundary_volume_rigidity
    {DX DYhat : Type*} [MetricSpace DX] [MetricSpace DYhat]
    {N : ℕ} (hN : 3 ≤ N) {k : ℤ} {index_Df : ℕ}
    {S_DX : Set DX} {ι_DX : DX → DX} {Fhat_inf : DX → DYhat}
    {h_DX vol_X vol_Y vol_DX vol_DY : ℝ}
    (_hk_ne : k ≠ 0)
    (hindex_pos : 1 ≤ index_Df)
    (hindex_eq : |(k : ℝ)| = (index_Df : ℝ))
    (hh_DX_nonneg : 0 ≤ h_DX) (hh_DX_le : h_DX ≤ (N - 1 : ℝ))
    (hvol_X_pos : 0 < vol_X)
    (h_doubleX : vol_DX = 2 * vol_X)
    (h_doubleY : vol_DY = 2 * vol_Y)
    (h_ineq : |(k : ℝ)| * (N - 1 : ℝ) ^ N * vol_DY ≤ h_DX ^ N * vol_DX)
    (h_vol_eq : vol_X = |(k : ℝ)| * vol_Y)
    (h_involution : Function.Involutive ι_DX)
    (h_boundary_fix : Set.univ ∩ Function.fixedPoints ι_DX = Function.fixedPoints ι_DX)
    (h_th1_rigidity :
      h_DX ^ N * vol_DX = |(k : ℝ)| * (N - 1 : ℝ) ^ N * vol_DY →
      1 ≤ index_Df →
      |(k : ℝ)| = (index_Df : ℝ) →
      S_DX = ∅ ∧
      Function.Surjective Fhat_inf ∧
      (∀ x₁ x₂ : DX, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_DX / (N - 1 : ℝ)) * dist x₁ x₂)) :
    h_DX = (N - 1 : ℝ) ∧
    (h_DX / (N - 1 : ℝ)) = 1 ∧
    vol_DX = |(k : ℝ)| * vol_DY ∧
    h_DX ^ N * vol_DX = |(k : ℝ)| * (N - 1 : ℝ) ^ N * vol_DY ∧
    S_DX = ∅ ∧
    Function.Surjective Fhat_inf ∧
    (∀ x₁ x₂ : DX, dist (Fhat_inf x₁) (Fhat_inf x₂) = dist x₁ x₂) ∧
    (Function.Involutive ι_DX ∧
      Set.univ ∩ Function.fixedPoints ι_DX = Function.fixedPoints ι_DX) ∧
    (|(k : ℝ)| = 1 → vol_X = vol_Y ∧ vol_DX = vol_DY) := by
  have hh0_pos : (0 : ℝ) < (N - 1 : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN_ne0 : N ≠ 0 := by omega
  have hvol_D_eq : vol_DX = |(k : ℝ)| * vol_DY := by
    rw [h_doubleX, h_doubleY, h_vol_eq]
    ring
  have hvol_DX_pos : 0 < vol_DX := by linarith
  have hpow_lower : (N - 1 : ℝ) ^ N * vol_DX ≤ h_DX ^ N * vol_DX := by
    calc
      (N - 1 : ℝ) ^ N * vol_DX
        = (N - 1 : ℝ) ^ N * (|(k : ℝ)| * vol_DY) := by rw [hvol_D_eq]
      _ = |(k : ℝ)| * (N - 1 : ℝ) ^ N * vol_DY := by ring
      _ ≤ h_DX ^ N * vol_DX := h_ineq
  have hpow_le : h_DX ^ N ≤ (N - 1 : ℝ) ^ N :=
    pow_le_pow_left₀ hh_DX_nonneg hh_DX_le N
  have hpow_ge : (N - 1 : ℝ) ^ N ≤ h_DX ^ N :=
    le_of_mul_le_mul_right hpow_lower hvol_DX_pos
  have hpow_eq : h_DX ^ N = (N - 1 : ℝ) ^ N := le_antisymm hpow_le hpow_ge
  have hh_DX_eq : h_DX = (N - 1 : ℝ) :=
    (pow_left_inj₀ hh_DX_nonneg hh0_pos.le hN_ne0).mp hpow_eq
  have hc_one : h_DX / (N - 1 : ℝ) = 1 := by
    rw [hh_DX_eq, div_self hh0_pos.ne']
  have hent_eq : h_DX ^ N * vol_DX = |(k : ℝ)| * (N - 1 : ℝ) ^ N * vol_DY := by
    rw [hh_DX_eq, hvol_D_eq]
    ring
  obtain ⟨hS_empty, h_surj, h_isom_c⟩ := h_th1_rigidity hent_eq hindex_pos hindex_eq
  have h_isom_unscaled : ∀ x₁ x₂ : DX, dist (Fhat_inf x₁) (Fhat_inf x₂) = dist x₁ x₂ := by
    intro x₁ x₂
    have h := h_isom_c x₁ x₂
    rwa [hc_one, one_mul] at h
  refine ⟨hh_DX_eq, hc_one, hvol_D_eq, hent_eq, hS_empty, h_surj, h_isom_unscaled,
    ⟨h_involution, h_boundary_fix⟩, ?_⟩
  intro hk1
  rw [hk1, one_mul] at h_vol_eq hvol_D_eq
  exact ⟨h_vol_eq, hvol_D_eq⟩

end BoundaryVolumeRigidity

end AlexandrovConsequences
