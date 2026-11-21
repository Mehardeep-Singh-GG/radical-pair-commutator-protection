#!/usr/bin/env python3
"""
Script 01: Exact Verification of Spin Hamiltonians, Moment Invariants,
and Laplace-Mittag-Leffler Singlet Yields (< 1e-13 accuracy).

Covers:
1. Spin-1/2 single nucleus (8x8 Hilbert space)
2. Spin-1 (14N) single nucleus (12x12 Hilbert space)
3. Two-nucleus 14N5 + 14N10 FAD^{.-} model (36x36 Hilbert space)
   - Both canonical dimensionless parameters and physical 50 uT FAD^{.-} parameters
4. Exact closed-form verification of M0, M2, and M4(theta) for arbitrary
   multi-nucleus anisotropic hyperfine tensors A_k.
5. High-precision (mpmath 50-digit + scipy quad) verification of the exact
   Laplace-Mittag-Leffler singlet yield formula vs time-domain quadrature.
"""

import json
from pathlib import Path
import numpy as np
import mpmath as mp
from scipy.integrate import quad

mp.mp.dps = 50

DATA_DIR = Path(__file__).resolve().parent.parent / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def spin_matrices(spin_val: float):
    """Return (Ix, Iy, Iz, I_eye) for spin magnitude spin_val."""
    dim = int(round(2.0 * spin_val + 1.0))
    m_vals = np.arange(spin_val, -spin_val - 1.0, -1.0)
    Ip = np.zeros((dim, dim), dtype=complex)
    for i in range(dim - 1):
        m = m_vals[i + 1]
        Ip[i, i + 1] = np.sqrt(spin_val * (spin_val + 1.0) - m * (m + 1.0))
    Im = Ip.conj().T
    Ix = 0.5 * (Ip + Im)
    Iy = -0.5j * (Ip - Im)
    Iz = np.diag(m_vals).astype(complex)
    return Ix, Iy, Iz, np.eye(dim, dtype=complex)


def build_single_nucleus_system(spin_I: float):
    """Build spin operators on H_e1 (2) x H_e2 (2) x H_I (2I+1)."""
    sx, sy, sz, I2 = spin_matrices(0.5)
    Ix_loc, Iy_loc, Iz_loc, IdI = spin_matrices(spin_I)
    dI = IdI.shape[0]
    D = 4 * dI

    def k3(A, B, C):
        return np.kron(np.kron(A, B), C)

    S1 = (k3(sx, I2, IdI), k3(sy, I2, IdI), k3(sz, I2, IdI))
    S2 = (k3(I2, sx, IdI), k3(I2, sy, IdI), k3(I2, sz, IdI))
    Iop = (k3(I2, I2, Ix_loc), k3(I2, I2, Iy_loc), k3(I2, I2, Iz_loc))
    Id = np.eye(D, dtype=complex)
    S1_dot_S2 = sum(S1[a] @ S2[a] for a in range(3))
    P_S = 0.25 * Id - S1_dot_S2
    P_T = 0.75 * Id + S1_dot_S2
    return {
        "D": D,
        "dI": dI,
        "S1": S1,
        "S2": S2,
        "I_list": [Iop],
        "spin_list": [spin_I],
        "Id": Id,
        "S1_dot_S2": S1_dot_S2,
        "P_S": P_S,
        "P_T": P_T,
    }


def build_two_nucleus_system(spin_I1: float = 1.0, spin_I2: float = 1.0):
    """Build spin operators on H_e1 (2) x H_e2 (2) x H_I1 (3) x H_I2 (3) -> 36x36."""
    sx, sy, sz, I2 = spin_matrices(0.5)
    I1x, I1y, I1z, Id1 = spin_matrices(spin_I1)
    I2x, I2y, I2z, Id2 = spin_matrices(spin_I2)
    dI = Id1.shape[0] * Id2.shape[0]
    D = 4 * dI

    def k4(A, B, C, E):
        return np.kron(np.kron(np.kron(A, B), C), E)

    S1 = (k4(sx, I2, Id1, Id2), k4(sy, I2, Id1, Id2), k4(sz, I2, Id1, Id2))
    S2 = (k4(I2, sx, Id1, Id2), k4(I2, sy, Id1, Id2), k4(I2, sz, Id1, Id2))
    N1 = (k4(I2, I2, I1x, Id2), k4(I2, I2, I1y, Id2), k4(I2, I2, I1z, Id2))
    N2 = (k4(I2, I2, Id1, I2x), k4(I2, I2, Id1, I2y), k4(I2, I2, Id1, I2z))
    Id = np.eye(D, dtype=complex)
    S1_dot_S2 = sum(S1[a] @ S2[a] for a in range(3))
    P_S = 0.25 * Id - S1_dot_S2
    P_T = 0.75 * Id + S1_dot_S2
    return {
        "D": D,
        "dI": dI,
        "S1": S1,
        "S2": S2,
        "I_list": [N1, N2],
        "spin_list": [spin_I1, spin_I2],
        "Id": Id,
        "S1_dot_S2": S1_dot_S2,
        "P_S": P_S,
        "P_T": P_T,
    }


def build_hamiltonian(sys: dict, b_unit: np.ndarray, omega_L: float,
                      A_tensors: list, electron_idx: list, J_ex: float) -> np.ndarray:
    """
    Construct H_RP(b_unit) = omega_L * b_unit . (S1 + S2)
                            + sum_k S_{e_k} . A_k . I_k
                            - J_ex * (2 S1.S2 + 0.5 I).
    """
    S1, S2 = sys["S1"], sys["S2"]
    H_Z = omega_L * sum(b_unit[a] * (S1[a] + S2[a]) for a in range(3))
    H_HF = np.zeros_like(sys["Id"])
    for A_k, I_k, e_idx in zip(A_tensors, sys["I_list"], electron_idx):
        S_e = S1 if e_idx == 1 else S2
        for a in range(3):
            for c in range(3):
                if A_k[a, c] != 0.0:
                    H_HF += A_k[a, c] * (S_e[a] @ I_k[c])
    H_ex = -J_ex * (2.0 * sys["S1_dot_S2"] + 0.5 * sys["Id"])
    return H_Z, H_HF, H_ex, H_Z + H_HF + H_ex


def compute_moments_numeric(H: np.ndarray, P_S: np.ndarray, dI: int):
    """Exact Frobenius commutator moments M_0, M_2, M_4."""
    c1 = H @ P_S - P_S @ H
    c2 = H @ c1 - c1 @ H
    M0 = float(np.real(np.trace(P_S @ P_S)) / dI)
    M2 = float(np.real(np.sum(np.abs(c1) ** 2)) / dI)
    M4 = float(np.real(np.sum(np.abs(c2) ** 2)) / dI)
    return M0, M2, M4


def analytic_M2(A_tensors: list, spin_list: list) -> float:
    """Exact closed form: M_2 = sum_k [I_k(I_k+1)/6] * Tr(A_k A_k^T)."""
    total = 0.0
    for A_k, Ik in zip(A_tensors, spin_list):
        total += (Ik * (Ik + 1.0) / 6.0) * float(np.trace(A_k @ A_k.T))
    return total


def analytic_M4_theta_dep(b_unit: np.ndarray, omega_L: float,
                          A_tensors: list, spin_list: list) -> float:
    """
    Exact theta-dependent part of M_4(b_unit):
      M_4(b_unit) - M_4_iso = sum_k [I_k(I_k+1)/6] * omega_L^2 * (Tr(A_k A_k^T) - b^T (A_k A_k^T) b)
    (equivalently, M_4(b) - M_4(z) = sum_k [I_k(I_k+1)/6] * omega_L^2 * (z^T A_k A_k^T z - b^T A_k A_k^T b)).
    """
    total = 0.0
    for A_k, Ik in zip(A_tensors, spin_list):
        G_k = A_k @ A_k.T
        total += (Ik * (Ik + 1.0) / 6.0) * (omega_L ** 2) * float(np.trace(G_k) - b_unit @ G_k @ b_unit)
    return total


def ml_fast_array(z: np.ndarray, mu: float) -> np.ndarray:
    """Vectorized high-precision Mittag-Leffler E_mu(-z) for z >= 0, 0 < mu <= 1."""
    from scipy.special import gamma as sp_gamma, erfcx
    z = np.asarray(z, dtype=float)
    if abs(mu - 1.0) < 1e-14:
        return np.exp(-z)
    if abs(mu - 0.5) < 1e-14:
        return erfcx(z)
    out = np.empty_like(z)
    m_small = z < 0.8
    if np.any(m_small):
        zs = z[m_small]
        k = np.arange(0, 80, dtype=float)
        out[m_small] = np.sum(((-zs[:, None]) ** k[None, :]) / sp_gamma(mu * k[None, :] + 1.0), axis=1)
    if np.any(~m_small):
        zm = z[~m_small]
        s_max = 45.0 ** (mu / 4.0)
        nodes, weights = np.polynomial.legendre.leggauss(192)
        s = 0.5 * s_max * (nodes + 1.0)
        w = 0.5 * s_max * weights
        r = s ** 4
        jac = 4.0 * (s ** 3)
        exp_fac = np.exp(-(s ** (4.0 / mu)))
        cos_pm = np.cos(np.pi * mu)
        sin_pm = np.sin(np.pi * mu)
        # Process in chunks to avoid giant intermediate arrays
        res_mid = np.empty_like(zm)
        chunk = 4000
        for i0 in range(0, len(zm), chunk):
            zc = zm[i0:i0 + chunk]
            denom = r[None, :] ** 2 + 2.0 * r[None, :] * zc[:, None] * cos_pm + zc[:, None] ** 2
            integrand = (exp_fac * jac)[None, :] * zc[:, None] / denom
            res_mid[i0:i0 + chunk] = (sin_pm / (np.pi * mu)) * (integrand @ w)
        out[~m_small] = res_mid
    return out


def laplace_ml_weight_mp(omega: np.ndarray, mu: float, k_rec: float, gamma_deph: float) -> np.ndarray:
    """Exact Laplace-Mittag-Leffler weight in mpmath precision converted to float64."""
    mu_m = mp.mpf(mu)
    k_m = mp.mpf(k_rec)
    g_mu = mp.mpf(gamma_deph) ** mu_m
    out = np.empty_like(omega, dtype=float)
    it = np.nditer(omega, flags=["multi_index"])
    for val in it:
        s = k_m - 1j * mp.mpf(float(val))
        w = k_m * mp.re((s ** (mu_m - 1)) / (s ** mu_m + g_mu))
        out[it.multi_index] = float(w)
    return out


def verify_laplace_vs_quadrature(sys: dict, b_unit: np.ndarray, omega_L: float,
                                A_tensors: list, electron_idx: list, J_ex: float,
                                k_rec: float, gamma_deph: float, mu: float):
    """Compare exact spectral Laplace-ML formula against numerical time quadrature."""
    _, _, _, H = build_hamiltonian(sys, b_unit, omega_L, A_tensors, electron_idx, J_ex)
    evals, evecs = np.linalg.eigh(H)
    P_S_eig = evecs.conj().T @ sys["P_S"] @ evecs
    W = (1.0 / sys["dI"]) * (np.abs(P_S_eig) ** 2)
    omega_mat = np.abs(evals[:, None] - evals[None, :])

    L_mat = laplace_ml_weight_mp(omega_mat, mu, k_rec, gamma_deph)
    L_zero = float(laplace_ml_weight_mp(np.array([0.0]), mu, k_rec, gamma_deph)[0])
    phi_exact = 0.25 + float(np.sum(W * L_mat)) - 0.25 * L_zero

    # Piecewise 16-point Gauss-Legendre quadrature resolving both the t=0 branch point
    # (via t = u^10 on [0, t_split]) and highest frequency omega_max up to T_cut = 42/k_rec.
    max_omega = float(np.max(omega_mat))
    T_cut = 42.0 / k_rec
    t_split = min(0.2 / k_rec, T_cut)
    dt_target = min(0.5 / k_rec, np.pi / max(max_omega, 1.0))

    gl_nodes, gl_weights = np.polynomial.legendre.leggauss(16)

    # Region 1: t = u^10 on u in [0, u_max], dt/du <= 10 * u_max^9
    u_max = t_split ** 0.1
    du_target = dt_target / max(10.0 * (u_max ** 9), 1e-12)
    n_u_panels = max(4, int(np.ceil(u_max / du_target)))
    u_edges = np.linspace(0.0, u_max, n_u_panels + 1)
    ua, ub = u_edges[:-1, None], u_edges[1:, None]
    u_nodes = (0.5 * (ub - ua) * gl_nodes[None, :] + 0.5 * (ub + ua)).ravel()
    wu_nodes = (0.5 * (ub - ua) * gl_weights[None, :]).ravel()
    t1_nodes = u_nodes ** 10
    w1_nodes = wu_nodes * (10.0 * (u_nodes ** 9))

    # Region 2: uniform panels on [t_split, T_cut]
    n_t_panels = max(4, int(np.ceil((T_cut - t_split) / dt_target)))
    t_edges = np.linspace(t_split, T_cut, n_t_panels + 1)
    ta, tb = t_edges[:-1, None], t_edges[1:, None]
    t2_nodes = (0.5 * (tb - ta) * gl_nodes[None, :] + 0.5 * (tb + ta)).ravel()
    w2_nodes = (0.5 * (tb - ta) * gl_weights[None, :]).ravel()

    t_nodes = np.concatenate([t1_nodes, t2_nodes])
    w_nodes = np.concatenate([w1_nodes, w2_nodes])

    env_vals = ml_fast_array((gamma_deph * t_nodes) ** mu, mu) if gamma_deph > 0 else np.ones_like(t_nodes)
    p_coh_vals = np.empty_like(t_nodes)
    batch = 500
    for i0 in range(0, len(t_nodes), batch):
        tb = t_nodes[i0:i0 + batch]
        cos_b = np.cos(omega_mat[:, :, None] * tb[None, None, :])
        p_coh_vals[i0:i0 + batch] = np.tensordot(W, cos_b, axes=([0, 1], [0, 1]))

    integrand_vals = k_rec * np.exp(-k_rec * t_nodes) * (0.25 + env_vals * (p_coh_vals - 0.25))
    phi_quad = float(np.sum(w_nodes * integrand_vals))
    return {
        "phi_exact": phi_exact,
        "phi_quad": phi_quad,
        "abs_err": abs(phi_exact - phi_quad),
        "n_panels": n_u_panels + n_t_panels,
        "n_quad_nodes": len(t_nodes),
    }


def main():
    results = {"models": {}, "laplace_quadrature_checks": {}}

    # ------------------------------------------------------------------
    # 1. Exact Moment & Operator Checks for 8x8, 12x12, and 36x36
    # ------------------------------------------------------------------
    configs = [
        {
            "name": "spin_half_8x8",
            "sys": build_single_nucleus_system(0.5),
            "omega_L": 1.40,
            "A_tensors": [np.diag([0.5, 0.5, 5.0])],
            "electron_idx": [1],
            "J_ex": 0.15,
        },
        {
            "name": "spin_one_14N_12x12",
            "sys": build_single_nucleus_system(1.0),
            "omega_L": 1.40,
            "A_tensors": [np.diag([0.5, 0.5, 5.0])],
            "electron_idx": [1],
            "J_ex": 0.15,
        },
        {
            "name": "fad_two_14N_36x36_canonical",
            "sys": build_two_nucleus_system(1.0, 1.0),
            "omega_L": 1.40,
            "A_tensors": [np.diag([0.5, 0.5, 5.0]), np.diag([0.2, 0.2, 2.0])],
            "electron_idx": [1, 1],
            "J_ex": 0.15,
        },
        {
            # Physical FAD^{.-} N5 + N10 at Earth field B0 = 50 uT
            # Conversions: gamma_e = 176.085963 rad/(us*mT)
            # B0 = 0.05 mT -> omega_L = 8.804298 rad/us
            # N5 (Lee et al. 2014 / Hore & Mouritsen 2016): a_perp = -0.086 mT (-15.143 rad/us),
            #   a_par = 1.757 mT (309.383 rad/us)
            # N10: a_perp = -0.019 mT (-3.346 rad/us), a_par = 0.607 mT (106.884 rad/us)
            "name": "fad_two_14N_36x36_physical_50uT",
            "sys": build_two_nucleus_system(1.0, 1.0),
            "omega_L": 8.80429815,
            "A_tensors": [
                np.diag([-15.1433928, -15.1433928, 309.383037]),
                np.diag([-3.3456333, -3.3456333, 106.884180]),
            ],
            "electron_idx": [1, 1],
            "J_ex": 0.0,
        },
        {
            # General asymmetric non-diagonal hyperfine test across both electrons
            "name": "general_36x36_asymmetric_both_electrons",
            "sys": build_two_nucleus_system(1.0, 1.0),
            "omega_L": 1.40,
            "A_tensors": [
                np.array([[0.7, 0.3, -0.4], [0.1, 0.9, 0.2], [0.5, -0.2, 4.8]]),
                np.array([[0.4, -0.1, 0.3], [0.2, 0.6, -0.3], [-0.1, 0.4, 2.1]]),
            ],
            "electron_idx": [1, 2],
            "J_ex": 0.37,
        },
    ]

    thetas_deg = [0.0, 30.0, 45.0, 60.0, 90.0, 135.0, 180.0]
    for cfg in configs:
        name = cfg["name"]
        sys = cfg["sys"]
        P_S, P_T, Id = sys["P_S"], sys["P_T"], sys["Id"]
        dI = sys["dI"]

        # Projector & commutator checks
        idem_S = float(np.max(np.abs(P_S @ P_S - P_S)))
        idem_T = float(np.max(np.abs(P_T @ P_T - P_T)))
        ortho = float(np.max(np.abs(P_S @ P_T)))
        comp = float(np.max(np.abs(P_S + P_T - Id)))
        tr_S = float(np.real(np.trace(P_S)))
        tr_T = float(np.real(np.trace(P_T)))

        M2_pred = analytic_M2(cfg["A_tensors"], sys["spin_list"])
        moment_records = []
        max_comm_Z_err = 0.0
        max_comm_ex_err = 0.0
        max_M0_err = 0.0
        max_M2_err = 0.0
        max_M4_diff_err = 0.0

        b0 = np.array([0.0, 0.0, 1.0])
        _, _, _, H0 = build_hamiltonian(
            sys, b0, cfg["omega_L"], cfg["A_tensors"], cfg["electron_idx"], cfg["J_ex"]
        )
        _, _, M4_at_0 = compute_moments_numeric(H0, P_S, dI)
        M4_theta_pred_0 = analytic_M4_theta_dep(
            b0, cfg["omega_L"], cfg["A_tensors"], sys["spin_list"]
        )

        # Also verify J_ex invariance of M0, M2, and M4(theta)-M4(0)
        _, _, _, H0_J0 = build_hamiltonian(
            sys, b0, cfg["omega_L"], cfg["A_tensors"], cfg["electron_idx"], 0.0
        )
        _, M2_J0, M4_J0_0 = compute_moments_numeric(H0_J0, P_S, dI)

        for th_deg in thetas_deg:
            th = np.deg2rad(th_deg)
            ph = 0.35 if "general" in name else 0.0
            b_vec = np.array([np.sin(th) * np.cos(ph), np.sin(th) * np.sin(ph), np.cos(th)])
            H_Z, H_HF, H_ex, H = build_hamiltonian(
                sys, b_vec, cfg["omega_L"], cfg["A_tensors"], cfg["electron_idx"], cfg["J_ex"]
            )
            comm_Z = float(np.max(np.abs(H_Z @ P_S - P_S @ H_Z)))
            comm_ex = float(np.max(np.abs(H_ex @ P_S - P_S @ H_ex)))
            M0, M2, M4 = compute_moments_numeric(H, P_S, dI)
            delta_M4_num = M4 - M4_at_0
            delta_M4_ana = (
                analytic_M4_theta_dep(b_vec, cfg["omega_L"], cfg["A_tensors"], sys["spin_list"])
                - M4_theta_pred_0
            )
            max_comm_Z_err = max(max_comm_Z_err, comm_Z)
            max_comm_ex_err = max(max_comm_ex_err, comm_ex)
            max_M0_err = max(max_M0_err, abs(M0 - 1.0))
            max_M2_err = max(max_M2_err, abs(M2 - M2_pred))
            max_M4_diff_err = max(max_M4_diff_err, abs(delta_M4_num - delta_M4_ana))

            moment_records.append({
                "theta_deg": th_deg,
                "phi_rad": ph,
                "M0": M0,
                "M2": M2,
                "M4": M4,
                "delta_M4_numeric": delta_M4_num,
                "delta_M4_analytic": delta_M4_ana,
            })

        results["models"][name] = {
            "hilbert_dim": sys["D"],
            "nuclear_dim": dI,
            "trace_P_S": tr_S,
            "trace_P_T": tr_T,
            "projector_checks": {
                "idempotency_err_P_S": idem_S,
                "idempotency_err_P_T": idem_T,
                "orthogonality_err": ortho,
                "completeness_err": comp,
            },
            "commutator_invariance": {
                "max_norm_H_Z_P_S": max_comm_Z_err,
                "max_norm_H_ex_P_S": max_comm_ex_err,
            },
            "M2_analytic": M2_pred,
            "M2_J0_check": M2_J0,
            "M4_at_theta0": M4_at_0,
            "M4_at_theta0_J0": M4_J0_0,
            "max_M0_err": max_M0_err,
            "max_M2_err": max_M2_err,
            "rel_M2_err": max_M2_err / max(abs(M2_pred), 1e-30),
            "max_M4_diff_err": max_M4_diff_err,
            "rel_M4_diff_err": max_M4_diff_err / max(abs(M4_at_0), 1e-30),
            "moments_by_theta": moment_records,
        }

    # ------------------------------------------------------------------
    # 2. Laplace-Mittag-Leffler vs Quadrature (< 1e-13 check)
    # ------------------------------------------------------------------
    b45 = np.array([np.sin(np.pi / 4), 0.0, np.cos(np.pi / 4)])
    for cfg in configs[:4]:
        name = cfg["name"]
        quad_checks = {}
        k_rec = 1.0
        gamma_ref = 3.0 if "physical" not in name else 30.0
        for mu in [0.4, 0.5, 0.7, 0.85, 1.0]:
            res_q = verify_laplace_vs_quadrature(
                cfg["sys"], b45, cfg["omega_L"], cfg["A_tensors"],
                cfg["electron_idx"], cfg["J_ex"], k_rec, gamma_ref, mu
            )
            quad_checks[f"mu_{mu:.2f}"] = res_q
        results["laplace_quadrature_checks"][name] = quad_checks

    out_path = DATA_DIR / "verify_01_moments_and_laplace.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2)

    print("=== Script 01 Summary ===")
    for name, m in results["models"].items():
        print(
            f"{name:40s} | dim={m['hilbert_dim']:2d} | M2={m['M2_analytic']:.6f} "
            f"| max_M2_err={m['max_M2_err']:.2e} | max_M4_err={m['max_M4_diff_err']:.2e} "
            f"| [HZ,PS]={m['commutator_invariance']['max_norm_H_Z_P_S']:.2e}"
        )
    for name, qdict in results["laplace_quadrature_checks"].items():
        worst = max(v["abs_err"] for v in qdict.values())
        print(f"Laplace vs Quad ({name:32s}): worst abs_err = {worst:.3e}")


if __name__ == "__main__":
    main()
