#!/usr/bin/env python3
"""
Script 04: Time-Series, Angular Profiles, and Master CSV/JSON Tables.

Computes exact time-domain p_S(t) trajectories (via matrix exponential in Liouville
space and exact Mittag-Leffler envelope) and dense 73-point angular profiles Phi_S(theta)
at reference noise xi = 3.0 across all physical channels (8x8 and 36x36 FAD).
"""

import json
from pathlib import Path
import numpy as np
from scipy.linalg import expm

from verify_01_hamiltonians_and_moments import (
    build_single_nucleus_system,
    build_two_nucleus_system,
    build_hamiltonian,
    ml_fast_array,
)
from verify_02_five_channel_liouville import (
    build_superops_numpy,
    solve_mittag_leffler_channel,
)

DATA_DIR = Path(__file__).resolve().parent.parent / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def compute_coherent_pS_t(H, P_S, dI, t_grid):
    evals, evecs = np.linalg.eigh(H)
    P_eig = evecs.conj().T @ P_S @ evecs
    W = (1.0 / dI) * (np.abs(P_eig) ** 2)
    om = np.abs(evals[:, None] - evals[None, :])
    cos_t = np.cos(om[:, :, None] * t_grid[None, None, :])
    return np.tensordot(W, cos_t, axes=([0, 1], [0, 1]))


def compute_liouville_pS_t(sys, H, D_mat, gamma_val, t_grid):
    """Exact matrix-exponential trajectory p_S(t) = Tr[P_S exp(L_no_rec t) rho_0]."""
    D = sys["D"]
    Id = sys["Id"]
    P_S = sys["P_S"]
    rho0 = (P_S / float(sys["dI"])).reshape(-1)
    PS_vec = P_S.T.reshape(-1)
    L_no_rec = -1j * (np.kron(H, Id) - np.kron(Id, H.T)) + gamma_val * D_mat
    dt = float(t_grid[1] - t_grid[0])
    step_op = expm(L_no_rec * dt)
    rho = rho0.copy()
    out = np.empty(len(t_grid), dtype=float)
    out[0] = float(np.real(PS_vec @ rho))
    for i in range(1, len(t_grid)):
        rho = step_op @ rho
        out[i] = float(np.real(PS_vec @ rho))
    return out


def main():
    sys8 = build_single_nucleus_system(0.5)
    A8 = [np.diag([0.5, 0.5, 5.0])]
    b0 = np.array([0.0, 0.0, 1.0])
    _, _, _, H0_8 = build_hamiltonian(sys8, b0, 1.40, A8, [1], 0.15)
    superops8 = build_superops_numpy(sys8)

    # 1. Time series p_S(t; theta=0) at xi = gamma / k_rec = 3.0 (k_rec = 1.0)
    t_grid = np.linspace(0.0, 5.0, 251)
    gamma_ref = 3.0
    pS_coh = compute_coherent_pS_t(H0_8, sys8["P_S"], sys8["dI"], t_grid)

    ts_dict = {"t": t_grid, "coherent": pS_coh}
    for mu in [0.40, 0.50, 0.70, 0.85, 1.00]:
        env = ml_fast_array((gamma_ref * t_grid) ** mu, mu)
        ts_dict[f"global_ML_mu{mu:.2f}"] = 0.25 + env * (pS_coh - 0.25)

    ts_dict["STD_xi3"] = compute_liouville_pS_t(sys8, H0_8, superops8["D_std"], gamma_ref, t_grid)
    ts_dict["local_iso_S1_xi3"] = compute_liouville_pS_t(sys8, H0_8, superops8["D_iso_S1"], gamma_ref, t_grid)
    ts_dict["local_z_S1_xi3"] = compute_liouville_pS_t(sys8, H0_8, superops8["D_z_S1"], gamma_ref, t_grid)

    cols_ts = list(ts_dict.keys())
    np.savetxt(
        DATA_DIR / "pS_time_series_xi3.csv",
        np.column_stack([ts_dict[k] for k in cols_ts]),
        delimiter=",",
        header=",".join(cols_ts),
        comments="",
        fmt="%.10f",
    )

    # 2. Dense angular profiles Phi_S(theta) across [0, 180] deg at xi = 3.0
    angles_deg = np.linspace(0.0, 180.0, 73)
    angles_rad = np.deg2rad(angles_deg)
    rho0 = (sys8["P_S"] / float(sys8["dI"])).reshape(-1)
    PS_vec = sys8["P_S"].T.reshape(-1)
    L_rec = -0.5 * superops8["aPS"] - 0.5 * superops8["aPT"]

    ang_dict = {"theta_deg": angles_deg}
    H_list = []
    for th in angles_rad:
        b = np.array([np.sin(th), 0.0, np.cos(th)])
        _, _, _, H = build_hamiltonian(sys8, b, 1.40, A8, [1], 0.15)
        H_list.append(H)

    # Coherent + Global ML
    for label, g_val, mu_val in [
        ("coherent", 0.0, 1.0),
        ("global_ML_mu0.40", 3.0, 0.40),
        ("global_ML_mu0.50", 3.0, 0.50),
        ("global_ML_mu0.70", 3.0, 0.70),
        ("global_Markov_mu1.00", 3.0, 1.00),
    ]:
        vals = []
        for H in H_list:
            evals, evecs = np.linalg.eigh(H)
            W = (1.0 / sys8["dI"]) * (np.abs(evecs.conj().T @ sys8["P_S"] @ evecs) ** 2)
            om = np.abs(evals[:, None] - evals[None, :])
            if g_val == 0.0:
                L_mat = 1.0 / (1.0 + om ** 2)
                Lz = 1.0
            else:
                s = 1.0 - 1j * om
                L_mat = np.real((s ** (mu_val - 1.0)) / (s ** mu_val + g_val ** mu_val))
                Lz = float(1.0 / (1.0 + g_val ** mu_val))
            vals.append(0.25 + float(np.sum(W * L_mat)) - 0.25 * Lz)
        ang_dict[label] = np.array(vals)

    # Physical Liouville channels at xi = 3.0
    for label, dkey in [
        ("STD_xi3", "D_std"),
        ("local_iso_S1_xi3", "D_iso_S1"),
        ("local_z_S1_xi3", "D_z_S1"),
        ("local_z_S1_S2_xi3", "D_z_S1_S2"),
    ]:
        D_mat = superops8[dkey]
        vals = []
        for H in H_list:
            L = -1j * superops8["L_comm"](H) + L_rec + gamma_ref * D_mat
            x = np.linalg.solve(L, -rho0)
            vals.append(float(np.real(PS_vec @ x)))
        ang_dict[label] = np.array(vals)

    cols_ang = list(ang_dict.keys())
    np.savetxt(
        DATA_DIR / "angular_profiles_xi3.csv",
        np.column_stack([ang_dict[k] for k in cols_ang]),
        delimiter=",",
        header=",".join(cols_ang),
        comments="",
        fmt="%.10f",
    )

    # 3. Also compute global Mittag-Leffler angular profiles vs xi to verify absence of sign flips for mu <= 0.70
    ml_flip_check = {}
    xis_scan = np.logspace(-1.0, 1.5, 41)
    for mu in [0.40, 0.50, 0.70, 0.85, 1.00]:
        diffs_0_90 = []
        for xi in xis_scan:
            vals_0_90 = []
            for H in [H_list[0], H_list[36]]:  # 0 deg and 90 deg
                evals, evecs = np.linalg.eigh(H)
                W = (1.0 / sys8["dI"]) * (np.abs(evecs.conj().T @ sys8["P_S"] @ evecs) ** 2)
                om = np.abs(evals[:, None] - evals[None, :])
                s = 1.0 - 1j * om
                L_mat = np.real((s ** (mu - 1.0)) / (s ** mu + xi ** mu))
                Lz = float(1.0 / (1.0 + xi ** mu))
                vals_0_90.append(0.25 + float(np.sum(W * L_mat)) - 0.25 * Lz)
            diffs_0_90.append(vals_0_90[0] - vals_0_90[1])
        has_flip = any(diffs_0_90[i] * diffs_0_90[i + 1] < 0 for i in range(len(diffs_0_90) - 1))
        ml_flip_check[f"mu_{mu:.2f}"] = {
            "has_sign_flip_in_0.1_to_31.6": bool(has_flip),
            "min_signed_diff": float(min(diffs_0_90)),
            "max_signed_diff": float(max(diffs_0_90)),
        }

    # 4. Also check 36x36 physical 50 uT sign flip for global_dep and local_iso_S1
    sys36 = build_two_nucleus_system(1.0, 1.0)
    A_phys = [
        np.diag([-15.1433928, -15.1433928, 309.383037]),
        np.diag([-3.3456333, -3.3456333, 106.884180]),
    ]
    _, _, _, H0_p = build_hamiltonian(sys36, np.array([0.0, 0.0, 1.0]), 8.80429815, A_phys, [1, 1], 0.0)
    _, _, _, H90_p = build_hamiltonian(sys36, np.array([1.0, 0.0, 0.0]), 8.80429815, A_phys, [1, 1], 0.0)
    fad_phys_ml = solve_mittag_leffler_channel(
        sys36, H0_p, H90_p, [1.0, 3.0, 10.0, 30.0, 100.0, 300.0, 1000.0, 3000.0, 10000.0],
        [0.40, 0.50, 0.70, 0.85, 1.00], k_rec=1.0, fit_xmin=1000.0
    )
    for mk, entry in fad_phys_ml.items():
        recs = entry["records"]
        entry["alpha_1000_to_10000"] = entry["alpha_asym_100_to_10000"]
        pts_100 = [r for r in recs if r["xi"] >= 100.0 - 1e-9]
        lx = np.log([r["xi"] for r in pts_100])
        ly = np.log([r["abs_anisotropy"] for r in pts_100])
        entry["alpha_100_to_10000"] = float(-np.polyfit(lx, ly, 1)[0])

    out = {
        "ml_sign_flip_check_8x8": ml_flip_check,
        "fad_36x36_physical_50uT_ml_scan": fad_phys_ml,
        "reference_xi3_angular_summary": {
            k: {
                "Phi_S_0": float(v[0]),
                "Phi_S_90": float(v[36]),
                "signed_0_minus_90": float(v[0] - v[36]),
                "Delta_Phi_maxmin": float(np.max(v) - np.min(v)),
            }
            for k, v in ang_dict.items() if k != "theta_deg"
        },
    }
    with open(DATA_DIR / "verify_04_curves_and_tables.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print("Script 04 completed successfully.")
    print("ML sign flip check:", json.dumps(ml_flip_check, indent=2))


if __name__ == "__main__":
    main()
