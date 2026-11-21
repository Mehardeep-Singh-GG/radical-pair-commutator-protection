#!/usr/bin/env python3
"""
Script 05: Fast Supplementary High-Precision Cross-Checks (< 20s).

1. Exact 45-digit mpmath local_iso_S1 Markovian reference yields at all Protocol A
   and Protocol C gamma_eff values (replacing float64 noise at gamma_eff >= 500).
2. 12x12 (14N spin-1) 5-channel asymptotic slopes across xi in [10, 10^4].
3. 36x36 FAD^{.-} physical 50 uT extended to xi in [10^4, 10^6] so STD and
   local_z_S1_S2 reach their true Zeno asymptotic slopes (gamma >> A_par^2/k).
"""

import json
import time
from pathlib import Path
import numpy as np
import mpmath as mp
import scipy.sparse as sp
import scipy.sparse.linalg as spla

from verify_01_hamiltonians_and_moments import (
    build_single_nucleus_system,
    build_two_nucleus_system,
    build_hamiltonian,
)
from verify_02_five_channel_liouville import (
    build_superops_numpy,
    solve_mp_channel,
    solve_mittag_leffler_channel,
    solve_sparse_refined_mp,
)

DATA_DIR = Path(__file__).resolve().parent.parent / "data"


def main():
    t0 = time.time()
    mp.mp.dps = 45

    # 1. Exact mpmath local_iso_S1 reference at Protocol A and C gamma_eff points
    sys8 = build_single_nucleus_system(0.5)
    A8 = [np.diag([0.5, 0.5, 5.0])]
    _, _, _, H0_8 = build_hamiltonian(sys8, np.array([0.0, 0.0, 1.0]), 1.40, A8, [1], 0.15)
    _, _, _, H90_8 = build_hamiltonian(sys8, np.array([1.0, 0.0, 0.0]), 1.40, A8, [1], 0.15)
    ops8 = build_superops_numpy(sys8)

    # Load gamma_eff grids from verify_03 if present, otherwise use known grid
    v3_path = DATA_DIR / "verify_03_microscopic_ado_and_mc.json"
    g_list_A = []
    g_list_C = []
    if v3_path.exists():
        with open(v3_path) as f:
            v3 = json.load(f)
        g_list_A = [r["gamma_eff"] for r in v3["protocol_A_fixed_sigma"]["iso3d_mu0.50"]]
        g_list_C = [r["gamma_eff"] for r in v3["protocol_C_sigma_sweep"]["records"]]
    else:
        tau_int_05 = 138.399
        g_list_A = [2.0 * 9.0 * tc * tau_int_05 for tc in [0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0, 10.0, 30.0]]
        g_list_C = [2.0 * (s ** 2) * 0.2 * tau_int_05 for s in [0.3, 0.7, 1.5, 3.0, 6.0, 12.0, 24.0]]

    print("Computing exact 45-digit mpmath Markovian local_iso_S1 reference for Prot A & C...")
    mp_protA_markov = solve_mp_channel(sys8, H0_8, H90_8, ops8, "D_iso_S1", g_list_A)
    mp_protC_markov = solve_mp_channel(sys8, H0_8, H90_8, ops8, "D_iso_S1", g_list_C)

    # 2. 12x12 (14N spin-1) verification across all 5 channels
    print("Computing 12x12 (14N) 5-channel asymptotic slopes...")
    sys12 = build_single_nucleus_system(1.0)
    _, _, _, H0_12 = build_hamiltonian(sys12, np.array([0.0, 0.0, 1.0]), 1.40, A8, [1], 0.15)
    _, _, _, H90_12 = build_hamiltonian(sys12, np.array([1.0, 0.0, 0.0]), 1.40, A8, [1], 0.15)
    ops12 = build_superops_numpy(sys12)
    xis_12 = [1.0, 10.0, 100.0, 1000.0, 10000.0]
    ml_12 = solve_mittag_leffler_channel(sys12, H0_12, H90_12, xis_12, [0.5, 1.0], k_rec=1.0, fit_xmin=100.0)

    rho0_12 = (sys12["P_S"] / float(sys12["dI"])).reshape(-1)
    PS_vec_12 = sys12["P_S"].T.reshape(-1)
    L_rec_12 = -0.5 * ops12["aPS"] - 0.5 * ops12["aPT"]
    L0_12 = -1j * ops12["L_comm"](H0_12) + L_rec_12
    L90_12 = -1j * ops12["L_comm"](H90_12) + L_rec_12

    ch_12 = {}
    for cname, dkey in [("STD", "D_std"), ("local_z_S1", "D_z_S1"), ("local_z_S1_S2", "D_z_S1_S2")]:
        D_m = ops12[dkey]
        recs = []
        for xi in xis_12:
            p0 = float(np.real(PS_vec_12 @ np.linalg.solve(L0_12 + xi * D_m, -rho0_12)))
            p90 = float(np.real(PS_vec_12 @ np.linalg.solve(L90_12 + xi * D_m, -rho0_12)))
            recs.append({"xi": xi, "Phi_S_0": p0, "Phi_S_90": p90, "signed_anisotropy": p0 - p90})
        hi = [r for r in recs if r["xi"] >= 100.0]
        slope = float(-np.polyfit(np.log([r["xi"] for r in hi]), np.log([abs(r["signed_anisotropy"]) for r in hi]), 1)[0])
        ch_12[cname] = {"records": recs, "alpha_asym_100_to_10000": slope}

    # For 12x12 local_iso_S1 at xi=100,1000,10000 in float64? Check if |dPhi| ~ 1e-17 at 10k -> use mpmath for xi=10,100,1000,10000!
    ch_12["local_iso_S1"] = solve_mp_channel(sys12, H0_12, H90_12, ops12, "D_iso_S1", [10.0, 100.0, 1000.0, 10000.0])

    # 3. Exact 3D Static Gaussian Random-Field Limit (tau_c -> inf) via quadrature
    print("Computing exact 3D static Gaussian random-field quadrature (sigma in [0.3..1000])...")
    P_S8 = sys8["P_S"]
    S1_8 = sys8["S1"]
    x_u, w_u = np.polynomial.legendre.leggauss(12)
    x_p, w_p = np.polynomial.legendre.leggauss(12)
    phis_q = np.pi * (x_p + 1.0)
    w_phis_q = 0.5 * w_p
    w_us_q = 0.5 * w_u

    def static_yield(H, eta_vec):
        Htot = H + sum(eta_vec[a] * S1_8[a] for a in range(3))
        ev, evec = np.linalg.eigh(Htot)
        Peig = evec.conj().T @ P_S8 @ evec
        W = 0.5 * (np.abs(Peig) ** 2)
        om = ev[:, None] - ev[None, :]
        return float(np.sum(W / (1.0 + om ** 2)))

    static_3d_curve = []
    xr_q, wr_q = np.polynomial.legendre.leggauss(12)
    for sig in [0.3, 0.7, 1.5, 3.0, 6.0, 12.0, 24.0, 100.0, 300.0]:
        edges = np.unique(np.concatenate([
            np.linspace(0.0, min(20.0, 8.0 * sig), 22),
            np.geomspace(min(20.0, 8.0 * sig) + 1e-6, 8.0 * sig, 22),
        ]))
        R_n = (0.5 * (edges[1:, None] - edges[:-1, None]) * xr_q[None, :] + 0.5 * (edges[1:, None] + edges[:-1, None])).ravel()
        WR_n = (0.5 * (edges[1:, None] - edges[:-1, None]) * wr_q[None, :]).ravel()
        pdf_R = np.sqrt(2.0 / np.pi) * (R_n ** 2 / (sig ** 3)) * np.exp(-0.5 * (R_n / sig) ** 2)
        tot = 0.0
        for R, wR, pR in zip(R_n, WR_n, pdf_R):
            if wR * pR < 1e-16:
                continue
            s_val = 0.0
            for u, wu in zip(x_u, w_us_q):
                st = np.sqrt(1.0 - u * u)
                for ph, wp in zip(phis_q, w_phis_q):
                    v = R * np.array([st * np.cos(ph), st * np.sin(ph), u])
                    s_val += wu * wp * (static_yield(H0_8, v) - static_yield(H90_8, v))
            tot += wR * pR * s_val
        static_3d_curve.append({"sigma": sig, "signed_anisotropy": float(tot)})
    hi_st = [r for r in static_3d_curve if r["sigma"] >= 12.0]
    static_sigma_slope = float(-np.polyfit(np.log([r["sigma"] for r in hi_st]), np.log([abs(r["signed_anisotropy"]) for r in hi_st]), 1)[0])

    # 4. High-precision cubic-paired OU-MC for ProtC (tau_c = 5.0 slow bath, sig in [1,2,3,5,8,12])
    print("Computing high-precision slow-bath ProtC (tau_c = 5.0)...")
    from prony_ado_lib import fit_power_law_prony
    fit_05 = fit_power_law_prony(0.50, u_max=1000.0, K=8)
    c_t05, nu_t05 = fit_05["c_tilde"], fit_05["nu_tilde"]
    tau_int_ratio_05 = fit_05["tau_int_over_tau_c"]

    def run_cubic_ou_mc(tc_val, sig_val, n_seeds=120, dt=0.008, T_max=10.0, seed=901):
        rng = np.random.default_rng(seed)
        c_arr = (sig_val ** 2) * c_t05
        nu_arr = nu_t05 / tc_val
        K = len(c_arr)
        ev, evec = np.linalg.eigh(P_S8)
        psi0 = evec[:, np.where(ev > 0.5)[0]]
        max_H = float(np.linalg.norm(H0_8, ord=2) + 2.5 * sig_val)
        dt_eff = min(dt, 0.12 / max(max_H, 1.0))
        n_steps = int(np.ceil(T_max / dt_eff))
        dt_eff = T_max / n_steps
        phi_ou = np.exp(-nu_arr * dt_eff)
        x_ou = nu_arr * dt_eff
        var_eta = c_arr * (1.0 - phi_ou ** 2)
        std_eta = np.sqrt(var_eta)
        mu_I_fac = np.where(x_ou > 1e-6, (1.0 - phi_ou) / x_ou, 1.0 - 0.5 * x_ou + (x_ou ** 2) / 6.0)
        var_I = np.where(x_ou > 1e-4, c_arr * (2.0 * x_ou - 3.0 + 4.0 * phi_ou - phi_ou ** 2) / (x_ou ** 2), (2.0 / 3.0) * c_arr * x_ou)
        cov_eta_I = np.where(x_ou > 1e-5, c_arr * ((1.0 - phi_ou) ** 2) / x_ou, c_arr * x_ou * (1.0 - x_ou))
        coeff_Z1 = np.where(std_eta > 1e-15, cov_eta_I / std_eta, 0.0)
        coeff_Z2 = np.sqrt(np.maximum(var_I - coeff_Z1 ** 2, 0.0))
        sqrt_c = np.sqrt(c_arr)
        V_stack = np.stack(S1_8, axis=0)
        t_g = np.linspace(0.0, T_max, n_steps + 1)
        wt = np.full(n_steps + 1, dt_eff); wt[0] *= 0.5; wt[-1] *= 0.5; wt *= np.exp(-t_g)

        def evolve(H_s, eta_a):
            B = eta_a.shape[0]
            psi = np.broadcast_to(psi0[None, :, :], (B, 8, 2)).copy()
            y = wt[0] * np.ones(B, dtype=float)
            mid = -1j * dt_eff
            for st in range(n_steps):
                H_tot = H_s[None, :, :] + np.einsum("ba,aij->bij", eta_a[:, st, :], V_stack)
                Ap = mid * (H_tot @ psi); pn = psi + Ap
                Ap = (0.5 * mid) * (H_tot @ Ap); pn += Ap
                Ap = ((1.0 / 3.0) * mid) * (H_tot @ Ap); pn += Ap
                Ap = (0.25 * mid) * (H_tot @ Ap); psi = pn + Ap
                P_psi = np.einsum("ij,bjk->bik", P_S8, psi)
                y += wt[st + 1] * (np.real(np.sum(psi.conj() * P_psi, axis=(1, 2))) / 2.0)
            return y

        eta_modes = rng.normal(size=(n_seeds, 3, K)) * sqrt_c[None, None, :]
        eta_avg = np.empty((n_seeds, n_steps, 3), dtype=float)
        for st in range(n_steps):
            Z1 = rng.normal(size=(n_seeds, 3, K))
            Z2 = rng.normal(size=(n_seeds, 3, K))
            eta_avg[:, st, :] = np.sum(eta_modes * mu_I_fac[None, None, :] + Z1 * coeff_Z1[None, None, :] + Z2 * coeff_Z2[None, None, :], axis=2)
            eta_modes = eta_modes * phi_ou[None, None, :] + Z1 * std_eta[None, None, :]

        # 6 cubic rotations (x,y,z), (z,y,-x), (y,z,x), (x,z,-y), (z,x,y), (y,x,-z) x (+/-) = 12 trajectories/seed
        rots = [
            eta_avg,
            np.stack([eta_avg[:, :, 2], eta_avg[:, :, 1], -eta_avg[:, :, 0]], axis=2),
            np.stack([eta_avg[:, :, 1], eta_avg[:, :, 2], eta_avg[:, :, 0]], axis=2),
            np.stack([eta_avg[:, :, 0], eta_avg[:, :, 2], -eta_avg[:, :, 1]], axis=2),
            np.stack([eta_avg[:, :, 2], eta_avg[:, :, 0], eta_avg[:, :, 1]], axis=2),
            np.stack([eta_avg[:, :, 1], eta_avg[:, :, 0], -eta_avg[:, :, 2]], axis=2),
        ]
        diffs_sum = np.zeros(n_seeds)
        for r_tr in rots:
            diffs_sum += (evolve(H0_8, r_tr) - evolve(H90_8, r_tr)) + (evolve(H0_8, -r_tr) - evolve(H90_8, -r_tr))
        diffs_mean = diffs_sum / (2.0 * len(rots))
        return {
            "sigma": sig_val,
            "gamma_eff": float(2.0 * (sig_val ** 2) * tc_val * tau_int_ratio_05),
            "signed_anisotropy": float(np.mean(diffs_mean)),
            "signed_anisotropy_se": float(np.std(diffs_mean, ddof=1) / np.sqrt(n_seeds)),
        }

    seed_counts = {1.0: 150, 2.0: 150, 3.0: 150, 5.0: 200, 8.0: 400, 12.0: 400}
    protC_slow_tau5 = [run_cubic_ou_mc(5.0, s, n_seeds=seed_counts[s], seed=900 + i) for i, s in enumerate([1.0, 2.0, 3.0, 5.0, 8.0, 12.0])]
    pts_2_8 = [r for r in protC_slow_tau5 if 2.0 <= r["sigma"] <= 8.0]
    pts_2_12 = [r for r in protC_slow_tau5 if 2.0 <= r["sigma"] <= 12.0]
    c5_sig_slope_2_8 = float(-np.polyfit(np.log([r["sigma"] for r in pts_2_8]), np.log([r["signed_anisotropy"] for r in pts_2_8]), 1)[0])
    c5_sig_slope_2_12 = float(-np.polyfit(np.log([r["sigma"] for r in pts_2_12]), np.log([r["signed_anisotropy"] for r in pts_2_12]), 1)[0])
    c5_sig_slope_1_12 = float(-np.polyfit(np.log([r["sigma"] for r in protC_slow_tau5]), np.log([r["signed_anisotropy"] for r in protC_slow_tau5]), 1)[0])
    c5_xi_slope_2_8 = 0.5 * c5_sig_slope_2_8
    c5_xi_slope_2_12 = 0.5 * c5_sig_slope_2_12

    # 5. 36x36 FAD physical 50 uT extended to xi in [10^4, 10^6]
    print("Computing 36x36 FAD physical 50 uT extended tail (xi in [3e4, 1e6])...")
    sys36 = build_two_nucleus_system(1.0, 1.0)
    D36 = sys36["D"]
    Id36 = sp.eye(D36, dtype=complex, format="csc")
    P_S36, P_T36 = sys36["P_S"], sys36["P_T"]
    S1_36, S2_36 = sys36["S1"], sys36["S2"]
    rho0_36 = (P_S36 / float(sys36["dI"])).reshape(-1)
    PS_vec_36 = P_S36.T.reshape(-1)
    A_phys = [
        np.diag([-15.1433928, -15.1433928, 309.383037]),
        np.diag([-3.3456333, -3.3456333, 106.884180]),
    ]
    _, _, _, H0_p = build_hamiltonian(sys36, np.array([0.0, 0.0, 1.0]), 8.80429815, A_phys, [1, 1], 0.0)
    _, _, _, H90_p = build_hamiltonian(sys36, np.array([1.0, 0.0, 0.0]), 8.80429815, A_phys, [1, 1], 0.0)

    def L_comm_sp(A):
        As = sp.csc_matrix(A)
        return sp.kron(As, Id36, format="csc") - sp.kron(Id36, As.T, format="csc")

    def L_anti_sp(A):
        As = sp.csc_matrix(A)
        return sp.kron(As, Id36, format="csc") + sp.kron(Id36, As.T, format="csc")

    def L_diss_sp(L):
        Ls = sp.csc_matrix(L)
        return sp.kron(Ls, Ls.conj(), format="csc") - 0.5 * L_anti_sp(L.conj().T @ L)

    L_rec_sp = -0.5 * L_anti_sp(P_S36) - 0.5 * L_anti_sp(P_T36)
    L0_p_sp = -1j * L_comm_sp(H0_p) + L_rec_sp
    L90_p_sp = -1j * L_comm_sp(H90_p) + L_rec_sp

    xis_ext = [10000.0, 30000.0, 100000.0, 300000.0, 1000000.0]

    def solve_36_mp_eigsy(xis_list, mu_list):
        def to_mp_r(A):
            n = A.shape[0]
            M = mp.zeros(n, n)
            for ii in range(n):
                for jj in range(n):
                    val = float(A[ii, jj].real)
                    if val != 0.0:
                        M[ii, jj] = mp.mpf(val)
            return M
        PS_m = to_mp_r(P_S36)
        def spec(Hm):
            E, Q = mp.eigsy(Hm)
            Pe = Q.T * PS_m * Q
            W_l = [[(Pe[ii, jj] ** 2) / 9 for jj in range(36)] for ii in range(36)]
            om_l = [[abs(E[ii] - E[jj]) for jj in range(36)] for ii in range(36)]
            return W_l, om_l
        W0_m, om0_m = spec(to_mp_r(H0_p))
        W90_m, om90_m = spec(to_mp_r(H90_p))
        res_ml = {}
        for mu_v in mu_list:
            recs_m = []
            for xi_v in xis_list:
                g_m = mp.mpf(xi_v)
                def eval_p(W_l, om_l):
                    if abs(mu_v - 1.0) < 1e-12:
                        s_m = 1 + g_m
                        Lz = 1 / s_m
                        tot = mp.mpf("0.25") * (1 - Lz)
                        s2 = s_m * s_m
                        for ii in range(36):
                            for jj in range(36):
                                if W_l[ii][jj] != 0:
                                    tot += W_l[ii][jj] * s_m / (s2 + om_l[ii][jj] ** 2)
                        return tot
                    mu_m = mp.mpf(mu_v)
                    g_mu = g_m ** mu_m
                    Lz = 1 / (1 + g_mu)
                    tot = mp.mpf("0.25") * (1 - Lz)
                    for ii in range(36):
                        for jj in range(36):
                            if W_l[ii][jj] != 0:
                                s_c = 1 - 1j * om_l[ii][jj]
                                tot += W_l[ii][jj] * mp.re((s_c ** (mu_m - 1)) / (s_c ** mu_m + g_mu))
                    return tot
                p0_m = eval_p(W0_m, om0_m)
                p90_m = eval_p(W90_m, om90_m)
                diff_m = p0_m - p90_m
                recs_m.append({
                    "xi": float(xi_v),
                    "Phi_S_0": float(p0_m),
                    "Phi_S_90": float(p90_m),
                    "signed_anisotropy": float(diff_m),
                    "abs_anisotropy": float(abs(diff_m)),
                    "signed_str_mp": mp.nstr(diff_m, 18),
                })
            lx = np.log([r["xi"] for r in recs_m])
            ly = np.array([float(mp.log(abs(mp.mpf(r["signed_str_mp"])))) for r in recs_m])
            alpha_m = float(-np.polyfit(lx, ly, 1)[0])
            res_ml[f"mu_{mu_v:.2f}"] = {"records": recs_m, "alpha_asym_100_to_10000": alpha_m}
        return res_ml

    fad_phys_ext = {"global_dep_spectral": solve_36_mp_eigsy(xis_ext, [0.5, 1.0]), "sparse_channels": {}}
    PS_nz_36 = [(i, mp.mpc(float(v.real), float(v.imag))) for i, v in enumerate(PS_vec_36) if v != 0]

    for cname, D_sp in [
        ("STD", 0.5 * L_diss_sp(P_S36 - P_T36)),
        ("local_z_S1", L_diss_sp(S1_36[2])),
        ("local_z_S1_S2", L_diss_sp(S1_36[2]) + L_diss_sp(S2_36[2])),
        ("local_iso_S1", sum(L_diss_sp(S1_36[a]) for a in range(3))),
    ]:
        xis_ch = xis_ext + ([3000000.0] if cname == "local_iso_S1" else [])
        recs = []
        for xi in xis_ch:
            if cname == "local_iso_S1":
                x0_m = solve_sparse_refined_mp(L0_p_sp + xi * D_sp, -rho0_36, n_iter=6)
                x90_m = solve_sparse_refined_mp(L90_p_sp + xi * D_sp, -rho0_36, n_iter=6)
                p0_m = mp.re(sum(v * x0_m[i] for i, v in PS_nz_36))
                p90_m = mp.re(sum(v * x90_m[i] for i, v in PS_nz_36))
                diff_m = p0_m - p90_m
                recs.append({
                    "xi": xi,
                    "Phi_S_0": float(p0_m),
                    "Phi_S_90": float(p90_m),
                    "signed_anisotropy": float(diff_m),
                    "signed_str_mp": mp.nstr(diff_m, 18),
                })
            else:
                p0 = float(np.real(PS_vec_36 @ spla.spsolve(L0_p_sp + xi * D_sp, -rho0_36)))
                p90 = float(np.real(PS_vec_36 @ spla.spsolve(L90_p_sp + xi * D_sp, -rho0_36)))
                recs.append({"xi": xi, "Phi_S_0": p0, "Phi_S_90": p90, "signed_anisotropy": p0 - p90, "signed_str_mp": f"{p0 - p90:.17e}"})
        hi_1e5 = [r for r in recs if 100000.0 - 1e-6 <= r["xi"] <= 1000000.0 + 1e-6]
        slope_1e5_1e6 = float(-np.polyfit(np.log([r["xi"] for r in hi_1e5]), [float(mp.log(abs(mp.mpf(r["signed_str_mp"])))) for r in hi_1e5], 1)[0])
        slope_last2 = float(-mp.log(abs(mp.mpf(recs[-1]["signed_str_mp"])) / abs(mp.mpf(recs[-2]["signed_str_mp"]))) / mp.log(mp.mpf(recs[-1]["xi"]) / mp.mpf(recs[-2]["xi"])))
        fad_phys_ext["sparse_channels"][cname] = {
            "records": recs,
            "alpha_1e5_to_1e6": slope_1e5_1e6,
            "alpha_last_interval": slope_last2,
        }

    out = {
        "protA_mpmath_markov_local_iso_S1": mp_protA_markov,
        "protC_mpmath_markov_local_iso_S1": mp_protC_markov,
        "static_3d_gaussian_quadrature": {
            "records": static_3d_curve,
            "sigma_slope_high": static_sigma_slope,
        },
        "protC_slow_tau5_cubic_ou_mc": {
            "tau_c": 5.0,
            "mu": 0.50,
            "records": protC_slow_tau5,
            "sigma_slope_2_to_8": c5_sig_slope_2_8,
            "sigma_slope_2_to_12": c5_sig_slope_2_12,
            "sigma_slope_1_to_12": c5_sig_slope_1_12,
            "xi_eff_slope_2_to_8": c5_xi_slope_2_8,
            "xi_eff_slope_2_to_12": c5_xi_slope_2_12,
        },
        "spin1_14N_12x12": {"global_dep_spectral": ml_12, "channels": ch_12},
        "fad_36x36_physical_50uT_extended_tail": fad_phys_ext,
        "runtime_seconds": time.time() - t0,
    }
    with open(DATA_DIR / "verify_05_supplement_checks.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, allow_nan=False)
    print(f"Script 05 completed in {out['runtime_seconds']:.1f}s")
    print(f"Static 3D sigma slope: {static_sigma_slope:.4f}")
    print(f"ProtC slow (tau_c=5): slope(2..8)=sigma^-{c5_sig_slope_2_8:.3f}, slope(2..12)=sigma^-{c5_sig_slope_2_12:.3f}, slope(1..12)=sigma^-{c5_sig_slope_1_12:.3f}")
    for r in protC_slow_tau5:
        print(f"  tau5 sig={r['sigma']:4.1f}, xi_eff={r['gamma_eff']:8.1f}: dPhi={r['signed_anisotropy']:+.5e} +/- {r['signed_anisotropy_se']:.2e}")
    print("12x12 global_mu1:", round(ml_12["mu_1.00"]["alpha_asym_100_to_10000"], 5))
    print("12x12 slopes:", {k: round(v["alpha_asym_100_to_10000"], 4) for k, v in ch_12.items()})
    print("50uT extended slopes (1e5..1e6):", {k: (round(v["alpha_1e5_to_1e6"], 4), round(v["alpha_last_interval"], 4)) for k, v in fad_phys_ext["sparse_channels"].items()})
    print("50uT global_mu1 slope (1e4..1e6):", round(fad_phys_ext["global_dep_spectral"]["mu_1.00"]["alpha_asym_100_to_10000"], 5))


if __name__ == "__main__":
    main()
