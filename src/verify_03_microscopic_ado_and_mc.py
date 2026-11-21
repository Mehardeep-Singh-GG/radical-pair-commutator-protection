#!/usr/bin/env python3
"""
Script 03: Microscopic Non-Markovian Crucible (Prony/NNLS + Exact ADO + Colored-OU MC).

Tests non-commuting local spin-bath noise on S1 with physical power-law
autocorrelation C(t) = sigma^2 * (1 + t / tau_c)^(-mu), fitted via positive
K=8 Prony/NNLS exponential modes (< 1% relative residual over 7 decades).

Covers:
1. Prony/NNLS fits for mu in {0.40, 0.50, 0.70, 0.85} on u in [0, 1000].
2. ADO tier/truncation convergence audit vs independent Gillespie-OU Monte Carlo.
3. Protocol A (Fixed RMS coupling sigma = 3.0 across tau_c in [1e-3, 30]):
   Motional-narrowing -> resonance -> quasi-static crossover for both uniaxial (S1z)
   and 3D isotropic (S1) noise, vs rate-matched Markovian Lindblad and matched-tau_int
   single-mode exponential OU bath.
4. Protocol B (Fixed integrated rate gamma_eff = 10.0 across tau_c in [1e-3, 30]):
   Spectral memory redistribution escaping Markovian suppression.
5. Protocol C (Coupling-strength sweep sigma in [0.3, 24.0] at fixed tau_c = 0.2):
   Tests true xi_eff and sigma scaling in non-commuting 3D isotropic colored baths
   (O(sigma^-2) = O(xi_eff^-1) vs Markovian O(xi^-4) vs static 3D limit).
"""

import json
import time
from pathlib import Path
import numpy as np

from verify_01_hamiltonians_and_moments import (
    build_single_nucleus_system,
    build_hamiltonian,
)
from prony_ado_lib import (
    fit_power_law_prony,
    solve_ado_yield,
    solve_colored_ou_mc,
)

DATA_DIR = Path(__file__).resolve().parent.parent / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def solve_markovian_lindblad(sys8, H0, H90, V_ops, gamma_rate):
    """Exact Markovian Lindblad yield for sum_a gamma_rate * D[V_a]."""
    D = sys8["D"]
    Id = sys8["Id"]
    P_S, P_T = sys8["P_S"], sys8["P_T"]
    rho0 = (P_S / float(sys8["dI"])).reshape(-1)
    PS_vec = P_S.T.reshape(-1)

    D_op = np.zeros((D * D, D * D), dtype=complex)
    for V in V_ops:
        V2 = V @ V
        D_op += np.kron(V, V.conj()) - 0.5 * (np.kron(V2, Id) + np.kron(Id, V2.T))

    def eval_h(H):
        L = -1j * (np.kron(H, Id) - np.kron(Id, H.T)) - np.eye(D * D, dtype=complex) + gamma_rate * D_op
        x = np.linalg.solve(L, -rho0)
        return float(np.real(PS_vec @ x))

    p0 = eval_h(H0)
    p90 = eval_h(H90)
    return {"Phi_S_0": p0, "Phi_S_90": p90, "signed_anisotropy": p0 - p90}


def main():
    t_start = time.time()
    sys8 = build_single_nucleus_system(0.5)
    A_t = [np.diag([0.5, 0.5, 5.0])]
    _, _, _, H0 = build_hamiltonian(sys8, np.array([0.0, 0.0, 1.0]), 1.4, A_t, [1], 0.15)
    _, _, _, H90 = build_hamiltonian(sys8, np.array([1.0, 0.0, 0.0]), 1.4, A_t, [1], 0.15)
    P_S, P_T, dI = sys8["P_S"], sys8["P_T"], sys8["dI"]
    S1z = sys8["S1"][2]
    S1 = list(sys8["S1"])

    # ------------------------------------------------------------------
    # 1. Prony/NNLS Exponential Fits for Power-Law Baths
    # ------------------------------------------------------------------
    prony_fits = {}
    for mu in [0.40, 0.50, 0.70, 0.85]:
        fit = fit_power_law_prony(mu, u_max=1000.0, K=8)
        prony_fits[f"mu_{mu:.2f}"] = {
            "mu": fit["mu"],
            "u_max": fit["u_max"],
            "K_active": fit["K_active"],
            "c_tilde": fit["c_tilde"].tolist(),
            "nu_tilde": fit["nu_tilde"].tolist(),
            "max_abs_err": fit["max_abs_err"],
            "max_rel_err": fit["max_rel_err"],
            "tau_int_over_tau_c": fit["tau_int_over_tau_c"],
        }
        print(
            f"Prony fit mu={mu:.2f}: K={fit['K_active']}, "
            f"max_abs_err={fit['max_abs_err']:.3e}, max_rel_err={fit['max_rel_err']:.3e}, "
            f"tau_int/tau_c={fit['tau_int_over_tau_c']:.3f}"
        )

    fit_05 = prony_fits["mu_0.50"]
    c_tilde_05 = np.array(fit_05["c_tilde"])
    nu_tilde_05 = np.array(fit_05["nu_tilde"])
    tau_int_ratio_05 = fit_05["tau_int_over_tau_c"]

    fit_085 = prony_fits["mu_0.85"]
    c_tilde_085 = np.array(fit_085["c_tilde"])
    nu_tilde_085 = np.array(fit_085["nu_tilde"])
    tau_int_ratio_085 = fit_085["tau_int_over_tau_c"]

    # ------------------------------------------------------------------
    # 2. ADO Truncation Convergence Audit vs Colored-OU MC
    # ------------------------------------------------------------------
    audit_cases = [
        ("z_axis_fast_mu0.5", [S1z], c_tilde_05, nu_tilde_05, 0.005, 1.5, [200, 600, 1500], 500),
        ("z_axis_mod_mu0.5", [S1z], c_tilde_05, nu_tilde_05, 0.05, 3.0, [200, 600, 1500, 2500], 600),
        ("iso3d_fast_mu0.5", S1, c_tilde_05, nu_tilde_05, 0.005, 1.5, [400, 1200, 2500], 400),
    ]
    ado_audit = {}
    for label, vops, ct, nt, tc, sig, m_list, n_pairs in audit_cases:
        c_arr = (sig ** 2) * ct
        nu_arr = nt / tc
        ado_runs = []
        groups = [(c_arr, nu_arr)] * len(vops)
        for m_ado in m_list:
            p0, _, n_act, i0 = solve_ado_yield(H0, P_S, P_T, dI, 1.0, 1.0, vops, groups, max_tier=10, max_ados=m_ado)
            p90, _, _, i90 = solve_ado_yield(H90, P_S, P_T, dI, 1.0, 1.0, vops, groups, max_tier=10, max_ados=m_ado)
            ado_runs.append({
                "N_ado": n_act,
                "gmres_info": [i0, i90],
                "Phi_S_0": p0,
                "Phi_S_90": p90,
                "signed_anisotropy": p0 - p90,
            })
        mc_res = solve_colored_ou_mc(H0, H90, P_S, dI, vops, c_arr, nu_arr, k_rec=1.0, dt=0.008, T_max=12.0, n_pairs=n_pairs, seed=101)
        ado_audit[label] = {
            "tau_c": tc,
            "sigma": sig,
            "gamma_eff": float(2.0 * (sig ** 2) * tc * np.sum(ct / nt)),
            "ado_convergence": ado_runs,
            "ou_mc_crosscheck": mc_res,
        }
        print(
            f"Audit {label:18s}: ADO(N={ado_runs[-1]['N_ado']}) dPhi={ado_runs[-1]['signed_anisotropy']:+.6f} "
            f"vs OU-MC dPhi={mc_res['signed_anisotropy']:+.6f} +/- {mc_res['signed_anisotropy_se']:.6f}"
        )

    # ------------------------------------------------------------------
    # 3. Protocol A: Fixed RMS Amplitude sigma = 3.0 across tau_c
    # ------------------------------------------------------------------
    tau_c_grid = [0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0, 10.0, 30.0]
    sigma_fixed = 3.0
    protocol_A = {"sigma": sigma_fixed, "z_axis_mu0.50": [], "iso3d_mu0.50": [], "iso3d_mu0.85": [], "iso3d_ou1mode_matched": []}

    for tc in tau_c_grid:
        c_arr = (sigma_fixed ** 2) * c_tilde_05
        nu_arr = nu_tilde_05 / tc
        gamma_eff = float(2.0 * (sigma_fixed ** 2) * tc * tau_int_ratio_05)

        # Rate-matched Markovian Lindblad
        mk_z = solve_markovian_lindblad(sys8, H0, H90, [S1z], gamma_eff)
        mk_3d = solve_markovian_lindblad(sys8, H0, H90, S1, gamma_eff)

        # Power-law mu=0.5 z-axis (ADO where fast/moderate, OU-MC everywhere)
        mc_z = solve_colored_ou_mc(H0, H90, P_S, dI, [S1z], c_arr, nu_arr, k_rec=1.0, dt=0.008, T_max=11.0, n_pairs=450, seed=200 + int(tc * 1000))
        ado_z = None
        if tc <= 0.05:
            az0, _, Nz, _ = solve_ado_yield(H0, P_S, P_T, dI, 1.0, 1.0, [S1z], [(c_arr, nu_arr)], max_tier=10, max_ados=1500)
            az90, _, _, _ = solve_ado_yield(H90, P_S, P_T, dI, 1.0, 1.0, [S1z], [(c_arr, nu_arr)], max_tier=10, max_ados=1500)
            ado_z = {"N_ado": Nz, "Phi_S_0": az0, "Phi_S_90": az90, "signed_anisotropy": az0 - az90}

        protocol_A["z_axis_mu0.50"].append({
            "tau_c": tc,
            "tau_int": tc * tau_int_ratio_05,
            "gamma_eff": gamma_eff,
            "markovian": mk_z,
            "ado": ado_z,
            "ou_mc": mc_z,
        })

        # Power-law mu=0.5 3D isotropic
        mc_3d = solve_colored_ou_mc(H0, H90, P_S, dI, S1, c_arr, nu_arr, k_rec=1.0, dt=0.008, T_max=11.0, n_pairs=350, seed=300 + int(tc * 1000))
        ado_3d = None
        if tc <= 0.005:
            a30, _, N3, _ = solve_ado_yield(H0, P_S, P_T, dI, 1.0, 1.0, S1, [(c_arr, nu_arr)] * 3, max_tier=6, max_ados=1800)
            a390, _, _, _ = solve_ado_yield(H90, P_S, P_T, dI, 1.0, 1.0, S1, [(c_arr, nu_arr)] * 3, max_tier=6, max_ados=1800)
            ado_3d = {"N_ado": N3, "Phi_S_0": a30, "Phi_S_90": a390, "signed_anisotropy": a30 - a390}

        enh_vs_mark = abs(mc_3d["signed_anisotropy"]) / max(abs(mk_3d["signed_anisotropy"]), 1e-30)
        protocol_A["iso3d_mu0.50"].append({
            "tau_c": tc,
            "tau_int": tc * tau_int_ratio_05,
            "gamma_eff": gamma_eff,
            "markovian": mk_3d,
            "ado": ado_3d,
            "ou_mc": mc_3d,
            "enhancement_vs_rate_matched_Markov": enh_vs_mark,
        })

        # Single-mode exponential OU matched at IDENTICAL (sigma, tau_int, gamma_eff)
        tau_int = tc * tau_int_ratio_05
        mc_ou1 = solve_colored_ou_mc(
            H0, H90, P_S, dI, S1,
            np.array([sigma_fixed ** 2]), np.array([1.0 / tau_int]),
            k_rec=1.0, dt=0.008, T_max=11.0, n_pairs=300, seed=400 + int(tc * 1000)
        )
        protocol_A["iso3d_ou1mode_matched"].append({
            "tau_c_equiv": tc,
            "tau_int": tau_int,
            "gamma_eff": gamma_eff,
            "ou_mc": mc_ou1,
        })

        # Power-law mu=0.85 3D isotropic on subset of tau_c
        c_arr85 = (sigma_fixed ** 2) * c_tilde_085
        nu_arr85 = nu_tilde_085 / tc
        gamma_eff85 = float(2.0 * (sigma_fixed ** 2) * tc * tau_int_ratio_085)
        mk_3d_85 = solve_markovian_lindblad(sys8, H0, H90, S1, gamma_eff85)
        mc_3d_85 = solve_colored_ou_mc(H0, H90, P_S, dI, S1, c_arr85, nu_arr85, k_rec=1.0, dt=0.008, T_max=11.0, n_pairs=300, seed=500 + int(tc * 1000))
        protocol_A["iso3d_mu0.85"].append({
            "tau_c": tc,
            "tau_int": tc * tau_int_ratio_085,
            "gamma_eff": gamma_eff85,
            "markovian": mk_3d_85,
            "ou_mc": mc_3d_85,
            "enhancement_vs_rate_matched_Markov": abs(mc_3d_85["signed_anisotropy"]) / max(abs(mk_3d_85["signed_anisotropy"]), 1e-30),
        })

        print(
            f"ProtA tau_c={tc:6.3f} | g_eff={gamma_eff:8.2f} | "
            f"3D-PL(0.5)={mc_3d['signed_anisotropy']:+.4f}+/-{mc_3d['signed_anisotropy_se']:.4f} | "
            f"3D-OU1={mc_ou1['signed_anisotropy']:+.4f} | "
            f"3D-Markov={mk_3d['signed_anisotropy']:+.2e} | enh={enh_vs_mark:.2e}"
        )

    # ------------------------------------------------------------------
    # 4. Protocol B: Fixed Integrated Rate gamma_eff = 10.0 across tau_c
    # ------------------------------------------------------------------
    gamma_fixed = 10.0
    mk_ref_g10_3d = solve_markovian_lindblad(sys8, H0, H90, S1, gamma_fixed)
    mk_ref_g10_z = solve_markovian_lindblad(sys8, H0, H90, [S1z], gamma_fixed)
    protocol_B = {
        "gamma_eff": gamma_fixed,
        "markovian_3d": mk_ref_g10_3d,
        "markovian_z": mk_ref_g10_z,
        "records": [],
    }
    for tc in [0.001, 0.005, 0.02, 0.1, 0.5, 2.0, 10.0]:
        sigma_tc = np.sqrt(gamma_fixed / (2.0 * tc * tau_int_ratio_05))
        c_arr = (sigma_tc ** 2) * c_tilde_05
        nu_arr = nu_tilde_05 / tc
        mc_3d = solve_colored_ou_mc(H0, H90, P_S, dI, S1, c_arr, nu_arr, k_rec=1.0, dt=0.008, T_max=11.0, n_pairs=350, seed=600 + int(tc * 1000))
        enh = abs(mc_3d["signed_anisotropy"]) / abs(mk_ref_g10_3d["signed_anisotropy"])
        protocol_B["records"].append({
            "tau_c": tc,
            "sigma": float(sigma_tc),
            "gamma_eff": gamma_fixed,
            "iso3d_ou_mc": mc_3d,
            "enhancement_vs_Markov_g10": float(enh),
        })
        print(
            f"ProtB (gamma_eff=10) tau_c={tc:6.3f}, sig={sigma_tc:6.3f} | "
            f"3D-PL={mc_3d['signed_anisotropy']:+.5f} +/- {mc_3d['signed_anisotropy_se']:.5f} "
            f"(Markov={mk_ref_g10_3d['signed_anisotropy']:+.2e}, enh={enh:.1f}x)"
        )

    # ------------------------------------------------------------------
    # 5. Protocol C: Coupling-Strength Sweep sigma at fixed tau_c = 0.2
    # ------------------------------------------------------------------
    tc_sweep = 0.2
    sigmas = [0.3, 0.7, 1.5, 3.0, 6.0, 12.0, 24.0]
    protocol_C = {"tau_c": tc_sweep, "mu": 0.50, "records": []}
    for sig in sigmas:
        c_arr = (sig ** 2) * c_tilde_05
        nu_arr = nu_tilde_05 / tc_sweep
        g_eff = float(2.0 * (sig ** 2) * tc_sweep * tau_int_ratio_05)
        mk_3d = solve_markovian_lindblad(sys8, H0, H90, S1, g_eff)
        mc_z = solve_colored_ou_mc(H0, H90, P_S, dI, [S1z], c_arr, nu_arr, k_rec=1.0, dt=0.008, T_max=10.0, n_pairs=350, seed=700 + int(sig * 10))
        mc_3d = solve_colored_ou_mc(H0, H90, P_S, dI, S1, c_arr, nu_arr, k_rec=1.0, dt=0.008, T_max=10.0, n_pairs=350, seed=800 + int(sig * 10))
        protocol_C["records"].append({
            "sigma": sig,
            "gamma_eff": g_eff,
            "z_axis_ou_mc": mc_z,
            "iso3d_ou_mc": mc_3d,
            "iso3d_markovian": mk_3d,
            "enhancement_vs_rate_matched_Markov": abs(mc_3d["signed_anisotropy"]) / max(abs(mk_3d["signed_anisotropy"]), 1e-30),
        })
        print(
            f"ProtC (tau_c=0.2) sig={sig:4.1f}, xi_eff={g_eff:8.1f} | "
            f"z-PL={mc_z['signed_anisotropy']:+.5f} | "
            f"3D-PL={mc_3d['signed_anisotropy']:+.5f}+/-{mc_3d['signed_anisotropy_se']:.5f} | "
            f"3D-Mark={mk_3d['signed_anisotropy']:+.2e}"
        )

    # Fit sigma-scaling exponent on Protocol C (last 4 points sigma in [3, 24])
    hi_c = [r for r in protocol_C["records"] if r["sigma"] >= 3.0 and abs(r["iso3d_ou_mc"]["signed_anisotropy"]) > 2 * r["iso3d_ou_mc"]["signed_anisotropy_se"]]
    if len(hi_c) >= 2:
        lsig = np.log([r["sigma"] for r in hi_c])
        lval = np.log([abs(r["iso3d_ou_mc"]["signed_anisotropy"]) for r in hi_c])
        sigma_slope = float(-np.polyfit(lsig, lval, 1)[0])
        xi_slope = float(-np.polyfit(np.log([r["gamma_eff"] for r in hi_c]), lval, 1)[0])
    else:
        sigma_slope, xi_slope = None, None
    protocol_C["iso3d_sigma_slope_high"] = sigma_slope
    protocol_C["iso3d_xi_eff_slope_high"] = xi_slope
    if sigma_slope is not None:
        print(f"Protocol C high-sigma 3D-iso scaling: |dPhi| ~ sigma^(-{sigma_slope:.3f}) ~ xi_eff^(-{xi_slope:.3f})")
    else:
        print("Protocol C high-sigma 3D-iso scaling (tau_c=0.2, sigma>=3): unresolved (insufficient >2*SE points; see verify_05 slow tau_c=5.0)")

    out = {
        "prony_fits": prony_fits,
        "ado_convergence_audit": ado_audit,
        "protocol_A_fixed_sigma": protocol_A,
        "protocol_B_fixed_gamma_eff": protocol_B,
        "protocol_C_sigma_sweep": protocol_C,
        "runtime_seconds": time.time() - t_start,
    }
    out_path = DATA_DIR / "verify_03_microscopic_ado_and_mc.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, allow_nan=False)
    print(f"Script 03 completed in {out['runtime_seconds']:.1f}s -> {out_path}")


if __name__ == "__main__":
    main()
