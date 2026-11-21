#!/usr/bin/env python3
"""
Verification 06:
1. Direct non-commuting 3D-isotropic colored-bath OU-MC simulations on the
   full physical 50 uT 36x36 FAD.- (14N5 + 14N10) radical pair using batched
   exact integrated-OU SU(2) Strang splitting (dt = 0.001 us, T_max = 12.0 us,
   plus a dt = 0.0005 us convergence check), benchmarking 1/f^0.5 (mu = 0.50)
   honestly against both rate-matched Markovian local isotropic S1 (native
   45-digit mpmath assembly) and matched single-mode OU1 at identical (sigma, tau_int).
2. Exact numerical verification of Theorems 1-2 under arbitrary symmetric
   electron-electron dipolar coupling H_dip = sum_{a,b} D_{ab} S_{1a} S_{2b}
   with exact physical point-dipole convention D_{ab} = d(r) (delta_{ab} - 3 r_a r_b),
   d(r) = mu_0 gamma_e^2 hbar / (4 pi r^3) = +50.00 rad/us (D_ZFS = -75.0 rad/us,
   r = 1.870 nm cryptochrome separation, 35 deg tilt) on 36x36 FAD.- and an
   arbitrary non-diagonal traceless symmetric D on 8x8 at theta = 90 deg, phi = 0.4 rad.
"""

import json
import time
from pathlib import Path
import numpy as np
from scipy.linalg import expm
import mpmath as mp

from verify_01_hamiltonians_and_moments import (
    build_single_nucleus_system,
    build_two_nucleus_system,
    build_hamiltonian,
)
from prony_ado_lib import fit_power_law_prony

DATA_DIR = Path(__file__).resolve().parent.parent / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def build_dipolar_operator(sys_dict, D_tensor):
    """Build H_dip = sum_{a,b} D_{ab} S_{1a} S_{2b} on the full Hilbert space."""
    S1 = sys_dict["S1"]
    S2 = sys_dict["S2"]
    H_dip = np.zeros_like(S1[0], dtype=complex)
    for a in range(3):
        for b in range(3):
            if D_tensor[a, b] != 0.0:
                H_dip += D_tensor[a, b] * (S1[a] @ S2[b])
    return H_dip


def verify_dipolar_invariance():
    """Exact verification of dipolar protection across 8x8 and 36x36 FAD 50 uT."""
    results = {}
    comm = lambda X, Y: X @ Y - Y @ X

    # 1. Arbitrary non-diagonal traceless symmetric D on 8x8 with non-diag A at theta = 90 deg, phi = 0.4 rad
    sys8 = build_single_nucleus_system(0.5)
    D_gen = np.array([[1.3, -0.7, 0.4], [-0.7, -0.5, 1.1], [0.4, 1.1, -0.8]], dtype=float)
    H_dip8 = build_dipolar_operator(sys8, D_gen)
    PS8 = sys8["P_S"]
    dI8 = sys8["dI"]

    A_gen = [np.array([[0.5, 0.2, -0.3], [0.1, 0.7, 0.4], [-0.2, 0.3, 5.0]], dtype=float)]
    n0 = np.array([0.0, 0.0, 1.0])
    n1 = np.array([np.cos(0.4), np.sin(0.4), 0.0])  # exact theta = 90 deg, phi = 0.4 rad
    _, _, _, H0 = build_hamiltonian(sys8, n0, 1.4, A_gen, [1], 0.15)
    _, _, _, H1 = build_hamiltonian(sys8, n1, 1.4, A_gen, [1], 0.15)
    H0d, H1d = H0 + H_dip8, H1 + H_dip8

    C1_0, C1_1 = comm(H0d, PS8), comm(H1d, PS8)
    C2_0, C2_1 = comm(H0d, C1_0), comm(H1d, C1_1)
    M2_0 = float(np.real(np.trace(C1_0.conj().T @ C1_0)) / dI8)
    M2_1 = float(np.real(np.trace(C1_1.conj().T @ C1_1)) / dI8)
    M4_0 = float(np.real(np.trace(C2_0.conj().T @ C2_0)) / dI8)
    M4_1 = float(np.real(np.trace(C2_1.conj().T @ C2_1)) / dI8)
    AAT = A_gen[0] @ A_gen[0].T
    pred_M2 = (0.5 * 1.5 / 6.0) * float(np.trace(AAT))
    pred_dM4 = (0.5 * 1.5 / 6.0) * (1.4 ** 2) * float(n0 @ AAT @ n0 - n1 @ AAT @ n1)

    results["canonical_8x8_nondiag_dipolar"] = {
        "theta_deg": 90.0,
        "phi_rad": 0.4,
        "comm_Hdip_PS_norm": float(np.linalg.norm(comm(H_dip8, PS8))),
        "M2_with_dipolar": M2_0,
        "M2_exact_pred": pred_M2,
        "M2_rel_err": abs(M2_0 - pred_M2) / pred_M2,
        "M2_angle_diff": abs(M2_1 - M2_0),
        "M4_0_without_dipolar": float(np.real(np.trace(comm(H0, comm(H0, PS8)).conj().T @ comm(H0, comm(H0, PS8)))) / dI8),
        "M4_0_with_dipolar": M4_0,
        "dM4_with_dipolar": M4_1 - M4_0,
        "dM4_exact_pred": pred_dM4,
        "dM4_rel_err": abs((M4_1 - M4_0) - pred_dM4) / abs(pred_dM4),
    }

    # 2. Physical 50 uT 36x36 FAD.- with realistic cryptochrome point-dipole coupling
    # Exact Eq. (2): D_{ab} = d(r) * (delta_{ab} - 3 r_a r_b), with
    # d(r) = mu_0 gamma_e^2 hbar / (4 pi r^3) = 326.983 rad us^-1 nm^3 / r^3.
    # At r = 1.870 nm (FAD-TrpC separation): d(r) = +50.00 rad/us (D_ZFS = -3/2 d(r) = -75.00 rad/us = -0.426 mT).
    sys36 = build_two_nucleus_system(1.0, 1.0)
    PS36 = sys36["P_S"]
    dI36 = sys36["dI"]
    omega_L = 8.80429815
    A_N5 = np.diag([-15.14339282, -15.14339282, 309.3830370])
    A_N10 = np.diag([-3.3456333, -3.3456333, 106.884180])  # unified with verify_01
    d_dip = 50.0  # rad/us (d(r) > 0, physical point-dipole coupling at r = 1.870 nm)
    r_nm = float((326.983 / d_dip) ** (1.0 / 3.0))
    D_ZFS = -1.5 * d_dip  # -75.0 rad/us = -0.426 mT
    beta = np.deg2rad(35.0)
    u_dip = np.array([np.sin(beta), 0.0, np.cos(beta)])
    D_fad = d_dip * (np.eye(3) - 3.0 * np.outer(u_dip, u_dip))
    H_dip36 = build_dipolar_operator(sys36, D_fad)

    _, _, _, Hf0 = build_hamiltonian(sys36, np.array([0.0, 0.0, 1.0]), omega_L, [A_N5, A_N10], [1, 1], 0.0)
    _, _, _, Hf90 = build_hamiltonian(sys36, np.array([1.0, 0.0, 0.0]), omega_L, [A_N5, A_N10], [1, 1], 0.0)
    Hf0d, Hf90d = Hf0 + H_dip36, Hf90 + H_dip36

    Cf1_0, Cf1_90 = comm(Hf0d, PS36), comm(Hf90d, PS36)
    Cf2_0, Cf2_90 = comm(Hf0d, Cf1_0), comm(Hf90d, Cf1_90)
    Cf2_0_nodip = comm(Hf0, comm(Hf0, PS36))
    M2_f0 = float(np.real(np.trace(Cf1_0.conj().T @ Cf1_0)) / dI36)
    M2_f90 = float(np.real(np.trace(Cf1_90.conj().T @ Cf1_90)) / dI36)
    M4_f0_nodip = float(np.real(np.trace(Cf2_0_nodip.conj().T @ Cf2_0_nodip)) / dI36)
    M4_f0 = float(np.real(np.trace(Cf2_0.conj().T @ Cf2_0)) / dI36)
    M4_f90 = float(np.real(np.trace(Cf2_90.conj().T @ Cf2_90)) / dI36)
    pred_M2_f = (1.0 / 3.0) * float(np.trace(A_N5 @ A_N5.T) + np.trace(A_N10 @ A_N10.T))
    pred_dM4_f = (1.0 / 3.0) * (omega_L ** 2) * (
        (A_N5[2, 2] ** 2 - A_N5[0, 0] ** 2) + (A_N10[2, 2] ** 2 - A_N10[0, 0] ** 2)
    )

    # 45-digit global Markov scaling with dipolar coupling at xi = 1e4, 1e5, 1e6
    mp.mp.dps = 45

    def mp_markov_yield(H_np, PS_np, dI_val, xi_list):
        n = H_np.shape[0]
        H_mp = mp.matrix([[mp.mpf(repr(float(np.real(H_np[i, j])))) for j in range(n)] for i in range(n)])
        PS_mp = mp.matrix([[mp.mpf(repr(float(np.real(PS_np[i, j])))) for j in range(n)] for i in range(n)])
        evals, evecs = mp.eigsy(H_mp, eigvals_only=False)
        P_eig = evecs.T * PS_mp * evecs
        out = {}
        for xi in xi_list:
            s = mp.mpf(1) + mp.mpf(str(xi))
            s2 = s * s
            tot = mp.mpf(0)
            for a in range(n):
                for b in range(n):
                    w = (P_eig[a, b] ** 2) / mp.mpf(dI_val)
                    dw = evals[a] - evals[b]
                    tot += w * s / (s2 + dw * dw)
            out[xi] = mp.mpf("0.25") + tot - mp.mpf("0.25") / s
        return out

    xi_dip = [10000, 100000, 1000000]
    y0_dip = mp_markov_yield(Hf0d, PS36, dI36, xi_dip)
    y90_dip = mp_markov_yield(Hf90d, PS36, dI36, xi_dip)
    dphi_dip = {str(xi): float(y0_dip[xi] - y90_dip[xi]) for xi in xi_dip}
    slope_dip = float(
        (mp.log(abs(y0_dip[10000] - y90_dip[10000])) - mp.log(abs(y0_dip[1000000] - y90_dip[1000000])))
        / (mp.log(mp.mpf(1000000)) - mp.log(mp.mpf(10000)))
    )

    def coh_yield(H_np, PS_np, dI_val):
        ev, U = np.linalg.eigh(H_np)
        Pe = U.conj().T @ PS_np @ U
        W = (np.abs(Pe) ** 2) / dI_val
        dw = ev[:, None] - ev[None, :]
        return float(np.sum(W / (1.0 + dw ** 2)))

    coh_nodip = coh_yield(Hf0, PS36, dI36) - coh_yield(Hf90, PS36, dI36)
    coh_withdip = coh_yield(Hf0d, PS36, dI36) - coh_yield(Hf90d, PS36, dI36)

    results["fad_36x36_50uT_tilted_dipolar"] = {
        "d_dip_rad_per_us": d_dip,
        "D_ZFS_rad_per_us": D_ZFS,
        "r_nm": r_nm,
        "tilt_deg": 35.0,
        "comm_Hdip_PS_norm": float(np.linalg.norm(comm(H_dip36, PS36))),
        "M2_with_dipolar": M2_f0,
        "M2_rel_err": abs(M2_f0 - pred_M2_f) / pred_M2_f,
        "M2_angle_diff": abs(M2_f90 - M2_f0),
        "M4_0_without_dipolar": M4_f0_nodip,
        "M4_0_with_dipolar": M4_f0,
        "dM4_with_dipolar": M4_f90 - M4_f0,
        "dM4_exact_pred": pred_dM4_f,
        "dM4_rel_err": abs((M4_f90 - M4_f0) - pred_dM4_f) / abs(pred_dM4_f),
        "coherent_dPhi_no_dip": coh_nodip,
        "coherent_dPhi_with_dip": coh_withdip,
        "global_markov_dPhi_with_dip": dphi_dip,
        "global_markov_slope_1e4_1e6_with_dip": slope_dip,
        "asymptotic_ratio_at_1e6": float((y0_dip[1000000] - y90_dip[1000000]) / (-mp.mpf(repr(float(pred_dM4_f))) / mp.mpf(1000000) ** 5)),
    }
    return results


def solve_fad50uT_colored_ou_mc(H0, H90, PS, S1_ops, c_arr, nu_arr, dt=0.001, T_max=12.0, n_traj=200, seed=777):
    """
    Fast batched vectorized pure-state OU-MC unraveling for 36x36 FAD.- under
    non-commuting 3D-isotropic local fields H_noise(t) = sum_a B_a(t) S1_a,
    using exact joint-Gaussian step-averaged OU integrals (matching prony_ado_lib.py)
    and exact closed-form SU(2) Strang splitting across all trajectories simultaneously.
    """
    rng = np.random.default_rng(seed)
    D = H0.shape[0]
    dI = 9
    ev_p, U_p = np.linalg.eigh(PS)
    singlet_cols = U_p[:, ev_p > 0.5]  # (36, 9)
    assert singlet_cols.shape == (D, dI)

    U0_half = expm(-0.5j * dt * H0)
    U90_half = expm(-0.5j * dt * H90)
    S1x, S1y, S1z = S1_ops
    Id = np.eye(D, dtype=complex)

    n_steps = int(round(T_max / dt))
    t_grid = np.arange(n_steps + 1) * dt
    w_t = np.exp(-t_grid) * dt
    w_t[0] *= 0.5
    w_t[-1] *= 0.5

    K = len(c_arr)
    phi_ou = np.exp(-nu_arr * dt)
    x_ou = nu_arr * dt
    std_init = np.sqrt(c_arr)
    std_eta = np.sqrt(c_arr * (1.0 - phi_ou ** 2))

    # Exact joint Gaussian statistics for step-averaged field I_dt = (1/dt) int_0^dt eta(s) ds
    mu_I_fac = np.where(x_ou > 1e-6, (1.0 - phi_ou) / x_ou, 1.0 - 0.5 * x_ou + (x_ou ** 2) / 6.0)
    var_I = np.where(
        x_ou > 1e-4,
        c_arr * (2.0 * x_ou - 3.0 + 4.0 * phi_ou - phi_ou ** 2) / (x_ou ** 2),
        (2.0 / 3.0) * c_arr * x_ou,
    )
    cov_eta_I = np.where(
        x_ou > 1e-5,
        c_arr * ((1.0 - phi_ou) ** 2) / x_ou,
        c_arr * x_ou * (1.0 - x_ou),
    )
    coeff_Z1 = np.where(std_eta > 1e-15, cov_eta_I / std_eta, 0.0)
    coeff_Z2 = np.sqrt(np.maximum(var_I - coeff_Z1 ** 2, 0.0))

    # BLAS-optimal batched state layout: (36, n_traj * 9) contiguous for single zgemm calls
    eta = rng.normal(0.0, 1.0, size=(n_traj, 3, K)) * std_init[None, None, :]
    psi0 = np.broadcast_to(singlet_cols[:, None, :], (D, n_traj, dI)).reshape(D, n_traj * dI).copy()
    psi90 = np.broadcast_to(singlet_cols[:, None, :], (D, n_traj, dI)).reshape(D, n_traj * dI).copy()

    y0 = np.full(n_traj, w_t[0], dtype=float)
    y90 = np.full(n_traj, w_t[0], dtype=float)
    S_sing_H = np.ascontiguousarray(singlet_cols.conj().T)  # (9, 36)
    U0_half = np.ascontiguousarray(U0_half)
    U90_half = np.ascontiguousarray(U90_half)

    for step in range(1, n_steps + 1):
        z1 = rng.normal(0.0, 1.0, size=(n_traj, 3, K))
        z2 = rng.normal(0.0, 1.0, size=(n_traj, 3, K))
        # Step-averaged OU field per mode & summed across modes: shape (n_traj, 3)
        b_avg = np.sum(eta * mu_I_fac[None, None, :] + z1 * coeff_Z1[None, None, :] + z2 * coeff_Z2[None, None, :], axis=2)
        eta = eta * phi_ou[None, None, :] + z1 * std_eta[None, None, :]

        # Apply U_half left via Apple Accelerate BLAS zgemm: (36, 36) @ (36, n_traj * 9)
        psi0 = U0_half @ psi0
        psi90 = U90_half @ psi90

        # Exact batched SU(2) exponential exp(-i dt b_avg . S1) on qubit 1 (axis 0 of (2, 18, n_traj, 9))
        r = np.linalg.norm(b_avg, axis=1)  # (n_traj,)
        c_ang = np.cos(0.5 * r * dt)
        s_fac = np.where(r > 1e-14, -1.0j * np.sin(0.5 * r * dt) / np.where(r > 1e-14, r, 1.0), -0.5j * dt)
        m00 = (c_ang + s_fac * b_avg[:, 2])[None, :, None]
        m11 = (c_ang - s_fac * b_avg[:, 2])[None, :, None]
        m01 = (s_fac * (b_avg[:, 0] - 1.0j * b_avg[:, 1]))[None, :, None]
        m10 = (s_fac * (b_avg[:, 0] + 1.0j * b_avg[:, 1]))[None, :, None]

        p0_r = psi0.reshape(2, 18, n_traj, dI)
        n0_0 = m00 * p0_r[0] + m01 * p0_r[1]
        n0_1 = m10 * p0_r[0] + m11 * p0_r[1]
        p0_r[0] = n0_0
        p0_r[1] = n0_1

        p90_r = psi90.reshape(2, 18, n_traj, dI)
        n90_0 = m00 * p90_r[0] + m01 * p90_r[1]
        n90_1 = m10 * p90_r[0] + m11 * p90_r[1]
        p90_r[0] = n90_0
        p90_r[1] = n90_1

        psi0 = U0_half @ psi0
        psi90 = U90_half @ psi90

        ov0 = (S_sing_H @ psi0).reshape(dI, n_traj, dI)
        ov90 = (S_sing_H @ psi90).reshape(dI, n_traj, dI)
        ps0 = np.sum(ov0.real ** 2 + ov0.imag ** 2, axis=(0, 2)) / dI
        ps90 = np.sum(ov90.real ** 2 + ov90.imag ** 2, axis=(0, 2)) / dI

        wt = w_t[step]
        y0 += wt * ps0
        y90 += wt * ps90

    diffs = y0 - y90
    return {
        "n_traj": n_traj,
        "dt": dt,
        "T_max": T_max,
        "Phi_S_0": float(np.mean(y0)),
        "Phi_S_90": float(np.mean(y90)),
        "signed_anisotropy": float(np.mean(diffs)),
        "signed_anisotropy_se": float(np.std(diffs, ddof=1) / np.sqrt(n_traj)),
    }


def _to_mp_rows(A_sp):
    A_csr = A_sp.tocsr()
    indptr, indices, data = A_csr.indptr, A_csr.indices, A_csr.data
    n = A_csr.shape[0]
    return [
        (indices[indptr[i]:indptr[i + 1]],
         [mp.mpc(mp.mpf(repr(float(v.real))), mp.mpf(repr(float(v.imag)))) for v in data[indptr[i]:indptr[i + 1]]])
        for i in range(n)
    ]


def solve_markov_fad50uT_iso_S1(H0, H90, PS, S1_ops, gamma_rate, n_iter=7):
    """Exact native 45-digit iteratively refined sparse 1296-dim Liouville solve for 36x36 FAD 50 uT under local iso S1."""
    import scipy.sparse as sp
    import scipy.sparse.linalg as spla

    mp.mp.dps = 45
    D = H0.shape[0]
    Id = sp.eye(D, format="csc", dtype=complex)
    D_op = sp.csc_matrix((D * D, D * D), dtype=complex)
    for V in S1_ops:
        Vs = sp.csc_matrix(V)
        V2s = Vs @ Vs
        D_op = D_op + sp.kron(Vs, Vs.conj(), format="csc") - 0.5 * (
            sp.kron(V2s, Id, format="csc") + sp.kron(Id, V2s.T, format="csc")
        )
    D_rows = _to_mp_rows(-D_op)
    rho0 = (PS / 9.0).reshape(-1)
    b_mp = [mp.mpc(mp.mpf(repr(float(v.real))), mp.mpf(repr(float(v.imag)))) for v in rho0]
    PS_vec_mp = [mp.mpc(mp.mpf(repr(float(val.real))), mp.mpf(repr(float(val.imag)))) for val in PS.T.reshape(-1)]
    Id2 = sp.eye(D * D, format="csc", dtype=complex)
    g_mp = mp.mpf(repr(float(gamma_rate)))

    def ev_mp(H):
        Hs = sp.csc_matrix(H)
        L0_neg = -(-1j * (sp.kron(Hs, Id, format="csc") - sp.kron(Id, Hs.T, format="csc")) - Id2)
        L0_rows = _to_mp_rows(L0_neg)
        M_f64 = (L0_neg - float(gamma_rate) * D_op).tocsc()
        lu = spla.splu(M_f64)
        n = len(rho0)
        x = [mp.mpc(0)] * n
        for _ in range(n_iter):
            r_np = np.empty(n, dtype=np.complex128)
            for i in range(n):
                s = b_mp[i]
                cols0, vals0 = L0_rows[i]
                for c, v in zip(cols0, vals0):
                    s -= v * x[c]
                colsD, valsD = D_rows[i]
                sd = mp.mpc(0)
                for c, v in zip(colsD, valsD):
                    sd += v * x[c]
                s -= g_mp * sd
                r_np[i] = complex(float(s.real), float(s.imag))
            dx = lu.solve(r_np)
            for i in range(n):
                if dx[i] != 0:
                    x[i] += mp.mpc(float(dx[i].real), float(dx[i].imag))
        return sum(PS_vec_mp[i] * x[i] for i in range(n)).real

    p0 = ev_mp(H0)
    p90 = ev_mp(H90)
    diff = p0 - p90
    return {
        "Phi_S_0": float(p0),
        "Phi_S_90": float(p90),
        "signed_anisotropy": float(diff),
        "signed_str_mp": mp.nstr(diff, 18),
    }


def run_fad50uT_colored_bath():
    sys36 = build_two_nucleus_system(1.0, 1.0)
    PS36 = sys36["P_S"]
    S1 = list(sys36["S1"])
    omega_L = 8.80429815
    A_N5 = np.diag([-15.14339282, -15.14339282, 309.3830370])
    A_N10 = np.diag([-3.3456333, -3.3456333, 106.884180])
    _, _, _, H0 = build_hamiltonian(sys36, np.array([0.0, 0.0, 1.0]), omega_L, [A_N5, A_N10], [1, 1], 0.0)
    _, _, _, H90 = build_hamiltonian(sys36, np.array([1.0, 0.0, 0.0]), omega_L, [A_N5, A_N10], [1, 1], 0.0)

    ev0, U0 = np.linalg.eigh(H0)
    P0 = U0.conj().T @ PS36 @ U0
    W0 = (np.abs(P0) ** 2) / 9.0
    coh0 = float(np.sum(W0 / (1.0 + (ev0[:, None] - ev0[None, :]) ** 2)))

    ev90, U90 = np.linalg.eigh(H90)
    P90 = U90.conj().T @ PS36 @ U90
    W90 = (np.abs(P90) ** 2) / 9.0
    coh90 = float(np.sum(W90 / (1.0 + (ev90[:, None] - ev90[None, :]) ** 2)))

    fit05 = fit_power_law_prony(0.50, u_max=1000.0, K=8)
    c_tilde = fit05["c_tilde"]
    nu_tilde = fit05["nu_tilde"]
    tau_int_ratio = fit05["tau_int_over_tau_c"]

    sigma_val = 5.0
    tau_c_list = [0.001, 0.01, 0.1, 1.0, 10.0]
    rows = []
    for idx, tc in enumerate(tau_c_list):
        c_pl = (sigma_val ** 2) * c_tilde
        nu_pl = nu_tilde / tc
        tau_int = tc * tau_int_ratio
        gamma_eff = float(2.0 * (sigma_val ** 2) * tau_int)

        mk = solve_markov_fad50uT_iso_S1(H0, H90, PS36, S1, gamma_eff)
        pl = solve_fad50uT_colored_ou_mc(H0, H90, PS36, S1, c_pl, nu_pl, dt=0.001, T_max=12.0, n_traj=200, seed=1000 + idx)
        ou1 = solve_fad50uT_colored_ou_mc(
            H0, H90, PS36, S1, np.array([sigma_val ** 2]), np.array([1.0 / tau_int]),
            dt=0.001, T_max=12.0, n_traj=200, seed=2000 + idx
        )
        rows.append({
            "tau_c_us": tc,
            "sigma_rad_per_us": sigma_val,
            "tau_int_us": float(tau_int),
            "gamma_eff_per_us": gamma_eff,
            "markov_iso_S1": mk,
            "powerlaw_mu0.50_ou_mc": pl,
            "single_mode_ou1_matched": ou1,
            "ratio_pl_over_ou1": abs(pl["signed_anisotropy"] / ou1["signed_anisotropy"]) if abs(ou1["signed_anisotropy"]) > 1e-12 else None,
            "ratio_pl_over_markov": abs(pl["signed_anisotropy"] / mk["signed_anisotropy"]) if abs(mk["signed_anisotropy"]) > 1e-15 else None,
        })
        print(
            f"FAD 50uT tc={tc:6.3f} (gamma_eff={gamma_eff:8.2f}): "
            f"Markov={mk['signed_anisotropy']:+.5e} | "
            f"1/f^0.5={pl['signed_anisotropy']:+.5f}+/-{pl['signed_anisotropy_se']:.5f} | "
            f"OU1={ou1['signed_anisotropy']:+.5f}+/-{ou1['signed_anisotropy_se']:.5f}"
        )

    # Dedicated dt-convergence check at the most demanding point (tc = 0.001 us: dt=0.0005 vs dt=0.001)
    c_pl0 = (sigma_val ** 2) * c_tilde
    nu_pl0 = nu_tilde / 0.001
    conv_dt0005 = solve_fad50uT_colored_ou_mc(H0, H90, PS36, S1, c_pl0, nu_pl0, dt=0.0005, T_max=12.0, n_traj=200, seed=3000)
    print(f"dt=0.0005 convergence check at tc=0.001: 1/f^0.5={conv_dt0005['signed_anisotropy']:+.5f}+/-{conv_dt0005['signed_anisotropy_se']:.5f}")

    return {
        "model": "36x36 FAD.- physical 50 uT (14N5 + 14N10)",
        "omega_L_rad_per_us": omega_L,
        "coherent_Phi_S_0": coh0,
        "coherent_Phi_S_90": coh90,
        "coherent_signed_anisotropy": coh0 - coh90,
        "sigma_rad_per_us": sigma_val,
        "prony_tau_int_over_tau_c": float(tau_int_ratio),
        "sweep": rows,
        "dt_convergence_check_tc0.001_dt0.0005": conv_dt0005,
    }


def main():
    t0 = time.time()
    dip = verify_dipolar_invariance()
    print("Dipolar 8x8 dM4 rel err:", dip["canonical_8x8_nondiag_dipolar"]["dM4_rel_err"])
    print("Dipolar 36x36 FAD dM4 rel err:", dip["fad_36x36_50uT_tilted_dipolar"]["dM4_rel_err"])
    print("Dipolar 36x36 FAD M4_0 with dip:", dip["fad_36x36_50uT_tilted_dipolar"]["M4_0_with_dipolar"])
    print("Dipolar 36x36 FAD Markov slope [1e4,1e6]:", dip["fad_36x36_50uT_tilted_dipolar"]["global_markov_slope_1e4_1e6_with_dip"])
    fad_col = run_fad50uT_colored_bath()
    out = {
        "runtime_sec": round(time.time() - t0, 2),
        "dipolar_protection": dip,
        "fad_50uT_colored_bath": fad_col,
    }
    out_path = DATA_DIR / "verify_06_fad50uT_colored_and_dipolar.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, allow_nan=False)
    print(f"Saved strict RFC-8259 JSON: {out_path} ({out['runtime_sec']}s)")


if __name__ == "__main__":
    main()
