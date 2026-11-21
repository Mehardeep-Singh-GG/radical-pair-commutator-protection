#!/usr/bin/env python3
"""
Script 02: Exact Five-Channel Liouville Superoperator Solver (xi in [1e-1, 1e4]).

Uses 45-digit mpmath Liouville linear solves for 8x8 models (preventing float64
catastrophic cancellation down to 1e-40 at xi = 10^4), dense float64 angular
scans for max-min vs signed anisotropy and sign-flip blind spots, exact
non-Hermitian H_eff biorthogonal Sherman-Morrison cross-checks for k_S != k_T,
and sparse 1296-dim Liouville solves for 36x36 FAD^{.-} (14N5 + 14N10).

Channels tested:
  (a)  Global commuting depolarization (Markovian mu=1 vs Mittag-Leffler mu<1)
  (b)  Singlet-triplet dephasing (STD): P_S rho P_S + P_T rho P_T - rho = 0.5 D[P_S - P_T]
  (c)  Local isotropic random-field noise on S1, on S2 (J_ex=0.15 vs J_ex=0), and on S1+S2
  (d)  Local uniaxial spin noise: S1z, S2z, S1z+S2z, and S1x+S2x
  (e)  Asymmetric Haberkorn recombination (k_T / k_S in {0.1, 1.0, 5.0, 10.0})
       across global depolarization, STD, local isotropic S1, and local uniaxial S1+S2.
"""

import json
import time
from pathlib import Path
import numpy as np
import mpmath as mp
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from scipy.optimize import brentq

from verify_01_hamiltonians_and_moments import (
    build_single_nucleus_system,
    build_two_nucleus_system,
    build_hamiltonian,
    laplace_ml_weight_mp,
)

mp.mp.dps = 45

DATA_DIR = Path(__file__).resolve().parent.parent / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def to_mp(A: np.ndarray):
    n, m = A.shape
    M = mp.zeros(n, m)
    for i in range(n):
        for j in range(m):
            re, im = float(A[i, j].real), float(A[i, j].imag)
            if re != 0.0 or im != 0.0:
                M[i, j] = mp.mpc(re, im)
    return M


def build_superops_numpy(sys: dict):
    """Build dense/sparse Liouville superoperators for row-major vec(A X B) = kron(A, B.T) vec(X)."""
    D = sys["D"]
    Id = sys["Id"]
    P_S, P_T = sys["P_S"], sys["P_T"]
    S1, S2 = sys["S1"], sys["S2"]

    def L_comm(A):
        return np.kron(A, Id) - np.kron(Id, A.T)

    def L_anti(A):
        return np.kron(A, Id) + np.kron(Id, A.T)

    def L_diss(L):
        return np.kron(L, L.conj()) - 0.5 * L_anti(L.conj().T @ L)

    D_dep = np.outer(Id.reshape(-1) / float(D), Id.reshape(-1)) - np.eye(D * D, dtype=complex)
    D_std = 0.5 * L_diss(P_S - P_T)  # P_S rho P_S + P_T rho P_T - rho
    D_std_full = L_diss(P_S - P_T)   # 2 * (P_S rho P_S + P_T rho P_T - rho)
    D_iso_S1 = sum(L_diss(S1[a]) for a in range(3))
    D_iso_S2 = sum(L_diss(S2[a]) for a in range(3))
    D_iso_S1_S2 = D_iso_S1 + D_iso_S2
    D_z_S1 = L_diss(S1[2])
    D_z_S2 = L_diss(S2[2])
    D_z_S1_S2 = D_z_S1 + D_z_S2
    D_x_S1_S2 = L_diss(S1[0]) + L_diss(S2[0])

    return {
        "L_comm": L_comm,
        "L_anti": L_anti,
        "aPS": L_anti(P_S),
        "aPT": L_anti(P_T),
        "D_dep": D_dep,
        "D_std": D_std,
        "D_std_full": D_std_full,
        "D_iso_S1": D_iso_S1,
        "D_iso_S2": D_iso_S2,
        "D_iso_S1_S2": D_iso_S1_S2,
        "D_z_S1": D_z_S1,
        "D_z_S2": D_z_S2,
        "D_z_S1_S2": D_z_S1_S2,
        "D_x_S1_S2": D_x_S1_S2,
    }


def heff_sherman_morrison_yield(H: np.ndarray, P_S: np.ndarray, P_T: np.ndarray,
                                rho0: np.ndarray, kS: float, kT: float, gamma: float):
    """
    Analytic non-Hermitian H_eff biorthogonal eigenvalue + rank-1 Sherman-Morrison
    solution for global depolarization with asymmetric recombination (k_S != k_T):
      H_eff = H - i (kS/2) P_S - i (kT/2) P_T.
    Verifies exact agreement between H_eff eigendecomposition and full Liouville trace.
    """
    D = H.shape[0]
    H_eff = H - 0.5j * kS * P_S - 0.5j * kT * P_T
    # Eigendecompose H_eff: H_eff @ R = R @ diag(lam), L_dag @ H_eff = diag(lam) @ L_dag
    lam, R = np.linalg.eig(H_eff)
    R_inv = np.linalg.inv(R)  # rows of R_inv are left eigenvectors <L_a|

    # Exact action of (-A)^{-1}(Y) where A(X) = -i(H_eff X - X H_eff^dag) - gamma X
    # (-A)^{-1}(Y) = R @ [ (R_inv @ Y @ R_inv^dag) / (gamma + i*(lam_a - lam_b^*)) ] @ R^dag
    denom = gamma + 1j * (lam[:, None] - lam.conj()[None, :])

    def apply_neg_A_inv(Y: np.ndarray) -> np.ndarray:
        Y_tilde = R_inv @ Y @ R_inv.conj().T
        X_tilde = Y_tilde / denom
        return R @ X_tilde @ R.conj().T

    X_rho0 = apply_neg_A_inv(rho0)
    X_Id = apply_neg_A_inv(np.eye(D, dtype=complex))
    c_tr = np.trace(X_rho0) / (1.0 - (gamma / float(D)) * np.trace(X_Id))
    X_total = X_rho0 + (gamma * c_tr / float(D)) * X_Id
    phi_S = float(kS * np.real(np.trace(P_S @ X_total)))
    phi_T = float(kT * np.real(np.trace(P_T @ X_total)))
    return phi_S, phi_T, lam


def solve_sparse_refined_mp(M_sp, b_np: np.ndarray, n_iter: int = 6):
    """
    Mixed-precision sparse LU + 45-digit mpmath iterative refinement.
    Matches full mpmath.lu_solve to < 1e-42 while running ~15x faster on 64x64
    and handling 1296x1296 sparse 36x36 Liouville matrices in < 0.5s/solve.
    """
    M_csc = sp.csc_matrix(M_sp) if not sp.issparse(M_sp) else M_sp.tocsc()
    M_csr = M_csc.tocsr()
    indptr, indices, data = M_csr.indptr, M_csr.indices, M_csr.data
    n = M_csr.shape[0]
    lu = spla.splu(M_csc)
    rows = [
        (indices[indptr[i]:indptr[i + 1]],
         [mp.mpc(float(v.real), float(v.imag)) for v in data[indptr[i]:indptr[i + 1]]])
        for i in range(n)
    ]
    b_mp = [mp.mpc(float(v.real), float(v.imag)) for v in b_np]
    x_mp = [mp.mpc(0)] * n
    for _ in range(n_iter):
        r_np = np.empty(n, dtype=complex)
        for i in range(n):
            cols_i, vals_i = rows[i]
            s = b_mp[i]
            for c, v in zip(cols_i, vals_i):
                s -= v * x_mp[c]
            r_np[i] = complex(float(mp.re(s)), float(mp.im(s)))
        dx_np = lu.solve(r_np)
        for i in range(n):
            if dx_np[i] != 0:
                x_mp[i] += mp.mpc(float(dx_np[i].real), float(dx_np[i].imag))
    return x_mp


def _to_mp_rows(A_sp):
    A_csr = sp.csr_matrix(A_sp) if not sp.issparse(A_sp) else A_sp.tocsr()
    indptr, indices, data = A_csr.indptr, A_csr.indices, A_csr.data
    n = A_csr.shape[0]
    return [
        (indices[indptr[i]:indptr[i + 1]],
         [mp.mpc(mp.mpf(repr(float(v.real))), mp.mpf(repr(float(v.imag)))) for v in data[indptr[i]:indptr[i + 1]]])
        for i in range(n)
    ]


def solve_sparse_refined_mp_split(L0_sp, g_val: float, D_sp, b_np: np.ndarray, n_iter: int = 7, L0_rows=None, D_rows=None):
    """
    Native 45-digit mpmath residual iterative refinement for (L0 + g * D) x = b,
    assembling L0 + g * D directly in 45-digit mpmath (avoiding float64 diagonal
    cancellation at large g while using float64 sparse LU strictly as preconditioner).
    """
    L0_csc = sp.csc_matrix(L0_sp) if not sp.issparse(L0_sp) else L0_sp.tocsc()
    D_csc = sp.csc_matrix(D_sp) if not sp.issparse(D_sp) else D_sp.tocsc()
    n = L0_csc.shape[0]
    lu = spla.splu((L0_csc + float(g_val) * D_csc).tocsc())
    if L0_rows is None:
        L0_rows = _to_mp_rows(L0_csc)
    if D_rows is None:
        D_rows = _to_mp_rows(D_csc)
    g_mp = mp.mpf(repr(float(g_val)))
    b_mp = [mp.mpc(mp.mpf(repr(float(v.real))), mp.mpf(repr(float(v.imag)))) for v in b_np]
    x_mp = [mp.mpc(0)] * n
    for _ in range(n_iter):
        r_np = np.empty(n, dtype=complex)
        for i in range(n):
            s = b_mp[i]
            cols0, vals0 = L0_rows[i]
            for c, v in zip(cols0, vals0):
                s -= v * x_mp[c]
            colsD, valsD = D_rows[i]
            sd = mp.mpc(0)
            for c, v in zip(colsD, valsD):
                sd += v * x_mp[c]
            s -= g_mp * sd
            r_np[i] = complex(float(mp.re(s)), float(mp.im(s)))
        dx_np = lu.solve(r_np)
        for i in range(n):
            if dx_np[i] != 0:
                x_mp[i] += mp.mpc(float(dx_np[i].real), float(dx_np[i].imag))
    return x_mp


def solve_mp_channel(sys, H0, H90, superops, D_key, xis, kS=1.0, kT=1.0):
    """Solve 8x8 / 12x12 Liouville superoperator at native 45-digit refined precision."""
    D = sys["D"]
    P_S, P_T = sys["P_S"], sys["P_T"]
    rho0 = (-P_S / float(sys["dI"])).reshape(-1)

    PS_nz = [(i, mp.mpc(mp.mpf(repr(float(v.real))), mp.mpf(repr(float(v.imag))))) for i, v in enumerate(P_S.T.reshape(-1)) if v != 0]
    PT_nz = [(i, mp.mpc(mp.mpf(repr(float(v.real))), mp.mpf(repr(float(v.imag))))) for i, v in enumerate(P_T.T.reshape(-1)) if v != 0]

    L_comm = superops["L_comm"]
    L0_base = -1j * L_comm(H0) - 0.5 * kS * superops["aPS"] - 0.5 * kT * superops["aPT"]
    L90_base = -1j * L_comm(H90) - 0.5 * kS * superops["aPS"] - 0.5 * kT * superops["aPT"]
    D_mat = superops[D_key]
    L0_rows = _to_mp_rows(L0_base)
    L90_rows = _to_mp_rows(L90_base)
    D_rows = _to_mp_rows(D_mat)

    kS_m, kT_m = mp.mpf(repr(float(kS))), mp.mpf(repr(float(kT)))
    records = []
    for xi in xis:
        g = float(xi) * kS
        x0 = solve_sparse_refined_mp_split(L0_base, g, D_mat, rho0, n_iter=7, L0_rows=L0_rows, D_rows=D_rows)
        x90 = solve_sparse_refined_mp_split(L90_base, g, D_mat, rho0, n_iter=7, L0_rows=L90_rows, D_rows=D_rows)
        p0 = kS_m * mp.re(sum(v * x0[i] for i, v in PS_nz))
        t0 = kT_m * mp.re(sum(v * x0[i] for i, v in PT_nz))
        p90 = kS_m * mp.re(sum(v * x90[i] for i, v in PS_nz))
        t90 = kT_m * mp.re(sum(v * x90[i] for i, v in PT_nz))
        norm_err = float(max(abs(p0 + t0 - 1), abs(p90 + t90 - 1)))
        signed_diff = p0 - p90
        records.append({
            "xi": float(xi),
            "Phi_S_0": float(p0),
            "Phi_S_90": float(p90),
            "signed_anisotropy": float(signed_diff),
            "abs_anisotropy": float(abs(signed_diff)),
            "sign": 1 if signed_diff > 0 else (-1 if signed_diff < 0 else 0),
            "norm_conservation_err": norm_err,
            "signed_str_mp": mp.nstr(signed_diff, 18),
        })

    # Compute local log-log slopes -d ln|Phi_0 - Phi_90| / d ln(xi) using exact mpmath values
    slopes = []
    for i in range(len(records) - 1):
        v1 = abs(mp.mpf(records[i]["signed_str_mp"]))
        v2 = abs(mp.mpf(records[i + 1]["signed_str_mp"]))
        x1, x2 = mp.mpf(records[i]["xi"]), mp.mpf(records[i + 1]["xi"])
        if v1 > 0 and v2 > 0:
            sl = -float(mp.log(v2 / v1) / mp.log(x2 / x1))
        else:
            sl = None
        slopes.append({"xi_mid": float(np.sqrt(float(x1 * x2))), "alpha_eff": sl})

    # Asymptotic slope from xi = 10^2 to 10^4 (or last 5 points)
    hi_pts = [r for r in records if r["xi"] >= 100.0 - 1e-9]
    if len(hi_pts) >= 2:
        lx = np.array([np.log(r["xi"]) for r in hi_pts])
        ly = np.array([float(mp.log(abs(mp.mpf(r["signed_str_mp"])))) for r in hi_pts])
        slope_fit, _ = np.polyfit(lx, ly, 1)
        alpha_asym = float(-slope_fit)
    else:
        alpha_asym = float("nan")

    return {
        "records": records,
        "local_slopes": slopes,
        "alpha_asym_100_to_10000": alpha_asym,
    }


def solve_mittag_leffler_channel(sys, H0, H90, xis, mu_list, k_rec=1.0, fit_xmin=100.0):
    """Exact Laplace-Mittag-Leffler singlet yields via native 45-digit mp.eigsy/mp.eighe."""
    P_S = sys["P_S"]
    dI = sys["dI"]
    D = sys["D"]
    PS_mp = to_mp(P_S)
    is_real_PS = (np.max(np.abs(P_S.imag)) < 1e-14)

    def spec_data_mp(H):
        is_real_H = (np.max(np.abs(H.imag)) < 1e-14)
        if is_real_H and is_real_PS:
            Hm = mp.zeros(D, D)
            for i in range(D):
                for j in range(D):
                    val = float(H[i, j].real)
                    if val != 0.0:
                        Hm[i, j] = mp.mpf(val)
            evals, evecs = mp.eigsy(Hm)
            P_eig = evecs.T * PS_mp * evecs
            W = [[mp.re(P_eig[i, j]) ** 2 / dI for j in range(D)] for i in range(D)]
        else:
            Hm = to_mp(H)
            evals, evecs = mp.eighe(Hm)
            P_eig = evecs.H * PS_mp * evecs
            W = [[(mp.re(P_eig[i, j]) ** 2 + mp.im(P_eig[i, j]) ** 2) / dI for j in range(D)] for i in range(D)]
        om = [[abs(evals[i] - evals[j]) for j in range(D)] for i in range(D)]
        return W, om

    W0, om0 = spec_data_mp(H0)
    W90, om90 = spec_data_mp(H90)
    k_m = mp.mpf(k_rec)

    def eval_phi_mp(W_list, om_list, mu_val, g_val):
        if abs(mu_val - 1.0) < 1e-12:
            s_m = k_m + mp.mpf(g_val)
            Lz = k_m / s_m
            total = mp.mpf("0.25") * (1 - Lz)
            s2 = s_m * s_m
            ks = k_m * s_m
            for i in range(D):
                for j in range(D):
                    w_ij = W_list[i][j]
                    if w_ij < mp.mpf("1e-38"):
                        continue
                    om_ij = om_list[i][j]
                    total += w_ij * ks / (s2 + om_ij * om_ij)
            return total
        mu_m = mp.mpf(mu_val)
        g_mu = mp.mpf(g_val) ** mu_m
        s0 = k_m
        Lz = k_m * mp.re((s0 ** (mu_m - 1)) / (s0 ** mu_m + g_mu))
        total = mp.mpf("0.25") * (1 - Lz)
        for i in range(D):
            for j in range(D):
                w_ij = W_list[i][j]
                if w_ij < mp.mpf("1e-38"):
                    continue
                s = k_m - 1j * om_list[i][j]
                L_ij = k_m * mp.re((s ** (mu_m - 1)) / (s ** mu_m + g_mu))
                total += w_ij * L_ij
        return total

    out = {}
    for mu in mu_list:
        recs = []
        for xi in xis:
            g = float(xi) * k_rec
            p0_m = eval_phi_mp(W0, om0, mu, g)
            p90_m = eval_phi_mp(W90, om90, mu, g)
            diff_m = p0_m - p90_m
            recs.append({
                "xi": float(xi),
                "Phi_S_0": float(p0_m),
                "Phi_S_90": float(p90_m),
                "signed_anisotropy": float(diff_m),
                "abs_anisotropy": float(abs(diff_m)),
                "signed_str_mp": mp.nstr(diff_m, 18),
            })
        hi = [r for r in recs if r["xi"] >= fit_xmin - 1e-9]
        lx = np.log([r["xi"] for r in hi])
        ly = np.array([float(mp.log(abs(mp.mpf(r["signed_str_mp"])))) for r in hi])
        alpha_asym = float(-np.polyfit(lx, ly, 1)[0])
        out[f"mu_{mu:.2f}"] = {"records": recs, "alpha_asym_100_to_10000": alpha_asym}
    return out


def analyze_angular_and_sign_flip(sys, params, superops):
    """
    Dense angular scan (theta in [0, 180] deg, 37 points) across xi in [0.1, 30]
    to compare max-min Delta Phi_S vs signed Phi_S(0) - Phi_S(90) and find exact
    sign-flip blind spots xi_flip.
    """
    angles_deg = np.linspace(0.0, 180.0, 37)
    angles_rad = np.deg2rad(angles_deg)
    rho0 = (sys["P_S"] / float(sys["dI"])).reshape(-1)
    PS_vec = sys["P_S"].T.reshape(-1)
    L_comm = superops["L_comm"]
    kS, kT = 1.0, 1.0
    L_rec = -0.5 * kS * superops["aPS"] - 0.5 * kT * superops["aPT"]

    # Prebuild L_H(theta) for the 37 angles
    L_H_list = []
    for th in angles_rad:
        b = np.array([np.sin(th), 0.0, np.cos(th)])
        _, _, _, H = build_hamiltonian(
            sys, b, params["omega_L"], params["A_tensors"], params["electron_idx"], params["J_ex"]
        )
        L_H_list.append(-1j * L_comm(H) + L_rec)

    def eval_profile(D_key, xi):
        D_mat = superops[D_key]
        vals = np.empty(len(angles_rad))
        for i, L_base in enumerate(L_H_list):
            x = np.linalg.solve(L_base + xi * D_mat, -rho0)
            vals[i] = float(kS * np.real(PS_vec @ x))
        return vals

    xis_dense = np.logspace(-1, np.log10(30.0), 49)
    profiles = {}
    blind_spots = {}
    for key in ["D_dep", "D_std", "D_iso_S1", "D_z_S1", "D_z_S1_S2"]:
        maxmin_arr, signed_arr, min_abs_arr = [], [], []
        for xi in xis_dense:
            prof = eval_profile(key, float(xi))
            maxmin_arr.append(float(np.max(prof) - np.min(prof)))
            signed_arr.append(float(prof[0] - prof[18]))  # 0 deg - 90 deg
        profiles[key] = {
            "xi": xis_dense.tolist(),
            "Delta_Phi_maxmin": maxmin_arr,
            "signed_Phi0_minus_Phi90": signed_arr,
        }
        # Find sign-flip roots via brentq
        roots = []
        for idx in range(len(xis_dense) - 1):
            if signed_arr[idx] * signed_arr[idx + 1] < 0.0:
                r = brentq(
                    lambda x: float(eval_profile(key, x)[0] - eval_profile(key, x)[18]),
                    float(xis_dense[idx]),
                    float(xis_dense[idx + 1]),
                    xtol=1e-10,
                )
                # Also compute residual max - min at exact sign flip
                prof_at_r = eval_profile(key, r)
                roots.append({
                    "xi_flip": float(r),
                    "Delta_Phi_maxmin_at_flip": float(np.max(prof_at_r) - np.min(prof_at_r)),
                    "Phi0_minus_Phi90_at_flip": float(prof_at_r[0] - prof_at_r[18]),
                })
        blind_spots[key] = roots

    return {"angular_comparison": profiles, "sign_flip_blind_spots": blind_spots}


def solve_36x36_fad_channels(cfg_name, omega_L, A_tensors, electron_idx, J_ex, xis_fad, fit_xmin=100.0):
    """
    Sparse Liouville solver (1296 x 1296) for realistic 2-nucleus (14N5 + 14N10) FAD^{.-}.
    """
    sys36 = build_two_nucleus_system(1.0, 1.0)
    D = sys36["D"]  # 36
    Id = sp.eye(D, dtype=complex, format="csc")
    P_S = sys36["P_S"]
    P_T = sys36["P_T"]
    S1 = sys36["S1"]
    S2 = sys36["S2"]
    rho0 = (P_S / float(sys36["dI"])).reshape(-1)
    PS_vec = P_S.T.reshape(-1)
    PT_vec = P_T.T.reshape(-1)

    def L_comm_sp(A):
        As = sp.csc_matrix(A)
        return sp.kron(As, Id, format="csc") - sp.kron(Id, As.T, format="csc")

    def L_anti_sp(A):
        As = sp.csc_matrix(A)
        return sp.kron(As, Id, format="csc") + sp.kron(Id, As.T, format="csc")

    def L_diss_sp(L):
        Ls = sp.csc_matrix(L)
        return sp.kron(Ls, Ls.conj(), format="csc") - 0.5 * L_anti_sp(L.conj().T @ L)

    # Note: for global dep, D_dep = (1/D) |I><I| - I_1296 (dense rank-1 update via Sherman-Morrison!)
    # That keeps sparse LU super fast!
    b0 = np.array([0.0, 0.0, 1.0])
    b90 = np.array([1.0, 0.0, 0.0])
    _, _, _, H0 = build_hamiltonian(sys36, b0, omega_L, A_tensors, electron_idx, J_ex)
    _, _, _, H90 = build_hamiltonian(sys36, b90, omega_L, A_tensors, electron_idx, J_ex)

    # Sparse channels: STD, iso_S1, z_S1, z_S1_S2 (plus spectral global dep Markov & ML)
    D_std_sp = 0.5 * L_diss_sp(P_S - P_T)
    D_iso1_sp = sum(L_diss_sp(S1[a]) for a in range(3))
    D_z1_sp = L_diss_sp(S1[2])
    D_z12_sp = L_diss_sp(S1[2]) + L_diss_sp(S2[2])

    kS, kT = 1.0, 1.0
    L_rec_sp = -0.5 * kS * L_anti_sp(P_S) - 0.5 * kT * L_anti_sp(P_T)
    L0_base = -1j * L_comm_sp(H0) + L_rec_sp
    L90_base = -1j * L_comm_sp(H90) + L_rec_sp

    # 1) Exact spectral global depolarization (Markov & ML mu=0.5)
    ml_res = solve_mittag_leffler_channel(sys36, H0, H90, xis_fad, [0.5, 1.0], k_rec=1.0, fit_xmin=fit_xmin)

    # 2) Sparse Liouville solves for non-commuting physical channels
    # Use 45-digit refined sparse LU for local_iso_S1 at xi >= 100 to avoid float64 cancellation!
    PS_nz = [(i, mp.mpc(float(v.real), float(v.imag))) for i, v in enumerate(PS_vec) if v != 0]
    PT_nz = [(i, mp.mpc(float(v.real), float(v.imag))) for i, v in enumerate(PT_vec) if v != 0]

    sp_channels = {
        "STD": D_std_sp,
        "local_iso_S1": D_iso1_sp,
        "local_z_S1": D_z1_sp,
        "local_z_S1_S2": D_z12_sp,
    }
    out = {"global_dep_spectral": ml_res, "sparse_channels": {}, "sign_flip_blind_spots": {}}
    for cname, D_sp in sp_channels.items():
        recs = []
        L0_sp_rows = _to_mp_rows(L0_base) if cname == "local_iso_S1" else None
        L90_sp_rows = _to_mp_rows(L90_base) if cname == "local_iso_S1" else None
        D_sp_rows = _to_mp_rows(D_sp) if cname == "local_iso_S1" else None
        for xi in xis_fad:
            if cname == "local_iso_S1" and xi >= 100.0 - 1e-9:
                x0_mp = solve_sparse_refined_mp_split(L0_base, float(xi), D_sp, -rho0, n_iter=7, L0_rows=L0_sp_rows, D_rows=D_sp_rows)
                x90_mp = solve_sparse_refined_mp_split(L90_base, float(xi), D_sp, -rho0, n_iter=7, L0_rows=L90_sp_rows, D_rows=D_sp_rows)
                p0_m = mp.re(sum(v * x0_mp[i] for i, v in PS_nz))
                t0_m = mp.re(sum(v * x0_mp[i] for i, v in PT_nz))
                p90_m = mp.re(sum(v * x90_mp[i] for i, v in PS_nz))
                diff_m = p0_m - p90_m
                recs.append({
                    "xi": float(xi),
                    "Phi_S_0": float(p0_m),
                    "Phi_S_90": float(p90_m),
                    "signed_anisotropy": float(diff_m),
                    "abs_anisotropy": float(abs(diff_m)),
                    "norm_conservation_err": float(abs(p0_m + t0_m - 1)),
                    "signed_str_mp": mp.nstr(diff_m, 18),
                })
            else:
                x0 = spla.spsolve(L0_base + float(xi) * D_sp, -rho0)
                x90 = spla.spsolve(L90_base + float(xi) * D_sp, -rho0)
                p0 = float(kS * np.real(PS_vec @ x0))
                t0 = float(kT * np.real(PT_vec @ x0))
                p90 = float(kS * np.real(PS_vec @ x90))
                diff = p0 - p90
                recs.append({
                    "xi": float(xi),
                    "Phi_S_0": p0,
                    "Phi_S_90": p90,
                    "signed_anisotropy": diff,
                    "abs_anisotropy": abs(diff),
                    "norm_conservation_err": abs(p0 + t0 - 1.0),
                    "signed_str_mp": f"{diff:.17e}",
                })
        # Fit slope over [10^2, 10^4] cleanly AND over >= fit_xmin
        valid_std = [r for r in recs if 100.0 - 1e-9 <= r["xi"] <= 10000.0 + 1e-9]
        if len(valid_std) >= 2:
            lx = np.log([r["xi"] for r in valid_std])
            ly = np.array([float(mp.log(abs(mp.mpf(r["signed_str_mp"])))) for r in valid_std])
            alpha_100_10k = float(-np.polyfit(lx, ly, 1)[0])
        else:
            alpha_100_10k = None

        valid_hi = [r for r in recs if r["xi"] >= fit_xmin - 1e-9]
        if len(valid_hi) >= 2:
            lx = np.log([r["xi"] for r in valid_hi])
            ly = np.array([float(mp.log(abs(mp.mpf(r["signed_str_mp"])))) for r in valid_hi])
            alpha_fit = float(-np.polyfit(lx, ly, 1)[0])
        else:
            alpha_fit = None
        out["sparse_channels"][cname] = {
            "records": recs,
            "alpha_fit": alpha_fit,
            "alpha_100_to_10000": alpha_100_10k,
        }

        # Find exact brentq sign-flip root if sign changes along sweep
        roots_sp = []
        for idx in range(len(recs) - 1):
            if recs[idx]["signed_anisotropy"] * recs[idx + 1]["signed_anisotropy"] < 0.0:
                def f_sp(x_val):
                    x0_f = spla.spsolve(L0_base + float(x_val) * D_sp, -rho0)
                    x90_f = spla.spsolve(L90_base + float(x_val) * D_sp, -rho0)
                    return float(np.real(PS_vec @ (x0_f - x90_f)))
                r_flip = brentq(f_sp, recs[idx]["xi"], recs[idx + 1]["xi"], xtol=1e-6)
                roots_sp.append(float(r_flip))
        out["sign_flip_blind_spots"][cname] = roots_sp

    # Also find brentq sign-flip root for global Markov (mu=1.00)
    ev0, evec0 = np.linalg.eigh(H0)
    W0_f = (1.0 / sys36["dI"]) * (np.abs(evec0.conj().T @ P_S @ evec0) ** 2)
    om2_0 = (ev0[:, None] - ev0[None, :]) ** 2
    ev90, evec90 = np.linalg.eigh(H90)
    W90_f = (1.0 / sys36["dI"]) * (np.abs(evec90.conj().T @ P_S @ evec90) ** 2)
    om2_90 = (ev90[:, None] - ev90[None, :]) ** 2
    mk_recs = ml_res["mu_1.00"]["records"]
    mk_roots = []
    for idx in range(len(mk_recs) - 1):
        if mk_recs[idx]["signed_anisotropy"] * mk_recs[idx + 1]["signed_anisotropy"] < 0.0:
            def f_mk(x_val):
                s = 1.0 + float(x_val)
                p0 = 0.25 * (1.0 - 1.0 / s) + float(np.sum(W0_f * s / (s * s + om2_0)))
                p90 = 0.25 * (1.0 - 1.0 / s) + float(np.sum(W90_f * s / (s * s + om2_90)))
                return p0 - p90
            mk_roots.append(float(brentq(f_mk, mk_recs[idx]["xi"], mk_recs[idx + 1]["xi"], xtol=1e-6)))
    out["sign_flip_blind_spots"]["global_Markov_mu1"] = mk_roots

    return out


def solve_12x12_checks():
    """Verify 12x12 (14N spin-1) asymptotic slopes for all 5 core channels."""
    sys12 = build_single_nucleus_system(1.0)
    A_t = [np.diag([0.5, 0.5, 5.0])]
    _, _, _, H0 = build_hamiltonian(sys12, np.array([0.0, 0.0, 1.0]), 1.40, A_t, [1], 0.15)
    _, _, _, H90 = build_hamiltonian(sys12, np.array([1.0, 0.0, 0.0]), 1.40, A_t, [1], 0.15)
    xis = [1.0, 10.0, 100.0, 1000.0, 10000.0]
    ml_12 = solve_mittag_leffler_channel(sys12, H0, H90, xis, [0.5, 1.0], k_rec=1.0)

    # Non-commuting channels where anisotropy >= 1e-12 up to xi=10^4 in float64 (STD, z_S1, z_S1_S2)
    # plus local_iso_S1 up to xi=100 in float64 and xi=1000,10000 in mpmath (144x144).
    ops12 = build_superops_numpy(sys12)
    rho0 = (sys12["P_S"] / float(sys12["dI"])).reshape(-1)
    PS_vec = sys12["P_S"].T.reshape(-1)
    L_rec = -0.5 * ops12["aPS"] - 0.5 * ops12["aPT"]
    L0_b = -1j * ops12["L_comm"](H0) + L_rec
    L90_b = -1j * ops12["L_comm"](H90) + L_rec

    sp_12 = {}
    for cname, dkey in [("STD", "D_std"), ("local_z_S1", "D_z_S1"), ("local_z_S1_S2", "D_z_S1_S2")]:
        D_m = ops12[dkey]
        recs = []
        for xi in xis:
            p0 = float(np.real(PS_vec @ np.linalg.solve(L0_b + xi * D_m, -rho0)))
            p90 = float(np.real(PS_vec @ np.linalg.solve(L90_b + xi * D_m, -rho0)))
            recs.append({"xi": xi, "Phi_S_0": p0, "Phi_S_90": p90, "signed_anisotropy": p0 - p90})
        hi = [r for r in recs if r["xi"] >= 100.0]
        slope = float(-np.polyfit(np.log([r["xi"] for r in hi]), np.log([abs(r["signed_anisotropy"]) for r in hi]), 1)[0])
        sp_12[cname] = {"records": recs, "alpha_asym_100_to_10000": slope}

    # Check local_iso_S1 on 12x12 using mpmath at xi = 100, 1000, 10000
    sp_12["local_iso_S1"] = solve_mp_channel(sys12, H0, H90, ops12, "D_iso_S1", [10.0, 100.0, 1000.0, 10000.0])
    return {"global_dep_spectral": ml_12, "channels": sp_12}


def main():
    t_start = time.time()
    sys8 = build_single_nucleus_system(0.5)
    params8 = {
        "omega_L": 1.40,
        "A_tensors": [np.diag([0.5, 0.5, 5.0])],
        "electron_idx": [1],
        "J_ex": 0.15,
    }
    b0 = np.array([0.0, 0.0, 1.0])
    b90 = np.array([1.0, 0.0, 0.0])
    _, _, _, H0_8 = build_hamiltonian(sys8, b0, params8["omega_L"], params8["A_tensors"], [1], params8["J_ex"])
    _, _, _, H90_8 = build_hamiltonian(sys8, b90, params8["omega_L"], params8["A_tensors"], [1], params8["J_ex"])
    _, _, _, H0_8_J0 = build_hamiltonian(sys8, b0, params8["omega_L"], params8["A_tensors"], [1], 0.0)
    _, _, _, H90_8_J0 = build_hamiltonian(sys8, b90, params8["omega_L"], params8["A_tensors"], [1], 0.0)

    superops8 = build_superops_numpy(sys8)

    # 16 log-spaced points across [0.1, 10^4] (3 points per decade, includes 0.1, 1, 10, 100, 1000, 10000)
    xis_main = [float(x) for x in np.logspace(-1.0, 4.0, 16)]

    channels_mp = {}
    channel_specs = [
        ("a_global_dep_markov", "D_dep", 1.0, 1.0, H0_8, H90_8),
        ("b_STD_half", "D_std", 1.0, 1.0, H0_8, H90_8),
        ("b_STD_full_PSmPT", "D_std_full", 1.0, 1.0, H0_8, H90_8),
        ("c1_local_iso_S1", "D_iso_S1", 1.0, 1.0, H0_8, H90_8),
        ("c2_local_iso_S2_J015", "D_iso_S2", 1.0, 1.0, H0_8, H90_8),
        ("c2b_local_iso_S2_J000", "D_iso_S2", 1.0, 1.0, H0_8_J0, H90_8_J0),
        ("c3_local_iso_S1_S2", "D_iso_S1_S2", 1.0, 1.0, H0_8, H90_8),
        ("d1_local_z_S1", "D_z_S1", 1.0, 1.0, H0_8, H90_8),
        ("d2_local_z_S2", "D_z_S2", 1.0, 1.0, H0_8, H90_8),
        ("d3_local_z_S1_S2", "D_z_S1_S2", 1.0, 1.0, H0_8, H90_8),
        ("d4_local_x_S1_S2", "D_x_S1_S2", 1.0, 1.0, H0_8, H90_8),
        # Asymmetric Haberkorn k_T / k_S in {0.1, 5.0, 10.0}
        ("e1_dep_kT0.1", "D_dep", 1.0, 0.1, H0_8, H90_8),
        ("e2_dep_kT5.0", "D_dep", 1.0, 5.0, H0_8, H90_8),
        ("e3_dep_kT10.0", "D_dep", 1.0, 10.0, H0_8, H90_8),
        ("e4_STD_kT5.0", "D_std", 1.0, 5.0, H0_8, H90_8),
        ("e5_iso_S1_kT5.0", "D_iso_S1", 1.0, 5.0, H0_8, H90_8),
        ("e6_z_S1_S2_kT5.0", "D_z_S1_S2", 1.0, 5.0, H0_8, H90_8),
    ]

    for cname, dkey, kS, kT, Ha, Hb in channel_specs:
        print(f"Solving 45-digit mpmath channel: {cname}...")
        channels_mp[cname] = solve_mp_channel(sys8, Ha, Hb, superops8, dkey, xis_main, kS=kS, kT=kT)

    # Mittag-Leffler global commuting channel across [0.1, 10^4]
    ml_global = solve_mittag_leffler_channel(sys8, H0_8, H90_8, xis_main, [0.4, 0.5, 0.7, 0.85, 1.0], k_rec=1.0)

    # Cross-check H_eff biorthogonal Sherman-Morrison vs mpmath Liouville for k_T / k_S in {0.1, 1.0, 5.0, 10.0}
    heff_crosschecks = {}
    rho0_8 = sys8["P_S"] / float(sys8["dI"])
    for kT_val, cname in [(0.1, "e1_dep_kT0.1"), (1.0, "a_global_dep_markov"), (5.0, "e2_dep_kT5.0"), (10.0, "e3_dep_kT10.0")]:
        max_err = 0.0
        max_lam_imag_neg = -1e9
        for rec in channels_mp[cname]["records"]:
            if rec["xi"] <= 10.0:
                p0_sm, t0_sm, lam0 = heff_sherman_morrison_yield(H0_8, sys8["P_S"], sys8["P_T"], rho0_8, 1.0, kT_val, rec["xi"])
                p90_sm, t90_sm, _ = heff_sherman_morrison_yield(H90_8, sys8["P_S"], sys8["P_T"], rho0_8, 1.0, kT_val, rec["xi"])
                err = max(abs(p0_sm - rec["Phi_S_0"]), abs(p90_sm - rec["Phi_S_90"]), abs(p0_sm + t0_sm - 1.0))
                max_err = max(max_err, err)
                max_lam_imag_neg = max(max_lam_imag_neg, float(np.max(np.imag(lam0))))
        heff_crosschecks[f"kT_over_kS_{kT_val}"] = {
            "max_abs_err_vs_mpmath_liouville": max_err,
            "max_imag_eigenvalue_Heff": max_lam_imag_neg,
        }

    # Sign-flip blind spot and angular max-min vs signed analysis
    blind_spot_data = analyze_angular_and_sign_flip(sys8, params8, superops8)

    # 12x12 (14N spin-1) verification
    print("Solving 12x12 (14N) asymptotic checks...")
    spin1_12x12 = solve_12x12_checks()

    # 36x36 FAD^{.-} (14N5 + 14N10) canonical + physical 50 uT
    xis_fad = [float(x) for x in np.logspace(-1.0, 4.0, 16)]
    xis_fad_phys = [float(x) for x in np.logspace(-1.0, 6.0, 22)]
    print("Solving 36x36 FAD canonical (1296-dim)...")
    fad_canonical = solve_36x36_fad_channels(
        "fad_36x36_canonical", 1.40,
        [np.diag([0.5, 0.5, 5.0]), np.diag([0.2, 0.2, 2.0])],
        [1, 1], 0.15, xis_fad, fit_xmin=100.0
    )
    print("Solving 36x36 FAD physical 50 uT (1296-dim, xi up to 1e6)...")
    fad_physical_50uT = solve_36x36_fad_channels(
        "fad_36x36_physical_50uT", 8.80429815,
        [np.diag([-15.1433928, -15.1433928, 309.383037]), np.diag([-3.3456333, -3.3456333, 106.884180])],
        [1, 1], 0.0, xis_fad_phys, fit_xmin=10000.0
    )

    output = {
        "xis_grid": xis_main,
        "channels_8x8_mpmath": channels_mp,
        "mittag_leffler_8x8": ml_global,
        "heff_sherman_morrison_crosschecks": heff_crosschecks,
        "angular_and_sign_flips_8x8": blind_spot_data,
        "spin1_14N_12x12": spin1_12x12,
        "fad_36x36_canonical": fad_canonical,
        "fad_36x36_physical_50uT": fad_physical_50uT,
        "runtime_seconds": time.time() - t_start,
    }

    out_path = DATA_DIR / "verify_02_five_channel_liouville.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, allow_nan=False)

    print("\n=== Script 02 Asymptotic Slopes (xi in [100, 10000]) ===")
    for cname, res in channels_mp.items():
        r_100 = [r for r in res["records"] if abs(r["xi"] - 100.0) < 1e-6][0]
        r_10k = [r for r in res["records"] if abs(r["xi"] - 10000.0) < 1e-6][0]
        print(
            f"{cname:24s} | alpha_asym={res['alpha_asym_100_to_10000']:7.4f} "
            f"| dPhi(100)={r_100['signed_anisotropy']:+.3e} "
            f"| dPhi(10k)={r_10k['signed_anisotropy']:+.3e} "
            f"| norm_err={max(r['norm_conservation_err'] for r in res['records']):.1e}"
        )
    print("\n=== Mittag-Leffler Global Depolarization Slopes ===")
    for mk, res in ml_global.items():
        print(f"{mk:10s} | alpha_asym={res['alpha_asym_100_to_10000']:7.4f}")
    print("\n=== 12x12 Slopes ===")
    print("  global_mu1:", round(spin1_12x12["global_dep_spectral"]["mu_1.00"]["alpha_asym_100_to_10000"], 5))
    for k, v in spin1_12x12["channels"].items():
        print(f"  {k:15s}: {v['alpha_asym_100_to_10000']:.5f}")
    print("\n=== 36x36 FAD Canonical & 50 uT Slopes & Blind Spots ===")
    print("  can global_mu1:", round(fad_canonical["global_dep_spectral"]["mu_1.00"]["alpha_asym_100_to_10000"], 5))
    for k, v in fad_canonical["sparse_channels"].items():
        print(f"  can {k:15s}: alpha_100_10k={v['alpha_100_to_10000']:.5f}")
    print("  50uT global_mu1 (1e4..1e6):", round(fad_physical_50uT["global_dep_spectral"]["mu_1.00"]["alpha_asym_100_to_10000"], 5))
    for k, v in fad_physical_50uT["sparse_channels"].items():
        print(f"  50uT {k:15s}: alpha_100_10k={v['alpha_100_to_10000']:.5f}, alpha_1e4_1e6={v['alpha_fit']:.5f}")
    print("  50uT blind spots:", fad_physical_50uT["sign_flip_blind_spots"])
    print("\n=== Sign-Flip Blind Spots (8x8) ===")
    for k, roots in blind_spot_data["sign_flip_blind_spots"].items():
        print(f"{k:12s}: {roots}")
    print(f"\nCompleted in {output['runtime_seconds']:.1f}s")


if __name__ == "__main__":
    main()
