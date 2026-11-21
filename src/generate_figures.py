#!/usr/bin/env python3
"""
Generate 4 publication-quality multi-panel vector PDF + 300-DPI PNG figures
for the radical-pair magnetoreception manuscript from deterministic JSON/CSV data in data/.
"""

import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
FIG_DIR = BASE_DIR / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

# Clean publication matplotlib style
plt.rcParams.update({
    "font.family": "serif",
    "mathtext.fontset": "stix",
    "font.size": 9.5,
    "axes.labelsize": 10.5,
    "axes.titlesize": 10.5,
    "legend.fontsize": 8.0,
    "xtick.labelsize": 9.0,
    "ytick.labelsize": 9.0,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.linewidth": 0.85,
    "figure.dpi": 300,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.08,
})

C_MU = {
    0.40: "#1b7837",
    0.50: "#0072B2",
    0.70: "#762a83",
    0.85: "#E69F00",
    1.00: "#D55E00",
}


def load_json(name: str):
    with open(DATA_DIR / name, "r", encoding="utf-8") as f:
        return json.load(f)


def load_csv_dict(name: str):
    path = DATA_DIR / name
    with open(path, "r", encoding="utf-8") as f:
        header = f.readline().strip().split(",")
    arr = np.loadtxt(path, delimiter=",", skiprows=1)
    return {col: arr[:, i] for i, col in enumerate(header)}


def save_fig(fig, stem: str):
    fig.savefig(FIG_DIR / f"{stem}.pdf")
    fig.savefig(FIG_DIR / f"{stem}.png", dpi=300)
    plt.close(fig)
    print(f"Saved {stem}.pdf and {stem}.png")


def add_slope_guide(ax, x0, y0, x1, slope, label, color="#333333", dy_text=1.0):
    """Draw clean power-law reference segment y = y0 * (x/x0)^slope."""
    y1 = y0 * ((x1 / x0) ** slope)
    ax.plot([x0, x1], [y0, y1], color=color, lw=1.0, ls=":", alpha=0.8)
    xm = np.sqrt(x0 * x1)
    ym = np.sqrt(y0 * y1) * dy_text
    ax.text(xm, ym, label, fontsize=8.0, color=color, ha="center", va="center",
            bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.75))


def make_figure1(v1, v2, v4):
    ts = load_csv_dict("pS_time_series_xi3.csv")
    ang = load_csv_dict("angular_profiles_xi3.csv")

    fig, axes = plt.subplots(2, 2, figsize=(11.5, 8.6), constrained_layout=True)

    # Panel (a): Time-domain singlet survival p_S(t; theta=0) at xi=3
    ax = axes[0, 0]
    t = ts["t"]
    ax.plot(t, ts["coherent"], color="#999999", lw=1.0, ls=":", label=r"Coherent ($\gamma=0$)")
    for mu, lbl in [(0.40, r"Global ML ($\mu=0.40$)"), (0.50, r"Global ML ($\mu=0.50$)"),
                    (0.70, r"Global ML ($\mu=0.70$)"), (1.00, r"Global Markov ($\mu=1.00$)")]:
        ax.plot(t, ts[f"global_ML_mu{mu:.2f}"], color=C_MU[mu],
                lw=1.9 if mu in (0.5, 1.0) else 1.4,
                ls="--" if mu == 1.0 else "-", label=lbl)
    ax.plot(t, ts["STD_xi3"], color="#009E73", lw=1.4, ls="-.", label=r"STD ($\xi=3$)")
    ax.plot(t, ts["local_z_S1_xi3"], color="#CC79A7", lw=1.5, ls=(0, (3, 1, 1, 1)), label=r"Uniaxial $S_{1z}$ ($\xi=3$)")
    ax.axhline(0.25, color="k", lw=0.75, ls=":", alpha=0.5)
    ax.set_xlabel(r"Dimensionless time $k_{\mathrm{rec}} t$")
    ax.set_ylabel(r"Singlet probability $p_S(t; \theta=0^\circ)$")
    ax.set_title(r"(a) Singlet Survival Dynamics ($\xi = \gamma/k_{\mathrm{rec}} = 3.0$)")
    ax.set_xlim(0.0, 5.0)
    ax.set_ylim(0.0, 1.04)
    ax.grid(True, alpha=0.2)
    ax.legend(loc="upper right", ncol=2, frameon=True, framealpha=0.92, handlelength=2.0)

    # Panel (b): Angular compass modulation Phi_S(theta) - Phi_S(0) at xi=3
    ax = axes[0, 1]
    th = ang["theta_deg"]
    for mu, lbl in [(0.40, r"Global ML ($\mu=0.40$)"), (0.50, r"Global ML ($\mu=0.50$)"),
                    (0.70, r"Global ML ($\mu=0.70$)"), (1.00, r"Global Markov ($\mu=1.00$)")]:
        mod = 100.0 * (ang[f"global_ML_mu{mu:.2f}"] if mu < 1.0 else ang["global_Markov_mu1.00"])
        mod = mod - mod[0]
        ax.plot(th, mod, color=C_MU[mu], lw=1.9 if mu in (0.5, 1.0) else 1.4,
                ls="--" if mu == 1.0 else "-", label=lbl)
    for key, col, ls, lbl in [
        ("STD_xi3", "#009E73", "-.", r"STD ($\xi=3$)"),
        ("local_iso_S1_xi3", "#56B4E9", ":", r"Local iso $\mathbf{S}_1$ ($\xi=3$)"),
        ("local_z_S1_xi3", "#CC79A7", (0, (3, 1, 1, 1)), r"Uniaxial $S_{1z}$ ($\xi=3$)"),
    ]:
        mod = 100.0 * (ang[key] - ang[key][0])
        ax.plot(th, mod, color=col, lw=1.5, ls=ls, label=lbl)
    ax.axhline(0.0, color="k", lw=0.7, alpha=0.5)
    ax.set_xlabel(r"Magnetic field inclination $\theta$ (deg)")
    ax.set_ylabel(r"$[\Phi_S(\theta) - \Phi_S(0^\circ)] \times 10^2$")
    ax.set_title(r"(b) Compass Angular Modulation at $\xi = 3.0$ (Sign Reversal at $\mu=1$)")
    ax.set_xlim(0.0, 180.0)
    ax.set_ylim(-10.6, 0.8)
    ax.set_xticks([0, 30, 60, 90, 120, 150, 180])
    ax.grid(True, alpha=0.2)
    ax.legend(loc="lower left", ncol=2, frameon=True, framealpha=0.95, fontsize=7.0)

    # Zoom inset placed in completely empty bottom-right whitespace
    axins = ax.inset_axes([0.65, 0.08, 0.32, 0.28], facecolor="white")
    mk_mod = 100.0 * (ang["global_Markov_mu1.00"] - ang["global_Markov_mu1.00"][0])
    iso_mod = 100.0 * (ang["local_iso_S1_xi3"] - ang["local_iso_S1_xi3"][0])
    axins.plot(th, mk_mod, color=C_MU[1.00], lw=1.7, ls="--")
    axins.plot(th, iso_mod, color="#56B4E9", lw=1.4, ls=":")
    axins.axhline(0.0, color="k", lw=0.6, alpha=0.6)
    axins.set_xlim(0.0, 180.0)
    axins.set_ylim(-0.04, 0.22)
    axins.set_xticks([0, 90, 180])
    axins.set_yticks([0.0, 0.1, 0.2])
    axins.tick_params(labelsize=6.6)
    axins.set_title(r"Zoom: sign flip ($\mu=1 > 0$)", fontsize=6.9, pad=2)
    axins.grid(True, alpha=0.25)

    # Panel (c): Sign-flip blind spot: max-min vs |Phi(0) - Phi(90)|
    ax = axes[1, 0]
    ang_scan = v2["angular_and_sign_flips_8x8"]["angular_comparison"]
    xis_d = np.array(ang_scan["D_dep"]["xi"])
    ax.loglog(xis_d, ang_scan["D_dep"]["Delta_Phi_maxmin"], color=C_MU[1.00], lw=1.8, ls="-",
              label=r"Global Markov $\Delta\Phi_S^{\max-\min}$")
    ax.loglog(xis_d, np.abs(ang_scan["D_dep"]["signed_Phi0_minus_Phi90"]), color=C_MU[1.00], lw=1.3, ls="--",
              label=r"Global Markov $|\Phi_S(0^\circ)-\Phi_S(90^\circ)|$")
    ax.loglog(xis_d, ang_scan["D_iso_S1"]["Delta_Phi_maxmin"], color="#56B4E9", lw=1.8, ls="-",
              label=r"Local iso $\mathbf{S}_1$ $\Delta\Phi_S^{\max-\min}$")
    ax.loglog(xis_d, np.abs(ang_scan["D_iso_S1"]["signed_Phi0_minus_Phi90"]), color="#56B4E9", lw=1.3, ls=":",
              label=r"Local iso $\mathbf{S}_1$ $|\Phi_S(0^\circ)-\Phi_S(90^\circ)|$")

    # Overlay ML mu=0.50 (monotonic, no sign flip)
    ml05_recs = v2["mittag_leffler_8x8"]["mu_0.50"]["records"]
    ml_x = [r["xi"] for r in ml05_recs if r["xi"] <= 35.0]
    ml_y = [r["abs_anisotropy"] for r in ml05_recs if r["xi"] <= 35.0]
    ax.loglog(ml_x, ml_y, color=C_MU[0.50], lw=2.0, marker="o", ms=4, label=r"Global ML ($\mu=0.50$, no flip)")

    xi_flip_dep = v2["angular_and_sign_flips_8x8"]["sign_flip_blind_spots"]["D_dep"][0]["xi_flip"]
    xi_flip_iso = v2["angular_and_sign_flips_8x8"]["sign_flip_blind_spots"]["D_iso_S1"][0]["xi_flip"]
    ax.axvline(xi_flip_dep, color=C_MU[1.00], lw=0.9, ls=":", alpha=0.7)
    ax.axvline(xi_flip_iso, color="#56B4E9", lw=0.9, ls=":", alpha=0.7)
    ax.annotate(rf"$\xi_{{\mathrm{{flip}}}}={xi_flip_dep:.2f}$", xy=(xi_flip_dep, 1.5e-3),
                xytext=(0.24, 2.2e-4), arrowprops=dict(arrowstyle="->", color=C_MU[1.00], lw=0.9),
                fontsize=8.2, color=C_MU[1.00])
    ax.annotate(rf"$\xi_{{\mathrm{{flip}}}}={xi_flip_iso:.2f}$", xy=(xi_flip_iso, 1.2e-3),
                xytext=(2.3, 1.8e-4), arrowprops=dict(arrowstyle="->", color="#0072B2", lw=0.9),
                fontsize=8.2, color="#0072B2")
    ax.set_xlabel(r"Dimensionless noise rate $\xi = \gamma / k_{\mathrm{rec}}$")
    ax.set_ylabel(r"Compass anisotropy metric")
    ax.set_title(r"(c) Sign-Flip Blind Spots vs. Unidirectional ML Decay")
    ax.set_xlim(0.1, 30.0)
    ax.set_ylim(3e-6, 0.12)
    ax.grid(True, which="both", alpha=0.18)
    ax.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.5)

    # Panel (d): Fourth-moment theorem verification across 8x8, 12x12, 36x36
    ax = axes[1, 1]
    th_grid = np.linspace(0.0, 180.0, 181)
    sin2_grid = np.sin(np.deg2rad(th_grid)) ** 2
    model_styles = [
        ("spin_half_8x8", "#0072B2", "o", r"$I=1/2$ ($8\times 8$, $M_2=3.1875$)"),
        ("spin_one_14N_12x12", "#1b7837", "s", r"$^{14}\mathrm{N}\;I=1$ ($12\times 12$, $M_2=8.500$)"),
        ("fad_two_14N_36x36_canonical", "#762a83", "^", r"$^{14}\mathrm{N}_5+{}^{14}\mathrm{N}_{10}$ ($36\times 36$, $M_2=9.860$)"),
    ]
    for mkey, col, mk, lbl in model_styles:
        m = v1["models"][mkey]
        recs = m["moments_by_theta"]
        x_pts = np.sin(np.deg2rad([r["theta_deg"] for r in recs])) ** 2
        y_num = np.array([r["delta_M4_numeric"] for r in recs])
        y_max = max(r["delta_M4_analytic"] for r in recs)
        ax.plot(sin2_grid, y_max * sin2_grid, color=col, lw=1.6, alpha=0.85)
        ax.scatter(x_pts, y_num, color=col, marker=mk, s=36, zorder=4, label=lbl)

    ax.text(0.55, 0.12,
            r"$M_0(\theta)=1$,  $M_2(\theta)=\mathrm{const}$" + "\n" + r"($\max|\Delta M_2| < 2\times 10^{-15}$)",
            transform=ax.transAxes, fontsize=8.5,
            bbox=dict(boxstyle="round,pad=0.3", fc="#f7f7f7", ec="#cccccc", lw=0.8))
    ax.set_xlabel(r"$\sin^2\theta$")
    ax.set_ylabel(r"Fourth-moment shift $M_4(\theta) - M_4(0^\circ)$")
    ax.set_title(r"(d) Exact Fourth-Moment Commutator Theorem Across Hilbert Spaces")
    ax.set_xlim(-0.03, 1.03)
    ax.set_ylim(-0.8, 20.5)
    ax.grid(True, alpha=0.2)
    ax.legend(loc="upper left", frameon=True, framealpha=0.92)

    save_fig(fig, "fig1_commutator_protection_and_blind_spot")


def make_figure2(v2):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12.2, 5.2), constrained_layout=True)

    # Panel (a): 5-channel taxonomy on 8x8 (45-digit mpmath)
    ch = v2["channels_8x8_mpmath"]
    ml = v2["mittag_leffler_8x8"]

    # Plot ML curves
    for mu, lbl in [(0.40, r"Global ML ($\mu=0.40$, $\xi^{-0.40}$)"),
                    (0.50, r"Global ML ($\mu=0.50$, $\xi^{-0.50}$)"),
                    (0.70, r"Global ML ($\mu=0.70$, $\xi^{-0.70}$)")]:
        recs = ml[f"mu_{mu:.2f}"]["records"]
        xs = [r["xi"] for r in recs]
        ys = [r["abs_anisotropy"] for r in recs]
        ax1.loglog(xs, ys, color=C_MU[mu], lw=1.8, marker="o", ms=3.5, label=lbl)

    specs = [
        ("d1_local_z_S1", "#CC79A7", "-", "d", r"Uniaxial $S_{1z}$ ($\xi^{0}$ plateau)"),
        ("d3_local_z_S1_S2", "#E69F00", "-", "^", r"Uniaxial $S_{1z}+S_{2z}$ ($\xi^{-1.0}$)"),
        ("b_STD_half", "#009E73", "-", "s", r"Singlet–triplet deph. STD ($\xi^{-2.0}$)"),
        ("c1_local_iso_S1", "#56B4E9", "-", "v", r"Local isotropic $\mathbf{S}_1$ ($\xi^{-4.0}$)"),
        ("c2_local_iso_S2_J015", "#004D40", ":", "P", r"Local iso $\mathbf{S}_2$, $J_{\mathrm{ex}}=0.15$ ($\to\xi^{-4}$)"),
        ("a_global_dep_markov", C_MU[1.00], "--", "x", r"Global Markov depol. ($\xi^{-5.0}$)"),
        ("c3_local_iso_S1_S2", "#444444", "-.", "*", r"Two-radical iso $\mathbf{S}_1+\mathbf{S}_2$ ($\xi^{-5.0}$)"),
    ]
    for key, col, ls, mk, lbl in specs:
        recs = ch[key]["records"]
        xs = [r["xi"] for r in recs]
        ys = [abs(float(r["signed_str_mp"])) for r in recs]
        ax1.loglog(xs, ys, color=col, lw=1.7, ls=ls, marker=mk, ms=3.8, label=lbl)

    # Reference slope labels positioned cleanly in open whitespace
    add_slope_guide(ax1, 300, 1.0e-3, 5000, -1.0, r"$\xi^{-1}$", color="#B87A00", dy_text=0.35)
    add_slope_guide(ax1, 300, 6e-6, 5000, -2.0, r"$\xi^{-2}$", color="#007A59", dy_text=0.35)
    add_slope_guide(ax1, 450, 1.5e-11, 7000, -4.0, r"$\xi^{-4}$", color="#0072B2", dy_text=3.2)
    add_slope_guide(ax1, 200, 3e-12, 5000, -5.0, r"$\xi^{-5}$", color="#A03000", dy_text=0.30)

    ax1.set_xlabel(r"Dimensionless noise strength $\xi = \gamma / k_{\mathrm{rec}}$")
    ax1.set_ylabel(r"$0^\circ$–$90^\circ$ compass anisotropy $|\Phi_S(0^\circ) - \Phi_S(90^\circ)|$")
    ax1.set_title(r"(a) Five-Channel Asymptotic Taxonomy ($8\times 8$, 45-digit $\mathtt{mpmath}$)")
    ax1.set_xlim(0.08, 1.4e4)
    ax1.set_ylim(1e-22, 0.5)
    ax1.grid(True, which="both", alpha=0.16)
    ax1.legend(loc="lower left", ncol=1, frameon=True, framealpha=0.92, fontsize=7.2)

    # Panel (b): Asymmetric Haberkorn k_T / k_S in {0.1, 1, 5, 10}
    asym_specs = [
        ("e1_dep_kT0.1", C_MU[1.00], ":", "v", r"Global depol. $k_T/k_S=0.1$ ($\alpha=5.00$)"),
        ("a_global_dep_markov", C_MU[1.00], "-", "o", r"Global depol. $k_T/k_S=1.0$ ($\alpha=4.99$)"),
        ("e2_dep_kT5.0", "#8c2d04", "--", "^", r"Global depol. $k_T/k_S=5.0$ ($\alpha=4.98$)"),
        ("e3_dep_kT10.0", "#d94801", "-.", "s", r"Global depol. $k_T/k_S=10.0$ ($\alpha=4.96$)"),
        ("e4_STD_kT5.0", "#009E73", "--", "D", r"STD $k_T/k_S=5.0$ ($\alpha=1.93\to 2.0$)"),
        ("e5_iso_S1_kT5.0", "#56B4E9", "-", "P", r"Local iso $\mathbf{S}_1$, $k_T/k_S=5.0$ ($\alpha\to 4.0$)"),
        ("e6_z_S1_S2_kT5.0", "#E69F00", "-", "*", r"Uniaxial $S_{1z}+S_{2z}$, $k_T/k_S=5.0$ ($\alpha=0.97$)"),
    ]
    for key, col, ls, mk, lbl in asym_specs:
        recs = ch[key]["records"]
        xs = [r["xi"] for r in recs]
        ys = [abs(float(r["signed_str_mp"])) for r in recs]
        ax2.loglog(xs, ys, color=col, lw=1.65, ls=ls, marker=mk, ms=3.8, label=lbl)

    ax2.text(0.04, 0.05,
             "Exact Haberkorn conservation:\n" + r"$\max|\Phi_S + \Phi_T - 1| \leq 8.2\times 10^{-43}$ (all $\xi, k_T/k_S$)" + "\n"
             + r"$H_{\mathrm{eff}}$ biorthogonal cross-check $< 2.23\times 10^{-15}$",
             transform=ax2.transAxes, fontsize=7.6,
             bbox=dict(boxstyle="round,pad=0.3", fc="#f7f7f7", ec="#cccccc", lw=0.8))

    ax2.set_xlabel(r"Dimensionless noise strength $\xi = \gamma / k_S$")
    ax2.set_ylabel(r"$0^\circ$–$90^\circ$ compass anisotropy $|\Phi_S(0^\circ) - \Phi_S(90^\circ)|$")
    ax2.set_title(r"(b) Asymmetric Haberkorn Recombination ($k_T/k_S \in \{0.1, 1, 5, 10\}$)")
    ax2.set_xlim(0.08, 1.4e4)
    ax2.set_ylim(1e-22, 0.5)
    ax2.grid(True, which="both", alpha=0.16)
    ax2.legend(loc="lower left", bbox_to_anchor=(0.0, 0.21), frameon=True, framealpha=0.92, fontsize=7.2)

    save_fig(fig, "fig2_five_channel_taxonomy")


def make_figure3(v3, v5):
    fig, axes = plt.subplots(2, 2, figsize=(11.8, 8.8), constrained_layout=True)

    # Panel (a): K=8 positive Prony/NNLS fit to power-law C(t)/sigma^2 = (1 + t/tau_c)^(-mu)
    ax = axes[0, 0]
    u = np.logspace(-4.0, 3.0, 400)
    prony = v3["prony_fits"]
    for mu in [0.40, 0.50, 0.70, 0.85]:
        f = prony[f"mu_{mu:.2f}"]
        c = np.array(f["c_tilde"])
        nu = np.array(f["nu_tilde"])
        exact = (1.0 + u) ** (-mu)
        approx = np.exp(-u[:, None] * nu[None, :]) @ c
        ax.loglog(u, exact, color=C_MU[mu], lw=2.2, alpha=0.35)
        ax.loglog(u, approx, color=C_MU[mu], lw=1.3, ls="--",
                  label=rf"$\mu={mu:.2f}$ ($K=8$, max rel err $= {100*f['max_rel_err']:.2f}\%$)")
    ax.set_xlabel(r"Dimensionless lag time $t / \tau_c$")
    ax.set_ylabel(r"Normalized bath autocorrelation $C(t)/\sigma^2$")
    ax.set_title(r"(a) Positive Prony/NNLS Decomposition of $(1 + t/\tau_c)^{-\mu}$")
    ax.set_xlim(1e-4, 1e3)
    ax.set_ylim(1e-3, 1.3)
    ax.grid(True, which="both", alpha=0.18)
    ax.legend(
        loc="lower left",
        frameon=True,
        framealpha=0.92,
        fontsize=7.4,
        title=r"Solid (translucent): exact   |   Dashed: $K=8$ Prony",
        title_fontsize=7.3,
    )

    # Panel (b): Protocol A (Fixed sigma = 3.0 across tau_c)
    ax = axes[0, 1]
    pA_3d_05 = v3["protocol_A_fixed_sigma"]["iso3d_mu0.50"]
    pA_3d_85 = v3["protocol_A_fixed_sigma"]["iso3d_mu0.85"]
    pA_ou1 = v3["protocol_A_fixed_sigma"]["iso3d_ou1mode_matched"]
    pA_z_05 = v3["protocol_A_fixed_sigma"]["z_axis_mu0.50"]

    tc = np.array([r["tau_c"] for r in pA_3d_05])
    # Exact 45-digit mpmath Markovian local_iso_S1 from v5!
    mk_mp_recs = v5["protA_mpmath_markov_local_iso_S1"]["records"]
    mk_mp_vals = np.array([abs(float(r["signed_str_mp"])) for r in mk_mp_recs])
    ax.loglog(tc, mk_mp_vals, color=C_MU[1.00], lw=1.8, ls="--", marker="x", ms=4.5,
              label=r"Rate-matched Markov $\mathbf{S}_1$ ($\gamma_{\mathrm{eff}}=2\sigma^2\tau_{\mathrm{int}}$)")

    y_3d05 = np.array([abs(r["ou_mc"]["signed_anisotropy"]) for r in pA_3d_05])
    se_3d05 = np.array([r["ou_mc"]["signed_anisotropy_se"] for r in pA_3d_05])
    ax.errorbar(tc, y_3d05, yerr=se_3d05, color=C_MU[0.50], lw=1.9, marker="o", ms=4.2, capsize=2.5,
                label=r"3D-iso $1/f^{0.5}$ bath ($\mu=0.50$, OU-MC)")

    # Overlay exact 3D ADO points where computed
    ado_tc = [r["tau_c"] for r in pA_3d_05 if r["ado"] is not None]
    ado_y = [abs(r["ado"]["signed_anisotropy"]) for r in pA_3d_05 if r["ado"] is not None]
    if ado_tc:
        ax.scatter(ado_tc, ado_y, color="k", marker="D", s=34, zorder=6, label=r"Exact 3D ADO check")

    y_3d85 = np.array([abs(r["ou_mc"]["signed_anisotropy"]) for r in pA_3d_85])
    se_3d85 = np.array([r["ou_mc"]["signed_anisotropy_se"] for r in pA_3d_85])
    ax.errorbar(tc, y_3d85, yerr=se_3d85, color=C_MU[0.85], lw=1.5, ls="-.", marker="^", ms=3.8, capsize=2,
                label=r"3D-iso $1/f^{0.15}$ bath ($\mu=0.85$, OU-MC)")

    y_ou1 = np.array([abs(r["ou_mc"]["signed_anisotropy"]) for r in pA_ou1])
    se_ou1 = np.array([r["ou_mc"]["signed_anisotropy_se"] for r in pA_ou1])
    res_ou1 = y_ou1 > 1.5 * se_ou1
    ax.errorbar(tc[res_ou1], y_ou1[res_ou1], yerr=se_ou1[res_ou1], color="#009E73", lw=1.4, ls=":", marker="s", ms=3.4, capsize=2.0,
                label=r"Single-mode OU (matched $\sigma, \tau_{\mathrm{int}}$)")
    if np.any(~res_ou1):
        ax.errorbar(tc[~res_ou1], y_ou1[~res_ou1] + se_ou1[~res_ou1],
                    yerr=0.45 * (y_ou1[~res_ou1] + se_ou1[~res_ou1]), uplims=True,
                    color="#009E73", ls="none", marker="s", mfc="white", ms=3.6, capsize=2.2)

    y_z05 = np.array([abs(r["ou_mc"]["signed_anisotropy"]) for r in pA_z_05])
    ax.loglog(tc, y_z05, color="#CC79A7", lw=1.4, ls="-",
              label=r"Uniaxial $S_{1z}$ $1/f^{0.5}$ bath ($\sigma=3.0$)")

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel(r"Bath UV correlation time $\tau_c$ ($\mu\mathrm{s}$)")
    ax.set_ylabel(r"$0^\circ$–$90^\circ$ anisotropy $|\Phi_S(0^\circ) - \Phi_S(90^\circ)|$")
    ax.set_title(r"(b) Protocol A: Fixed RMS $\sigma=3.0\;\mu\mathrm{s}^{-1}$ (Motional Narrowing $\to$ Static)")
    ax.set_xlim(7e-4, 45.0)
    ax.set_ylim(1e-20, 0.25)
    ax.grid(True, which="both", alpha=0.16)
    ax.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.2)

    # Panel (c): Protocol B (Fixed integrated Markovian rate gamma_eff = 10.0)
    ax = axes[1, 0]
    pB = v3["protocol_B_fixed_gamma_eff"]
    tc_b = np.array([r["tau_c"] for r in pB["records"]])
    y_b = np.array([abs(r["iso3d_ou_mc"]["signed_anisotropy"]) for r in pB["records"]])
    se_b = np.array([r["iso3d_ou_mc"]["signed_anisotropy_se"] for r in pB["records"]])
    mk_g10 = abs(pB["markovian_3d"]["signed_anisotropy"])
    mk_exp = int(np.floor(np.log10(mk_g10)))
    mk_man = mk_g10 / (10.0 ** mk_exp)

    ax.errorbar(tc_b, y_b, yerr=se_b, color=C_MU[0.50], lw=2.0, marker="o", ms=5, capsize=3,
                label=r"3D-iso $1/f^{0.5}$ bath ($\gamma_{\mathrm{eff}}=10.0$ fixed)")
    ax.axhline(mk_g10, color=C_MU[1.00], lw=1.6, ls="--",
               label=rf"Markovian 3D $\mathbf{{S}}_1$ ($\xi=10$): ${mk_man:.2f}\times 10^{{{mk_exp}}}$")
    ax.axhline(0.0766366, color="#666666", lw=1.2, ls=":", label=r"Coherent limit ($\gamma=0$): $0.0766$")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel(r"Bath UV correlation time $\tau_c$ ($\mu\mathrm{s}$)")
    ax.set_ylabel(r"$0^\circ$–$90^\circ$ anisotropy $|\Phi_S(0^\circ) - \Phi_S(90^\circ)|$")
    ax.set_title(r"(c) Protocol B: Fixed $\gamma_{\mathrm{eff}}=10.0$ (Memory Spectral Redistribution)")
    ax.set_xlim(7e-4, 15.0)
    ax.set_ylim(1e-5, 0.16)
    ax.grid(True, which="both", alpha=0.16)
    ax.legend(loc="center right", bbox_to_anchor=(0.98, 0.36), frameon=True, framealpha=0.95, fontsize=7.6)

    # Panel (d): Protocol C (Coupling sweep vs RMS amplitude sigma, showing O(sigma^-2) = O(xi_eff^-1) vs Markov O(sigma^-8))
    ax = axes[1, 1]
    pC = v3["protocol_C_sigma_sweep"]["records"]
    sig_c = np.array([r["sigma"] for r in pC])
    y_c_z = np.array([abs(r["z_axis_ou_mc"]["signed_anisotropy"]) for r in pC])
    se_c_z = np.array([r["z_axis_ou_mc"]["signed_anisotropy_se"] for r in pC])

    # Resolved points for tau_c = 0.2 (signal > 2*SE)
    sig_02_res, y_02_res, se_02_res = [], [], []
    for r in pC:
        if abs(r["iso3d_ou_mc"]["signed_anisotropy"]) > 2.0 * r["iso3d_ou_mc"]["signed_anisotropy_se"]:
            sig_02_res.append(r["sigma"])
            y_02_res.append(abs(r["iso3d_ou_mc"]["signed_anisotropy"]))
            se_02_res.append(r["iso3d_ou_mc"]["signed_anisotropy_se"])

    # Slow colored bath (tau_c = 5.0, cubic-paired OU-MC) and Exact Static 3D Gaussian Quadrature
    pC_t5 = v5["protC_slow_tau5_cubic_ou_mc"]["records"]
    sig_t5 = np.array([r["sigma"] for r in pC_t5])
    y_t5 = np.array([abs(r["signed_anisotropy"]) for r in pC_t5])
    se_t5 = np.array([r["signed_anisotropy_se"] for r in pC_t5])

    st3d = v5["static_3d_gaussian_quadrature"]["records"]
    sig_st = np.array([r["sigma"] for r in st3d])
    y_st = np.array([abs(r["signed_anisotropy"]) for r in st3d])

    mk_c_vals = np.array([abs(float(r["signed_str_mp"])) for r in v5["protC_mpmath_markov_local_iso_S1"]["records"]])

    ax.errorbar(sig_c, y_c_z, yerr=se_c_z, color="#CC79A7", lw=1.6, marker="d", ms=4.0, capsize=2.5,
                label=r"Uniaxial $S_{1z}$ $1/f^{0.5}$ ($\tau_c=0.2$, $O(1)$)")
    ax.loglog(sig_st, y_st, color="#222222", lw=1.8, ls="-",
              label=r"Static 3D Gaussian limit ($\tau_c\to\infty$, $\Theta(\sigma^{-2})$)")
    ax.errorbar(sig_t5, y_t5, yerr=se_t5, color=C_MU[0.50], lw=1.8, marker="o", ms=4.4, capsize=2.5,
                label=r"3D-iso $1/f^{0.5}$ slow ($\tau_c=5.0$, cubic OU-MC)")
    ax.errorbar(sig_02_res, y_02_res, yerr=se_02_res, color="#56B4E9", lw=1.5, ls="-.", marker="^", ms=4.2, capsize=2.5,
                label=r"3D-iso $1/f^{0.5}$ ($\tau_c=0.2$, resolved)")
    ax.loglog(sig_c, mk_c_vals, color=C_MU[1.00], lw=1.7, ls="--", marker="x", ms=4.2,
              label=r"Rate-matched Markov $\mathbf{S}_1$ ($\xi_{\mathrm{eff}}^{-4}\propto\sigma^{-8}$)")

    add_slope_guide(ax, 15.0, 2.5e-3, 250.0, -2.0, r"$\sigma^{-2}\;(\xi_{\mathrm{eff}}^{-1})$", color="#222222", dy_text=2.1)
    add_slope_guide(ax, 1.8, 3e-7, 15.0, -8.0, r"$\sigma^{-8}\;(\xi_{\mathrm{eff}}^{-4})$", color=C_MU[1.00], dy_text=0.35)

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel(r"RMS local magnetic noise amplitude $\sigma$ ($\mu\mathrm{s}^{-1}$)")
    ax.set_ylabel(r"$0^\circ$–$90^\circ$ anisotropy $|\Phi_S(0^\circ) - \Phi_S(90^\circ)|$")
    ax.set_title(r"(d) Protocol C: Strong-Coupling Scaling vs. $\sigma$ and $\xi_{\mathrm{eff}}$")
    ax.set_xlim(0.25, 380.0)
    ax.set_ylim(1e-20, 0.25)
    ax.grid(True, which="both", alpha=0.16)
    ax.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.0)

    save_fig(fig, "fig3_microscopic_ado_crucible")


def make_figure4(v2, v4, v5):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12.2, 5.2), constrained_layout=True)

    # Panel (a): Canonical 36x36 FAD (14N5 + 14N10)
    fc = v2["fad_36x36_canonical"]
    alpha_can_mu1 = fc["global_dep_spectral"]["mu_1.00"]["alpha_asym_100_to_10000"]
    alpha_can_iso = fc["sparse_channels"]["local_iso_S1"]["alpha_100_to_10000"]
    for mk, col, ls, lbl in [
        ("mu_0.50", C_MU[0.50], "-", r"Global ML ($\mu=0.50$, $\alpha=0.50$)"),
        ("mu_1.00", C_MU[1.00], "--", rf"Global Markov ($\mu=1.00$, $\alpha={alpha_can_mu1:.2f}$)"),
    ]:
        recs = fc["global_dep_spectral"][mk]["records"]
        xs = [r["xi"] for r in recs if r["abs_anisotropy"] > 1e-22]
        ys = [r["abs_anisotropy"] for r in recs if r["abs_anisotropy"] > 1e-22]
        ax1.loglog(xs, ys, color=col, lw=1.8, ls=ls, marker="o", ms=3.5, label=lbl)

    for cname, col, ls, mk, lbl in [
        ("local_z_S1", "#CC79A7", "-", "d", r"Uniaxial $S_{1z}$ ($\alpha=0.0$)"),
        ("local_z_S1_S2", "#E69F00", "-", "^", r"Uniaxial $S_{1z}+S_{2z}$ ($\alpha=0.97$)"),
        ("STD", "#009E73", "-", "s", r"STD ($\alpha=1.89\to 2.0$)"),
        ("local_iso_S1", "#56B4E9", "-", "v", rf"Local iso $\mathbf{{S}}_1$ ($\alpha={alpha_can_iso:.2f}\to 4.0$)"),
    ]:
        recs = fc["sparse_channels"][cname]["records"]
        xs = [r["xi"] for r in recs if r["abs_anisotropy"] > 1e-22]
        ys = [r["abs_anisotropy"] for r in recs if r["abs_anisotropy"] > 1e-22]
        ax1.loglog(xs, ys, color=col, lw=1.7, ls=ls, marker=mk, ms=3.6, label=lbl)

    ax1.set_xlabel(r"Dimensionless noise strength $\xi = \gamma / k_{\mathrm{rec}}$")
    ax1.set_ylabel(r"$0^\circ$–$90^\circ$ compass anisotropy $|\Phi_S(0^\circ) - \Phi_S(90^\circ)|$")
    ax1.set_title(r"(a) Canonical $36\times 36$ $^{14}\mathrm{N}_5+{}^{14}\mathrm{N}_{10}$ $\mathrm{FAD}^{\bullet-}$ (1296-dim)")
    ax1.set_xlim(0.08, 1.4e4)
    ax1.set_ylim(1e-20, 0.4)
    ax1.grid(True, which="both", alpha=0.16)
    ax1.legend(loc="lower left", frameon=True, framealpha=0.95, fontsize=7.5)

    # Panel (b): Physical Earth-field 50 uT FAD (A_N5=309, A_N10=107, omega_L=8.80) up to xi=3e6
    fp = v2["fad_36x36_physical_50uT"]
    fp_ext = v5["fad_36x36_physical_50uT_extended_tail"]
    fp_ml = v4["fad_36x36_physical_50uT_ml_scan"]
    xi_flip_mk = fp["sign_flip_blind_spots"]["global_Markov_mu1"][0]
    xi_flip_iso = fp["sign_flip_blind_spots"]["local_iso_S1"][0]
    alpha_50_iso_tail = fp_ext["sparse_channels"]["local_iso_S1"]["alpha_last_interval"]

    # Stitch ML mu=0.50 & mu=1.00 across [0.1, 1e6] (v2 low-xi + v4 + v5 45-digit mp.eigsy tail)
    for mk, col, ls, lbl in [
        ("mu_0.50", C_MU[0.50], "-", r"Global ML ($\mu=0.50$, $\xi^{-0.50}$)"),
        ("mu_1.00", C_MU[1.00], "--", rf"Global Markov ($\mu=1.00$, $\xi_{{\mathrm{{flip}}}}={xi_flip_mk:.0f}$, $\xi^{{-5.00}}$)"),
    ]:
        d_map = {round(r["xi"], 6): r["abs_anisotropy"] for r in fp["global_dep_spectral"][mk]["records"]}
        for r in fp_ml[mk]["records"]:
            d_map[round(r["xi"], 6)] = abs(float(r["signed_str_mp"]))
        for r in fp_ext["global_dep_spectral"][mk]["records"]:
            d_map[round(r["xi"], 6)] = abs(float(r["signed_str_mp"]))
        xs = [x for x in sorted(d_map.keys()) if d_map[x] > 1e-26]
        ys = [d_map[x] for x in xs]
        ax2.loglog(xs, ys, color=col, lw=1.8, ls=ls, marker="o", ms=3.5, label=lbl)

    for cname, col, ls, mk, lbl in [
        ("local_z_S1", "#CC79A7", "-", "d", r"Uniaxial $S_{1z}$ ($\xi^0$)"),
        ("local_z_S1_S2", "#E69F00", "-", "^", r"Uniaxial $S_{1z}+S_{2z}$ ($\to\xi^{-1.00}$)"),
        ("STD", "#009E73", "-", "s", r"STD ($\to\xi^{-2}$ for $\xi \gg A^2/k$)"),
        ("local_iso_S1", "#56B4E9", "-", "v", rf"Local iso $\mathbf{{S}}_1$ ($\xi_{{\mathrm{{flip}}}}={xi_flip_iso:.0f}$, $\to\xi^{{-{alpha_50_iso_tail:.2f}}}$)"),
    ]:
        d_map = {round(r["xi"], 6): r["abs_anisotropy"] for r in fp["sparse_channels"][cname]["records"]}
        if cname in fp_ext["sparse_channels"]:
            for r in fp_ext["sparse_channels"][cname]["records"]:
                d_map[round(r["xi"], 6)] = abs(r["signed_anisotropy"])
        xs = [x for x in sorted(d_map.keys()) if d_map[x] > 1e-26]
        ys = [d_map[x] for x in xs]
        ax2.loglog(xs, ys, color=col, lw=1.7, ls=ls, marker=mk, ms=3.6, label=lbl)

    ax2.axvline(309.38, color="#333333", lw=1.0, ls=":", alpha=0.75, zorder=1)
    ax2.text(390, 8e-6, r"$\gamma = A_{\mathrm{N5},\parallel}$" + "\n" + r"($309\;\mu\mathrm{s}^{-1}$)",
             ha="left", va="center", fontsize=7.8, color="#333333",
             bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.9))
    ax2.axvspan(0.1, 309.38, color="#f0f0f0", alpha=0.45, zorder=0)
    ax2.text(3.5, 2e-7, "Pre-asymptotic\n" + r"($\gamma < A_{\mathrm{N5},\parallel}$)",
             ha="center", va="center", fontsize=7.8, color="#444444")

    ax2.set_xlabel(r"Dimensionless noise strength $\xi = \gamma / k_{\mathrm{rec}}$")
    ax2.set_ylabel(r"$0^\circ$–$90^\circ$ compass anisotropy $|\Phi_S(0^\circ) - \Phi_S(90^\circ)|$")
    ax2.set_title(r"(b) Physical $50\;\mu\mathrm{T}$ $\mathrm{FAD}^{\bullet-}$ ($A_{\mathrm{N5},\parallel}=309\;\mu\mathrm{s}^{-1}$)")
    ax2.set_xlim(0.08, 5.0e6)
    ax2.set_ylim(1e-25, 0.5)
    ax2.grid(True, which="both", alpha=0.16)
    leg2 = ax2.legend(loc="lower left", frameon=True, framealpha=1.0, fontsize=7.2)
    leg2.set_zorder(6)

    save_fig(fig, "fig4_realistic_fad_36x36")


def main():
    v1 = load_json("verify_01_moments_and_laplace.json")
    v2 = load_json("verify_02_five_channel_liouville.json")
    v3 = load_json("verify_03_microscopic_ado_and_mc.json")
    v4 = load_json("verify_04_curves_and_tables.json")
    v5 = load_json("verify_05_supplement_checks.json")

    make_figure1(v1, v2, v4)
    make_figure2(v2)
    make_figure3(v3, v5)
    make_figure4(v2, v4, v5)
    print("All 4 figures generated successfully.")


if __name__ == "__main__":
    main()
