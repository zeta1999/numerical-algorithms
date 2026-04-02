#!/usr/bin/env python3
"""
Plot sensitivity analysis results: condition number vs forward/backward error.
Generates log-log plots comparing empirical results to the theoretical bound.

Usage:
    python3 scripts/plot_sensitivity.py [csv_file]

If no CSV file is given, reads from lean/Analysis/sensitivity_results.csv.
"""

import csv
import sys
import os

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np
except ImportError:
    print("Error: matplotlib and numpy are required.")
    print("Install with: pip install matplotlib numpy")
    sys.exit(1)


def load_csv(path):
    """Load sensitivity results CSV."""
    data = {}
    with open(path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            n = int(row["n"])
            if n not in data:
                data[n] = {"kappa": [], "fwd_mean": [], "fwd_max": [], "bwd_mean": [], "bwd_max": []}
            data[n]["kappa"].append(float(row["mean_actual_kappa"]))
            data[n]["fwd_mean"].append(float(row["mean_forward_err"]))
            data[n]["fwd_max"].append(float(row["max_forward_err"]))
            data[n]["bwd_mean"].append(float(row["mean_backward_err"]))
            data[n]["bwd_max"].append(float(row["max_backward_err"]))
    return data


def plot_forward_error(data, output_path):
    """Plot condition number vs forward error (log-log)."""
    fig, ax = plt.subplots(figsize=(10, 7))

    eps = 2.22e-16
    colors = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]

    for idx, n in enumerate(sorted(data.keys())):
        d = data[n]
        kappas = np.array(d["kappa"])
        fwd_max = np.array(d["fwd_max"])
        # Filter out zero errors for log plot
        mask = fwd_max > 0
        if mask.any():
            ax.scatter(kappas[mask], fwd_max[mask],
                       color=colors[idx % len(colors)],
                       label=f"n={n} (max)", marker="o", s=60, zorder=3)

    # Theoretical bound line
    k_range = np.logspace(0, 14, 100)
    ax.plot(k_range, k_range * eps, "k--", linewidth=2,
            label=r"Theoretical: $\kappa \cdot \epsilon$", alpha=0.7)

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Condition Number " + r"$\kappa_1(A)$", fontsize=13)
    ax.set_ylabel("Forward Relative Error", fontsize=13)
    ax.set_title("LU Decomposition: Condition Number vs Forward Error", fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, which="both", alpha=0.3)
    ax.set_xlim(1, 1e14)
    ax.set_ylim(1e-17, 1)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    print(f"Saved forward error plot to {output_path}")


def plot_backward_error(data, output_path):
    """Plot condition number vs backward error (log-log)."""
    fig, ax = plt.subplots(figsize=(10, 7))

    eps = 2.22e-16
    colors = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd"]

    for idx, n in enumerate(sorted(data.keys())):
        d = data[n]
        kappas = np.array(d["kappa"])
        bwd_max = np.array(d["bwd_max"])
        mask = bwd_max > 0
        if mask.any():
            ax.scatter(kappas[mask], bwd_max[mask],
                       color=colors[idx % len(colors)],
                       label=f"n={n} (max)", marker="s", s=60, zorder=3)

    # Machine epsilon reference line
    ax.axhline(y=eps, color="k", linestyle="--", linewidth=2,
               label=r"Machine $\epsilon$", alpha=0.7)

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Condition Number " + r"$\kappa_1(A)$", fontsize=13)
    ax.set_ylabel("Backward Relative Error", fontsize=13)
    ax.set_title("LU Decomposition: Backward Stability", fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, which="both", alpha=0.3)
    ax.set_xlim(1, 1e14)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    print(f"Saved backward error plot to {output_path}")


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    default_csv = os.path.join(script_dir, "..", "lean", "Analysis", "sensitivity_results.csv")

    csv_path = sys.argv[1] if len(sys.argv) > 1 else default_csv
    if not os.path.exists(csv_path):
        print(f"Error: CSV file not found: {csv_path}")
        print("Run 'lake exe sensitivity' first to generate results.")
        sys.exit(1)

    data = load_csv(csv_path)

    out_dir = os.path.join(script_dir, "..", "plots")
    os.makedirs(out_dir, exist_ok=True)

    plot_forward_error(data, os.path.join(out_dir, "forward_error.png"))
    plot_backward_error(data, os.path.join(out_dir, "backward_error.png"))

    print("\nDone. Plots saved in nr1/plots/")


if __name__ == "__main__":
    main()
