#!/usr/bin/env python3
import json
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.patches import Patch
import numpy as np

results_file = Path(__file__).parent / "results" / "summary.jsonl"

records = []
with open(results_file) as f:
    for line in f:
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
            if r.get("model") and r.get("problem"):
                records.append(r)
        except json.JSONDecodeError:
            continue

combo_data = defaultdict(lambda: {"costs": [], "pass": 0, "fail": 0})
for r in records:
    model = r["model"].split("/")[-1]
    profile = r.get("profile", "?")
    cost = r.get("cost", 0)
    ev = r.get("eval", {})
    resolved = ev.get("pairs_resolved", 0)
    total = ev.get("pairs_total", 0)
    compiles = ev.get("compiles", False)
    passed = compiles and total > 0 and resolved >= total

    combo_data[(model, profile)]["costs"].append(cost)
    if passed:
        combo_data[(model, profile)]["pass"] += 1
    else:
        combo_data[(model, profile)]["fail"] += 1

combos = sorted(combo_data.keys())
labels = [f"{m} /\n{'rocq-piler' if p == 'full' else p}" for m, p in combos]
avg_costs = [np.mean(combo_data[k]["costs"]) for k in combos]
fail_rates = [
    combo_data[k]["fail"] / (combo_data[k]["pass"] + combo_data[k]["fail"]) * 100
    for k in combos
]
runs = [combo_data[k]["pass"] + combo_data[k]["fail"] for k in combos]

combo_colors = {
    ("deepseek-v4-pro", "full"):        "#00d4aa",
    ("deepseek-v4-pro", "rocq-mcp"):    "#007a62",
    ("claude-sonnet-4-6", "full"):      "#ff6b6b",
    ("claude-sonnet-4-6", "rocq-mcp"):  "#cc3333",
}
colors = [combo_colors.get(k, "#888888") for k in combos]

plt.style.use("dark_background")
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

x = np.arange(len(combos))

bars1 = ax1.bar(x, avg_costs, 0.6, color=colors, edgecolor="white", linewidth=0.5)
for bar, v in zip(bars1, avg_costs):
    ax1.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.05,
             f"${v:.4f}" if v < 1 else f"${v:.2f}",
             ha="center", va="bottom", fontsize=10, color="white", fontweight="bold")
ax1.set_xticks(x)
ax1.set_xticklabels(labels, fontsize=9)
ax1.set_ylabel("Avg Cost per Run ($)", fontsize=12)
ax1.set_title("Cost per Proof", fontsize=14, fontweight="bold")
ax1.grid(axis="y", alpha=0.2)

bars2 = ax2.bar(x, fail_rates, 0.6, color=colors, edgecolor="white", linewidth=0.5)
for bar, v, n in zip(bars2, fail_rates, runs):
    ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.5,
             f"{v:.0f}%\n(n={n})",
             ha="center", va="bottom", fontsize=10, color="white", fontweight="bold")
ax2.set_xticks(x)
ax2.set_xticklabels(labels, fontsize=9)
ax2.set_ylabel("Failure Rate (%)", fontsize=12)
ax2.set_title("Proof Failure Rate", fontsize=14, fontweight="bold")
ax2.set_ylim(0, max(fail_rates) * 1.5 + 5)
ax2.grid(axis="y", alpha=0.2)

fig.suptitle("Vericoding Benchmark — Cost & Reliability by Model × MCP",
             fontsize=15, fontweight="bold", y=1.02)
plt.tight_layout()
out = Path(__file__).parent / "results" / "cost_and_failure.png"
plt.savefig(out, dpi=150, bbox_inches="tight")
print(f"Saved to {out}")
