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
            if r.get("duration_s") and r.get("model") and r.get("problem") and r.get("profile"):
                records.append(r)
        except json.JSONDecodeError:
            continue

data = defaultdict(lambda: {"times": [], "resolved": [], "total": [], "compiles": []})
for r in records:
    model = r["model"].split("/")[-1]
    profile = r["profile"]
    ev = r.get("eval", {})
    key = (r["problem"], model, profile)
    data[key]["times"].append(r["duration_s"])
    data[key]["resolved"].append(ev.get("pairs_resolved", 0))
    data[key]["total"].append(ev.get("pairs_total", 0))
    data[key]["compiles"].append(ev.get("compiles", False))

problems = sorted({k[0] for k in data})
combos = sorted({(k[1], k[2]) for k in data})

plt.style.use("dark_background")
fig, ax = plt.subplots(figsize=(14, 7))

x = np.arange(len(problems))
n = len(combos)
width = 0.8 / max(n, 1)

combo_colors = {
    ("deepseek-v4-pro", "full"):     "#00d4aa",
    ("deepseek-v4-pro", "rocq-mcp"): "#007a62",
    ("claude-sonnet-4-6", "full"):     "#ff6b6b",
    ("claude-sonnet-4-6", "rocq-mcp"): "#cc3333",
}
fallback_colors = ["#00d4aa", "#007a62", "#ff6b6b", "#cc3333", "#ffe66d", "#4ecdc4"]

for i, (model, profile) in enumerate(combos):
    display_profile = "rocq-piler" if profile == "full" else profile
    label = f"{model} / {display_profile}"
    color = combo_colors.get((model, profile), fallback_colors[i % len(fallback_colors)])
    vals = []
    hatches = []

    for p in problems:
        d = data.get((p, model, profile))
        if d and d["times"]:
            avg_time = np.mean(d["times"])
            avg_resolved = np.mean(d["resolved"])
            avg_total = np.mean(d["total"])
            any_compiles = any(d["compiles"])
            rate = avg_resolved / avg_total if avg_total > 0 else 0
            passed = any_compiles and rate >= 1.0
            vals.append(avg_time)
            hatches.append("" if passed else "///")
        else:
            vals.append(0)
            hatches.append("")

    offset = (i - (n - 1) / 2) * width
    bars = ax.bar(x + offset, vals, width * 0.9, label=label,
                  color=color, edgecolor="white", linewidth=0.5)

    for bar, v, h in zip(bars, vals, hatches):
        if h:
            bar.set_hatch(h)
            bar.set_edgecolor("#ff4444")
            bar.set_linewidth(1.5)
        if v > 0:
            ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 15,
                    f"{v:.0f}s", ha="center", va="bottom", fontsize=8, color="white")

ax.set_xlabel("Problem", fontsize=12)
ax.set_ylabel("Avg Duration (seconds)", fontsize=12)
ax.set_title("Vericoding Benchmark — Time × Success by Model × MCP",
             fontsize=14, fontweight="bold")
ax.set_xticks(x)
ax.set_xticklabels(problems, fontsize=11)

legend_handles = []
for model, profile in combos:
    color = combo_colors.get((model, profile), "#888888")
    dp = "rocq-piler" if profile == "full" else profile
    legend_handles.append(Patch(facecolor=color, edgecolor="white",
                                label=f"{model} / {dp}"))
legend_handles.append(Patch(facecolor="#666666", edgecolor="#ff4444",
                            hatch="///", label="FAILED (hatched)"))

ax.legend(handles=legend_handles, fontsize=9, loc="upper left")
ax.grid(axis="y", alpha=0.2)

plt.tight_layout()
out = Path(__file__).parent / "results" / "avg_time_by_model.png"
plt.savefig(out, dpi=150)
print(f"Saved to {out}")
