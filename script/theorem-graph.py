#!/usr/bin/env python3
"""Theorem dependency graph for the twin exchange cargo theorem.

Parses lean-model/Klondike/*.lean, extracts declarations (comment-stripped),
and builds the strategic dependency graph among the curated major theorems
(direct-citation edges).  Manual dashed edges mark pending wiring; premise
pseudo-nodes mark the open premises (hwin / hrp / hdet).  Renders DOT ->
PNG/SVG via graphviz.

Run:   python script/theorem-graph.py
Out:   script/theorem-graph.{dot,png,svg}
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean-model" / "Klondike"
OUT_DOT = ROOT / "script" / "theorem-graph.dot"
OUT_PNG = ROOT / "script" / "theorem-graph.png"
OUT_SVG = ROOT / "script" / "theorem-graph.svg"

DECL_RE = re.compile(
    r"^(?:private\s+|protected\s+)?(?:theorem|lemma|def|structure|abbrev)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)",
    re.M,
)


def _blank(m):
    return "".join(ch if ch == "\n" else " " for ch in m.group(0))


def strip_comments(text: str) -> str:
    # block comments AND docstrings: every opener starts with /-, closer -/
    # (non-nesting approximation; nesting is absent from these files)
    text = re.sub(r"/-.*?-/", _blank, text, flags=re.S)
    # line comments (may start mid-line)
    text = re.sub(r"--[^\n]*", _blank, text)
    return text


def parse_declarations():
    decls = {}
    for f in sorted(LEAN_DIR.glob("*.lean")):
        raw = f.read_text(encoding="utf-8", errors="replace")
        stripped = strip_comments(raw)
        matches = list(DECL_RE.finditer(stripped))
        for i, m in enumerate(matches):
            start = m.start()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(stripped)
            body = stripped[start:end]
            decls.setdefault(m.group(1), []).append({
                "file": f.name,
                "line": stripped.count("\n", 0, start) + 1,
                "body": body,
                "sorry": re.search(r"\bsorry\b", body) is not None,
            })
    return decls


# id, matcher names, label, status
CURATED = [
    ("goal", ["solvable_cargoTwin_exchange"], "GOAL\nsolvable_cargoTwin_exchange", "goal"),
    ("licensed", ["solvable_cargoTwin_exchange_licensed"], "solvable_cargoTwin_exchange_licensed", "proven"),
    ("iff", ["solvable_iff_exchangeTwinCargo"], "solvable_iff_exchangeTwinCargo", "proven"),
    ("fwd", ["solvable_exchangeTwinCargo"], "solvable_exchangeTwinCargo", "proven"),
    ("go", ["solvable_exchangeTwinCargo_go"], "solvable_exchangeTwinCargo_go\n(play induction, 7 kinds)", "proven"),
    ("iffkit", ["wf_exchangeTwinCargo_of_twinLicensed", "twinLicensed_exchangeTwinCargo", "exchangeTwinCargo_exchangeTwinCargo"], "iff side-lemmas\n(WF / license / involution)", "proven"),
    ("H", ["solvable_of_exchange_merge"], "[H] solvable_of_exchange_merge", "sorry"),
    ("Hp", ["solvable_of_exchange_merge_rooted"], "[H'] solvable_of_exchange_merge_rooted", "sorry"),
    ("Hbridge", ["solvable_of_exchange_merge_bridge", "solvable_of_exchange_merge_bridge_flip", "solvable_of_exchange_merge_bridge_full"], "[H] bridge_full\n(assembled)", "modulo"),
    ("Hpbridge", ["solvable_of_exchange_merge_rooted_bridge", "solvable_of_exchange_merge_rooted_bridge_flip", "solvable_of_exchange_merge_rooted_bridge_full"], "[H'] rooted_bridge_full\n(assembled)", "modulo"),
    ("Hcleared", ["solvable_of_exchange_merge_cleared"], "[H] cleared assembly", "modulo"),
    ("Hpcleared", ["solvable_of_exchange_merge_rooted_cleared"], "[H'] rooted cleared assembly", "modulo"),
    ("plyroot", ["exchange_merge_ply_root"], "ply_root (2a)", "proven"),
    ("plyfit", ["exchange_merge_ply_deep_fit"], "ply_deep_fit (2b FIT)", "proven"),
    ("plycorr", ["twinCorr_of_ply"], "twinCorr_of_ply", "proven"),
    ("covers", ["exchangeTwin_eq_mapByTwin_of_covers"], "covers -> twin-swap", "proven"),
    ("hrp", ["ExchangeRiderPrefix", "ExchangeRiderPrefixRooted"], "hrp: rider-prefix norm\nOPEN (commutation)", "premise"),
    ("hdet", ["ExchangeDeepNorm", "ExchangeDeepNormRooted"], "hdet: deep norm\nREFUTED (1-move; detour witnesses)", "refuted"),
    ("hdet2", [], "hdet': iterated detach\nrepair (validated, to prove)", "todo"),
    ("freedom", ["solvable_of_exchange_pileStack"], "freedom-first bridge", "proven"),
    ("steps", ["exchangeTwinCargo_step_pilePile", "exchangeTwinCargo_step_pilePile_root", "exchangeTwinCargo_step_pilePile_passing", "exchangeTwinCargo_step_draw", "exchangeTwinCargo_step_deckStack", "exchangeTwinCargo_step_deckPile", "exchangeTwinCargo_step_stackPile", "exchangeTwinCargo_step_reveal", "exchangeTwinCargo_step_pileStack"], "exchangeTwinCargo_step kit (9)", "proven"),
    ("lictr", ["twinLicensed_apply_pilePile", "twinLicensed_apply_pilePile_root", "twinLicensed_apply_pilePile_passing", "twinLicensed_apply_reveal", "twinLicensed_attach", "twinLicensed_apply_pileStack", "twinLicensed_congr", "twinLicensed_flipSuit"], "license transfers", "proven"),
    ("seatlock", ["canSitOn_hosts_are_twins"], "seat lock\n(canSitOn_hosts_are_twins)", "proven"),
    ("cargotwin", ["cargo_flipSuit"], "cargo_flipSuit", "proven"),
    ("separated", ["solvable_swapTwin_separated", "solvable_swapTwin_separated_back"], "separated replay\n(L1/O3 part i)", "proven"),
    ("boardswap", ["apply_swapTwinBoard_clean"], "apply_swapTwinBoard_clean", "proven"),
    ("cleanwin", ["solvable_of_twinCorr_clean", "solvable_of_twinCorr_clean_back"], "clean window\n(no twin-foundation)", "proven"),
    ("runclean", ["twinCorr_run_clean"], "twinCorr_run_clean", "proven"),
    ("applyclean", ["apply_clean"], "TwinCorr.apply_clean\n(rho-step, 7 kinds)", "proven"),
    ("onsuit", ["apply_pileStack_onsuit"], "verbatim stacking (aligned)", "proven"),
    ("worry", ["apply_stackPile_onsuit"], "worry-back (aligned)", "proven"),
    ("worryrung", ["stackPile_rung"], "worry-back rung derivation", "proven"),
    ("grow", ["apply_pileStack_grow"], "GROWTH step", "proven"),
    ("growX", ["apply_pileStack_grow_X"], "growth -> crossed frame", "proven"),
    ("drain", ["apply_pileStack_catchup"], "CATCH-UP DRAIN", "proven"),
    ("skew", ["rung_of_skew"], "catch-up alignment", "proven"),
    ("rho", ["mapByRho", "mapByRho_topOf", "mapByRho_attach", "mapByRho_detach", "mapByRho_bottomOf", "mapByRho_aboveOf"], "rho-conjugation kit\n(mapByRho)", "proven"),
    ("bare", ["solvable_cargoTwin_exchange_bare"], "bare-twin companion [PROVEN]", "proven"),
    ("backreal", ["exchangeTwinCargo_pilePile_back"], "backward realization", "proven"),
    ("hwin", [], "hwin: THE WINDOW\nOPEN: X-clean steps,\ndeckStack corner, run induction", "todo"),
]

# src, dst, kind, label   (kind: wiring | premise | content | replace)
MANUAL = [
    ("goal", "licensed", "wiring", "wiring pending"),
    ("H", "Hbridge", "wiring", "discharges"),
    ("Hp", "Hpbridge", "wiring", "discharges"),
    ("Hcleared", "hwin", "premise", "hwin premise"),
    ("Hpcleared", "hwin", "premise", "hwin premise"),
    ("Hcleared", "hdet2", "premise", "repair"),
    ("Hpcleared", "hdet2", "premise", "repair"),
    ("hdet", "hdet2", "replace", "superseded by"),
    ("hwin", "cleanwin", "content", "core landed"),
    ("hwin", "separated", "content", "generalizes"),
    ("hwin", "growX", "content", "schedules"),
    ("hwin", "drain", "content", "schedules"),
    ("hwin", "applyclean", "content", "needs X-frame version"),
    ("hwin", "worry", "content", ""),
    ("hwin", "onsuit", "content", ""),
]

FILE_FILL = {
    "TwinExchange.lean": "#FDEBD0",
    "TwinQuotient.lean": "#D6EAF8",
    "TwinBridge.lean": "#D5F5E3",
    "TwinReplay.lean": "#E8DAEF",
}

EDGESTYLE = {
    "auto":     ('color="#85929E"', ""),
    "wiring":   ('color="#2E86C1", style=dashed', "pending"),
    "premise":  ('color="#B7950B", style=dotted', "premise"),
    "content":  ('color="#8E44AD", style=dotted', "content"),
    "replace":  ('color="#7F8C8D", style=dashed', ""),
}


def main():
    decls = parse_declarations()
    print(f"parsed {sum(len(v) for v in decls.values())} declarations "
          f"({len(decls)} distinct names) in {len(list(LEAN_DIR.glob('*.lean')))} files")

    # locate curated nodes
    nodes = {}
    for nid, matchers, label, status in CURATED:
        found = []
        for mname in matchers:
            # exact short name, or dotted decl ending in .name
            for dname, sites in decls.items():
                if dname == mname or dname.endswith("." + mname):
                    found.extend(sites)
        if not found and matchers:
            print(f"  !! MISSING curated node: {nid} ({matchers})")
            continue
        files = [s["file"] for s in found]
        file = max(set(files), key=files.count) if files else None
        line = min(s["line"] for s in found) if found else 0
        nodes[nid] = {
            "label": label, "status": status, "file": file, "line": line,
            "matchers": matchers, "sites": found,
        }

    # auto edges: A cites B
    edges = {}
    for aid, a in nodes.items():
        if not a["sites"]:
            continue
        pat = {}
        for bid, b in nodes.items():
            if bid == aid or not b["matchers"]:
                continue
            p = r"\b(" + "|".join(re.escape(x) for x in
                                  sorted(b["matchers"], key=len, reverse=True)) + r")\b"
            pat[bid] = re.compile(p)
        for site in a["sites"]:
            for bid, p in pat.items():
                if p.search(site["body"]):
                    edges[(aid, bid)] = "auto"

    # manual edges
    for src, dst, kind, lab in MANUAL:
        if src not in nodes or dst not in nodes:
            print(f"  !! manual edge references missing node: {src} -> {dst}")
            continue
        if (src, dst) in edges:
            continue
        edges[(src, dst)] = (kind, lab)

    # --- DOT ---
    def esc(s):
        return s.replace("\\", "\\\\").replace('"', '\\"')

    lines = [
        'digraph theorem_graph {',
        '  graph [rankdir=TB, splines=true, nodesep=0.35, ranksep=0.55,',
        '         fontname="Helvetica", fontsize=14,',
        f'         label="Twin exchange cargo theorem - dependency graph ({len(nodes)} nodes, {len(edges)} edges)", labelloc=t];',
        '  node [fontname="Helvetica", fontsize=10, shape=box, style="rounded,filled", margin="0.12,0.07"];',
        '  edge [fontname="Helvetica", fontsize=8, arrowsize=0.7];',
    ]

    for nid, n in nodes.items():
        fill = FILE_FILL.get(n["file"], "#F2F3F4")
        st = n["status"]
        attrs = [f'fillcolor="{fill}"']
        if st == "goal":
            attrs += ['color="#C0392B"', 'penwidth=2.5', 'fontsize=12',
                      'label="' + esc(n["label"]) + '\\n[SORRY - TwinExchange:1267]"']
        elif st == "sorry":
            attrs += ['color="#C0392B"', 'penwidth=2',
                      'label="' + esc(n["label"]) + '\\n[SORRY]"']
        elif st == "modulo":
            attrs += ['color="#B7950B"', 'style="rounded,filled,dashed"',
                      'label="' + esc(n["label"]) + '\\n[proven mod premises]"']
        elif st == "premise":
            attrs += ['fillcolor="#FCF3CF"', 'color="#B7950B"', 'style="rounded,filled,dashed"']
        elif st == "refuted":
            attrs += ['fillcolor="#F5B7B1"', 'color="#943126"', 'penwidth=2']
        elif st == "todo":
            attrs += ['fillcolor="#FEF9E7"', 'color="#D35400"', 'style="rounded,filled,dashed"']
        loc = f"{n['file']}:{n['line']}" if n["file"] else "planned"
        if "label=" not in " ".join(attrs):
            attrs.append('label="' + esc(n["label"]) + '\\n' + loc + '"')
        else:
            attrs[-1] = attrs[-1][:-1] + '\\n' + loc + '"'
        lines.append(f'  "{nid}" [{", ".join(attrs)}];')

    for (a, b), kind in sorted(edges.items()):
        if isinstance(kind, tuple):
            k, lab = kind
            attr, _ = EDGESTYLE[k]
            labpart = f', label="{lab}"' if lab else ""
            lines.append(f'  "{a}" -> "{b}" [{attr}{labpart}];')
        else:
            attr, _ = EDGESTYLE[kind]
            lines.append(f'  "{a}" -> "{b}" [{attr}];')

    # legend
    lines += [
        '  subgraph cluster_legend {',
        '    label="Legend: fill = file (orange TwinExchange, blue TwinQuotient, green TwinBridge, purple TwinReplay);',
        '           red border = sorry; gold dashed = assembled modulo premises; yellow dashed = open (to prove);',
        '           pink = refuted premise; blue dashed = pending wiring; dotted = premise/content edges";',
        '    style="rounded"; color="#AAAAAA"; fontsize=9;',
        '  }',
        '}',
    ]

    dot = "\n".join(lines)
    OUT_DOT.write_text(dot, encoding="utf-8")
    print(f"wrote {OUT_DOT}")

    for out, fmt, extra in [(OUT_PNG, "png", ["-Gdpi=140"]), (OUT_SVG, "svg", [])]:
        cmd = ["dot", f"-T{fmt}", *extra, str(OUT_DOT), "-o", str(out)]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            print(f"dot failed for {fmt}: {r.stderr}")
            sys.exit(1)
        print(f"wrote {out}")

    print("\nedges:")
    for (a, b), kind in sorted(edges.items()):
        k = kind if isinstance(kind, str) else f"{kind[0]}:{kind[1]}"
        print(f"  {a:12s} -> {b:12s} [{k}]")


if __name__ == "__main__":
    main()
