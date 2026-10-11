#!/usr/bin/env python3
"""Scan ansatz specs / exponents a with search.run; prints one line per run."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search as S
m = int(sys.argv[1]); a = float(sys.argv[2]); nball = int(sys.argv[3])
for line in sys.argv[4:]:
    spec = S.parse_spec(line.split())
    r = S.run(m, a, spec, n_ball=nball, verbose=False)
    nb = len(r["basis"])
    print(f"a={a} [{line}] nb={nb} t_sdp={r['t_sdp']:.4f} dense={r['dense_margin']:.4f} minS={r['dense_minS']:.4f} ({r['time']:.0f}s)", flush=True)
