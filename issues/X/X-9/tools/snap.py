"""snap.py ROOT OUTDIR: run each tool in ROOT and save stdout+stderr+exit to OUTDIR/<n>.txt"""
import subprocess, sys
from pathlib import Path
root, out = Path(sys.argv[1]), Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
T = ["python3", "-B"]
cmds = {
    "docs_check": ["tools/docs.py", "check"],
    "docs_fmt_list": ["tools/docs.py", "fmt", "--list"],
    "pending": ["tools/pending.py"],
    "pending_M9": ["tools/pending.py", "--stage-end", "M9"],
    "ignores": ["tools/ignores.py", "stale"],
    "gap_marks": ["tools/gap_marks.py"],
    "diag_registry": ["tools/diag_codes.py", "--registry"],
    "keywords": ["tools/keywords.py"],
    "spec_sections": ["tools/spec_sections.py", "--check"],
    "spec_coverage": ["tools/spec_sections.py", "--list"],
    "builtin_names": ["tools/builtin_names.py"],
    "default_inits": ["tools/default_inits.py"],
    "spec_examples": ["tools/check_spec_examples.py"],
    "path": ["tools/docs.py", "path", "S-1", "W3-06", "§4.1", "R-90", "A-1", "tools.md §3.2"],
    "refs": ["tools/docs.py", "refs", "S-239"],
    "refs_w": ["tools/docs.py", "refs", "W3-06"],
    "back": ["tools/docs.py", "back", "S-239"],
    "back_w": ["tools/docs.py", "back", "W3-01"],
    "show": ["tools/docs.py", "show", "S-239"],
    "show_w": ["tools/docs.py", "show", "W3-01"],
    "list_w": ["tools/docs.py", "list", "W", "--count"],
    "list_s": ["tools/docs.py", "list", "S", "--count"],
}
only = set(sys.argv[3:])
for name, c in cmds.items():
    if only and name not in only:
        continue
    r = subprocess.run(T + c, cwd=root, capture_output=True, text=True, timeout=900)
    (out / f"{name}.txt").write_text(f"exit {r.returncode}\n--- stdout\n{r.stdout}--- stderr\n{r.stderr}")
    print(name, r.returncode, flush=True)
