"""mut.py TOOLS SCRATCH: copy tools/ to SCRATCH, apply each mutation of docs.py, run the graph self-tests, print which fail."""
import shutil, subprocess, sys
from pathlib import Path

tools, scratch = Path(sys.argv[1]), Path(sys.argv[2])
MUTS = {
    "self-edge kept": ('        if on != base:  # an edge', '        if True:  # an edge'),
    "tasks turned": ('"tasks": False', '"tasks": True'),
    "before turned": ('"before": False', '"before": True'),
    "no stage edges": ('add(work.split("-")[0], work, STAGE_EDGE)', 'pass'),
    "more counts nothing": ('                    more += 1', '                    pass'),
    "typed last": ('return not typed_edge(edge[1]), edge[1] == MENTION, node_key(edge[0]), edge[1]', 'return typed_edge(edge[1]), node_key(edge[0])'),
    "text(key) after text": ('edge[1] == MENTION, node_key', 'edge[1] != MENTION, node_key'),
    "paths first": ('return (1, node.as_posix()) if isinstance(node, Path) else (0, id_key(node))',
                    'return (0, node.as_posix()) if isinstance(node, Path) else (1, id_key(node))'),
    "no check (c)": ('    for readme, line, key in undirected(tree):\n        yield', '    for readme, line, key in []:\n        yield'),
}
for name, (old, new) in MUTS.items():
    d = scratch / "mut"
    if d.exists():
        shutil.rmtree(d)
    shutil.copytree(tools, d, ignore=shutil.ignore_patterns("__pycache__"))
    p = d / "docs.py"
    text = p.read_text()
    assert text.count(old) == 1, name
    p.write_text(text.replace(old, new))
    r = subprocess.run(["python3", "-B", str(d / "test_gate.py"), "DocsCommands.test_graph", "DocsCommands.test_graph_edges",
                        "DocsLayout.test_check_relations"], capture_output=True, text=True, timeout=120)
    fails = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith(("FAIL:", "ERROR:"))]
    print(f"{name}: exit {r.returncode}, {len(fails)} failing: {', '.join(f.split()[1] for f in fails)}")
shutil.rmtree(scratch / "mut")
