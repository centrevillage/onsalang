"""Count added and removed lines outside the test modules (and outside tests/ files).
Usage: count.py <repo> <base>"""
import re, subprocess, sys

repo, base = sys.argv[1], sys.argv[2]
out = subprocess.run(['git', '-C', repo, 'diff', '-U0', base, '--', 'crates'], capture_output=True, text=True).stdout
untracked = subprocess.run(['git', '-C', repo, 'ls-files', '--others', '--exclude-standard', 'crates'], capture_output=True, text=True).stdout.split()

def test_start(path):
    try:
        lines = open(f'{repo}/{path}').read().split('\n')
    except FileNotFoundError:
        return 10**9
    for i, l in enumerate(lines, 1):
        if l.startswith('#[cfg(test)]'):
            return i
    return 10**9

total_add = total_del = 0
file = None
start = None
per = {}
for line in out.split('\n'):
    if line.startswith('+++ '):
        file = line[6:] if line != '+++ /dev/null' else None
        start = test_start(file) if file else None
        continue
    m = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', line)
    if m:
        new = int(m.group(3))
        continue
    if file is None or '/tests/' in file or file.endswith('/tests.rs'):
        continue
    if line.startswith('+') and not line.startswith('+++'):
        if new < start:
            per.setdefault(file, [0, 0])[0] += 1
        new += 1
    elif line.startswith('-') and not line.startswith('---'):
        per.setdefault(file, [0, 0])[1] += 1
for f in untracked:
    if not f.endswith('.rs'):
        continue
    n = min(test_start(f) - 1, len(open(f'{repo}/{f}').read().split('\n')))
    per[f] = [n, 0]
for f, (a, d) in sorted(per.items()):
    print(f'{f}: +{a} -{d}')
    total_add += a; total_del += d
print(f'total: +{total_add} -{total_del}')
