from pathlib import Path
import re

pattern = re.compile(r"set_option\s+(linter\.[A-Za-z0-9_.]+)\s+false")

root = Path("FormalQualBench")

for path in root.rglob("*.lean"):
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        m = pattern.search(line)
        if m:
            print(f"{path}:{lineno}: {m.group(1)}")