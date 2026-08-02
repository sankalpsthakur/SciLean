#!/usr/bin/env bash
set -euo pipefail

candidate="$(find . -type f -name '*.lean' | grep -Ei 'harmonic.*oscillator|oscillator.*harmonic' | head -n 1 || true)"
if [ -z "$candidate" ]; then
  candidate="$(grep -Ril --include='*.lean' 'harmonic oscillator' . | head -n 1 || true)"
fi
if [ -z "$candidate" ]; then
  echo "Could not locate the existing harmonic oscillator example" >&2
  exit 1
fi
rel="${candidate#./}"

python3 - "$rel" <<'PY'
from pathlib import Path
import sys

example = sys.argv[1]
readme = Path("README.md")
text = readme.read_text()
link = f"- [Harmonic oscillator example]({example}) — an end-to-end SciLean scientific-computing example."
if link in text:
    raise SystemExit(0)

heading = "## Examples"
if heading in text:
    pos = text.index(heading) + len(heading)
    text = text[:pos] + "\n\n" + link + text[pos:]
else:
    text = text.rstrip() + f"\n\n{heading}\n\n{link}\n"
readme.write_text(text)
PY

rm -f .agent-patch.sh .github/workflows/agent-apply-harmonic-docs.yml

git config user.name "Sankalp Thakur"
git config user.email "sankalphimself@gmail.com"
git add -A
if git diff --cached --quiet; then
  exit 0
fi
git commit -m "docs: surface the harmonic oscillator example"
git push --force origin HEAD:"${GITHUB_REF_NAME}"
