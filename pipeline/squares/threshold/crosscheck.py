"""Cross-check the exported strategy tables against each other.

The Lean development, the site, and the reference verifier each carry
their own copy of the tables. This module reads the Lean data files
back into the pipeline's shape and compares them with the site's
tables.json and the generated Python module, so a stale export fails
here rather than letting the verifiers judge different strategies.

python3 -m squares.threshold.crosscheck exits nonzero on any mismatch.
"""

import json
import re
import sys

from ..paths import LEAN_DATA, SITE_TABLES
from . import strategy5
from .export_site import table_json

_TOKEN = re.compile(r"\s*(\d+|[A-Za-z][A-Za-z0-9_.]*|[(),\[\]])")


def _tokens(src):
    pos = 0
    while pos < len(src):
        m = _TOKEN.match(src, pos)
        if not m:
            raise ValueError(f"unexpected Lean syntax at {src[pos : pos + 20]!r}")
        pos = m.end()
        yield m.group(1)
    yield None


class _Parser:
    def __init__(self, src):
        self.toks = _tokens(src)
        self.cur = next(self.toks)

    def take(self, expected=None):
        tok = self.cur
        if expected is not None and tok != expected:
            raise ValueError(f"expected {expected!r}, found {tok!r}")
        self.cur = next(self.toks)
        return tok

    def value(self):
        tok = self.cur
        if tok == "(":
            self.take()
            first = self.value()
            self.take(",")
            second = self.value()
            self.take(")")
            return (first, second)
        if tok == "[":
            self.take()
            items = []
            while self.cur != "]":
                items.append(self.value())
                if self.cur == ",":
                    self.take()
            self.take("]")
            return items
        if tok.isdigit():
            return int(self.take())
        self.take()
        if tok == "Key.cell":
            return self.value()
        if tok == "Key.row":
            return ("row", self.value())
        if tok == "Key.col":
            return ("col", self.value())
        if tok == "Key.farm":
            return ("farm", self.value())
        if tok == "Key.dflt":
            return None
        if tok == "Entry.plan":
            return tuple(self.value())
        if tok == "Entry.quiet":
            move = self.value()
            branches = self.value()
            return ("q", move, dict(branches))
        raise ValueError(f"unknown Lean constructor {tok!r}")


def read_lean_table(path):
    """The (opening, box, x2, scripts) a Lean data file defines."""
    src = path.read_text()
    defs = re.findall(r"^def (\w+) : [^\n]* := (\[.*?^\])", src, re.S | re.M)
    x2 = None
    chunks = []
    for name, body in defs:
        value = _Parser(body).value()
        if name.endswith("X2"):
            x2 = dict(value)
        else:
            chunks.extend(value)
    header = re.search(r"⟨\((\d+), (\d+)\), (\d+), ", src)
    opening = (int(header.group(1)), int(header.group(2)))
    return opening, int(header.group(3)), x2, {k: dict(v) for k, v in chunks}


def main():
    site = json.loads(SITE_TABLES.read_text())
    lean = {
        "general": table_json(*read_lean_table(LEAN_DATA / "TableGen.lean")),
        "five": table_json(*read_lean_table(LEAN_DATA / "Table5.lean")),
    }
    python = {"five": table_json((2, 2), 5, strategy5.X2, strategy5.SCRIPTS)}
    failures = [name for name in lean if lean[name] != site[name]]
    failures += [f"{name} (python)" for name in python if python[name] != lean[name]]
    for name in failures:
        print(f"mismatch: {name}")
    if failures:
        sys.exit(1)
    print("Lean, site, and Python tables agree")


if __name__ == "__main__":
    main()
