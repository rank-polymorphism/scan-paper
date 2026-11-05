#!/usr/bin/env python3
"""Extract the Agda code of the paper into stand-alone modules in agda/.

The literate sources (*.lagda) remain the single source of truth: this script
concatenates their code blocks (shown and hidden alike) in paper order, exactly
as Agda sees them, and distributes them over the output modules below.  The
LaTeX text is dropped; section headings are kept as comments so that the code
can be related to the paper.

In the sources, a LaTeX comment line of the form

    %% agda: Module

directs all subsequent code blocks into the output module Module.  The header
block of every source (imports up to its `module ... where` line) is replaced by
the imports given in OUTPUTS.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "agda"

STDLIB_COMMON = [
    "open import Data.Nat as ℕ",
    "open import Data.Nat.Properties as ℕ",
    "open import Data.Fin as Fin using (Fin; zero; suc; remQuot; combine; toℕ; quotRem)",
    "open import Data.Product as Prod hiding (map; zipWith)",
    "open import Data.Product.Relation.Binary.Pointwise.NonDependent",
    "open import Relation.Binary.PropositionalEquality as Eq hiding ([_])",
    "open import Relation.Binary",
    "open import Function",
]

# Output modules in dependency order: name -> (description, options, imports).
OUTPUTS = {
    "Arrays": (
        "Sections 2.1-2.2: array theory and array operations.",
        [],
        STDLIB_COMMON,
    ),
    "Initial": (
        "Section 2.3: models, the initial model, and initiality.",
        [],
        STDLIB_COMMON + ["", "open import Arrays"],
    ),
    "Vectors": (
        "Section 3.1: scan on vectors, and lemmas about scans of vectors used in Section 5.",
        [],
        STDLIB_COMMON + [
            "open import Data.Fin as F using ()",
            "open import Data.Fin.Properties as Fin using (remQuot-combine)",
            "open import Data.Sum using (inj₁; inj₂)",
            "open import Algebra",
            "",
            "open import Arrays",
            "open import Initial",
        ],
    ),
    "Combinators": (
        "Sections 3.2-3.4: array combinators and generalised scan.",
        [],
        STDLIB_COMMON + [
            "open import Data.Fin.Properties as Fin using (remQuot-combine; combine-remQuot; "
            "toℕ-combine; toℕ-injective; combine-injectiveˡ; combine-injectiveʳ)",
            "open import Algebra",
            "",
            "open import Arrays",
            "open import Initial",
            "open import Vectors",
        ],
    ),
    "Reshaping": (
        "Section 4: reshapes.",
        [],
        STDLIB_COMMON + [
            "open import Data.Fin.Properties as Fin using (remQuot-combine; combine-remQuot; "
            "toℕ-combine; toℕ-injective; combine-injectiveˡ; combine-injectiveʳ)",
            "open import Algebra",
            "",
            "open import Arrays",
            "open import Initial",
            "open import Vectors",
            "open import Combinators",
        ],
    ),
    "Stability": (
        "Sections 3.5 and 5: initial scan, and reshape independence of scan.\n"
        "-- See StabilityNoRewrite.agda for a proof that does not use --rewriting.",
        ["--rewriting"],
        STDLIB_COMMON + [
            "open import Algebra",
            "",
            "open import Arrays",
            "open import Initial",
            "open import Vectors",
            "open import Combinators",
            "open import Reshaping",
        ],
    ),
    "Performance": (
        "Section 6: runtime effects and cost model.",
        ["--rewriting"],
        STDLIB_COMMON + [
            "open import Data.Nat.DivMod",
            "open import Effect.Monad",
            "",
            "open import Arrays",
            "open import Initial",
            "open import Vectors",
            "open import Combinators",
            "open import Reshaping",
            "open import Stability",
        ],
    ),
}

# Sources in paper order with the output module they start in.  Files that
# only contribute to the section numbering have no output module.
SOURCES = [
    ("intro.tex", None),
    ("array.lagda", "Arrays"),
    ("initial.lagda", "Initial"),
    ("combinators.lagda", "Combinators"),
    ("performance.lagda", "Performance"),
]

LOCAL_IMPORT = re.compile(r"^\s*open import (array|initial|vector|combinators)\s*$")
SECTION = re.compile(r"\\(section|subsection|subsubsection)\{(.*)\}\s*$")
MARKER = re.compile(r"^%% agda: (\w+)\s*$")
INPUT = re.compile(r"\\input\{(\w+)\}")

LEVELS = {"section": 0, "subsection": 1, "subsubsection": 2}


def clean_title(title):
    title = re.sub(r"\\label\{[^}]*\}", "", title)
    title = re.sub(r"\\\w+\{([^}]*)\}", r"\1", title)
    return title.strip()


class Extractor:
    def __init__(self):
        self.counters = [0, 0, 0]
        self.path = []               # current headings: [(number, title)] per level
        self.blocks = {name: [] for name in OUTPUTS}
        self.emitted = {name: None for name in OUTPUTS}
        self.sources = {name: [] for name in OUTPUTS}

    def section(self, kind, title):
        lvl = LEVELS[kind]
        self.counters[lvl] += 1
        for k in range(lvl + 1, 3):
            self.counters[k] = 0
        num = ".".join(str(c) for c in self.counters[: lvl + 1])
        self.path = self.path[:lvl] + [(num, clean_title(title))]

    def emit(self, out, src, code):
        if src not in self.sources[out]:
            self.sources[out].append(src)
        lines = self.blocks[out]
        printed = self.emitted[out] or []
        for lvl, h in enumerate(self.path):
            if lvl < len(printed) and printed[lvl] == h:
                continue
            text = f"-- §{h[0]} {h[1]}"
            if lvl == 0:
                bar = "-- " + "=" * (len(text) - 3)
                lines += ["", bar, text, bar, ""]
            else:
                lines += ["", text, "-- " + "-" * (len(text) - 3), ""]
        self.emitted[out] = list(self.path)
        lines += code + [""]

    def process(self, name, out):
        src = (ROOT / name).read_text(encoding="utf-8").splitlines()
        first_block = True
        i = 0
        while i < len(src):
            line = src[i]
            if "\\begin{code}" in line:
                code = []
                i += 1
                while not src[i].lstrip().startswith("\\end{code}"):
                    code.append(src[i])
                    i += 1
                code = [l for l in code if not LOCAL_IMPORT.match(l)]
                if first_block:
                    # Drop the header up to the module declaration; the rest is
                    # emitted with the next block, i.e. after any \input files.
                    k = next(n for n, l in enumerate(code) if re.match(r"^module \S+ where", l))
                    opens = [l for l in code[:k] if re.match(r"^open (?!import)", l)]
                    pending = opens + code[k + 1:]
                    first_block = False
                elif out is not None:
                    self.emit(out, name, pending + code)
                    pending = []
            elif m := MARKER.match(line):
                out = m.group(1)
                assert out in OUTPUTS, out
            elif (m := SECTION.search(line)) and not line.lstrip().startswith("%"):
                self.section(m.group(1), m.group(2))
            elif (m := INPUT.search(line)) and not line.lstrip().startswith("%"):
                self.process(m.group(1) + ".lagda", out)
            i += 1

    def write(self):
        OUT.mkdir(exist_ok=True)
        for name, (descr, options, imports) in OUTPUTS.items():
            srcs = ", ".join(self.sources[name])
            body = self.blocks[name]
            # Collapse runs of blank lines.
            text = re.sub(r"\n{3,}", "\n\n", "\n".join(body).strip("\n")) + "\n"
            head = []
            if options:
                head.append("{-# OPTIONS " + " ".join(options) + " #-}")
            head += [
                "",
                "-- Rank polymorphism at work",
                "-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.",
                "--",
                f"-- {descr}",
                "--",
                f"-- This file is generated from {srcs} by tools/extract-agda.py;",
                "-- section numbers refer to the paper.  Do not edit by hand.",
                "",
            ]
            if "--rewriting" in options:
                head += ["open import Agda.Builtin.Equality.Rewrite", ""]
            head += imports + ["", f"module {name} where", "", ""]
            text = "\n".join(head).lstrip("\n") + text
            text = "\n".join(l.rstrip() for l in text.split("\n"))
            (OUT / f"{name}.agda").write_text(text, encoding="utf-8")
        modules = list(OUTPUTS)
        modules.insert(modules.index("Stability") + 1, "StabilityNoRewrite")
        (OUT / "Everything.agda").write_text("\n".join([
            "{-# OPTIONS --rewriting #-}",
            "",
            "-- Rank polymorphism at work: all modules, in paper order.",
            "-- This file is generated by tools/extract-agda.py.  Do not edit by hand.",
            "",
            *[f"import {m}" for m in modules],
            "",
            "module Everything where",
            "",
        ]), encoding="utf-8")


def main():
    ex = Extractor()
    for name, out in SOURCES:
        if name.endswith(".lagda"):
            ex.process(name, out)
        else:
            for line in (ROOT / name).read_text(encoding="utf-8").splitlines():
                if (m := SECTION.search(line)) and not line.lstrip().startswith("%"):
                    ex.section(m.group(1), m.group(2))
    ex.write()


if __name__ == "__main__":
    sys.exit(main())
