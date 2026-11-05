# Rank polymorphism at work: Agda code

This directory contains the Agda code of the functional pearl

> Artjoms Šinkarovs and Sven-Bodo Scholz.
> *Rank polymorphism at work.*
> Journal of Functional Programming 36, Article 20 (2026).
> [doi:10.46298/jfp.17992](https://doi.org/10.46298/jfp.17992)

The paper, its sources, and a browsable HTML version of this code are available
at <https://rank-polymorphism.github.io/scan-paper/>.

The paper is written in literate Agda.  The modules here contain all of its
code, both the code shown in the paper and the code omitted from it (mostly
proofs), as plain Agda files.  They are organised by paper section, and each
file marks the sections of the paper with comments such as `-- §3.5 Initial scan`.

| File | Paper | Contents |
|------|-------|----------|
| `Arrays.agda` | §2.1–2.2 | Array theory (`Array`), example models, array operations and equality |
| `Initial.agda` | §2.3 | Models, the initial model `I`, lifting from the initial model (`FromInit`) |
| `Vectors.agda` | §3.1 | Scan on vectors; lemmas about scans of vectors over a monoid used in §5 (`Monoid-≡`, `FinScanLemmas`) |
| `Combinators.agda` | §3.2–3.4 | Array combinators (`Comb`, `CombOk`) and the generalised scan (`Scan`) |
| `Reshaping.agda` | §4 | Reshapes (`Rshp`), their properties in the initial model, and their lifting (`FromInitR`) |
| `Stability.agda` | §3.5, §5 | The initial scan (`IS`), the correctness of scans in all models (`scan-ok`), and reshape independence of scan (`scan-thm₁`, `scan-thm₂`) |
| `StabilityNoRewrite.agda` | §3.5, §5 | The same results without rewrite rules (see below) |
| `Performance.agda` | §6 | Effectful scan, left and right nesting, cost model |
| `Everything.agda` | | Imports all of the above |

## Checking the code

The code has been checked with Agda 2.8.0 and the Agda standard library 2.3.
With the standard library registered under the name `standard-library-2.3`,
run

    agda Everything.agda

in this directory.

## Rewrite rules

`Stability.agda` and `Performance.agda` use the `--rewriting` option for a
single rewrite rule: in the initial model, lifting shapes (`⟦_⟧s`) is the
identity.  This holds propositionally, and the rule is justified by a proof
(`⟦⟧s-id` in module `IS`), but turning it into a definitional equality lets us
apply the initial scan to arrays of type `I.Ar s X`, as in the paper.

`StabilityNoRewrite.agda` demonstrates that the rule is a convenience rather
than a necessity.  It proves the main theorems with the same statements and
without `--rewriting`, by stating the intermediate results for arrays of the
lifted shape.  The comment at the top of that file explains the differences.

## Relation to the paper sources

All files except `StabilityNoRewrite.agda` are generated from the literate
sources of the paper by `tools/extract-agda.py` (`make agda` in the paper
repository), so they contain exactly the code checked when building the paper.
A few equations that the paper typesets by hand (for instance, the round-trip
properties of the lifting in §2.3.2 and the definition of `IS` in §3.5) appear
here in their Agda form, which supplies some arguments explicitly.
