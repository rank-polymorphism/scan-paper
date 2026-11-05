This repository contains the sources of the functional pearl

> Artjoms Šinkarovs and Sven-Bodo Scholz.
> *Rank polymorphism at work.*
> Journal of Functional Programming 36, Article 20 (2026).
> [doi:10.46298/jfp.17992](https://doi.org/10.46298/jfp.17992)

The paper, and a browsable HTML version of its Agda code, are available at
<https://rank-polymorphism.github.io/scan-paper/>.

The paper is written in [Literate Agda](https://agda.readthedocs.io/en/v2.8.0/tools/literate-programming.html),
which means that the paper sources contain both the text of the paper and
the source code described in it.  The directory `agda/` contains the same code
as plain Agda modules, organised by paper section; see `agda/README.md`.

## Building

* `make` builds the paper (`paper.pdf`).
* `make agda` extracts the Agda code into `agda/` and checks it.
* `make docs` generates the web page in `docs/`: a copy of the paper and the
  HTML version of the code in `agda/`.

The following dependencies are needed:

* Agda version 2.8.0
* Agda standard library version 2.3, registered as `standard-library-2.3`
* `pdflatex` and `latexmk` (any recent version should do, e.g. pdflatex from
  TeX Live 2023, and latexmk version 4.83), including the TeX Gyre fonts
  (the `tex-gyre` package on Debian)
* Python 3, for `make agda`
