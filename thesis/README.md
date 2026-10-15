# Thesis

This directory contains the thesis source, independent of the Lean library and
the leanblueprint roadmap. The starting point is the supplied University of Bonn
mathematics master's thesis title-page template, not a complete thesis class.

## Files

- `main.tex`: entry point, adapted from the supplied `myThesis.tex`. Replace the
  example author, birth details, submission date, advisors, institute, and title.
- `MA_Titlepage.sty`: the original title-page package, preserved unchanged.
- `README.upstream.txt`: the original instructions, preserved unchanged. Its
  reference to `MA_Titelseite.sty` is a typo; use `MA_Titlepage.sty` and
  `\usepackage{MA_Titlepage}`, as in `main.tex`.

The template deliberately inserts a blank page after the cover. Its current
document class is `article`, which uses `\section`; `\chapter` would require a
different class and a fresh layout check. Add the contents and body after
`\maketitle`. As the text grows, it can be split into `chapters/` with `\input`;
add a bibliography when citations are introduced.

## Local compilation

From the repository root:

```sh
cd thesis
pdflatex -no-shell-escape -synctex=1 -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -no-shell-escape -synctex=1 -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -synctex=1 -interaction=nonstopmode -halt-on-error main.tex
```

The result is `thesis/main.pdf`. BibTeX reads `references.bib`; the two subsequent
LaTeX passes resolve citations and cross-references. The current cover requires only standard LaTeX and English
`babel`; it was verified with TeX Live 2026 Basic. Neither `latexmk` nor Biber is
required. On this Mac, the TeX binaries are in `/Library/TeX/texbin`.

For VS Code, open the repository folder and then `thesis/main.tex`. The existing
local LaTeX Workshop configuration provides the `pdflatex + bibtex + pdflatex x2` recipe. Run
**LaTeX Workshop: Build LaTeX project**, then **LaTeX Workshop: View LaTeX PDF
file**. Automatic compilation on save is currently disabled. The repository's
`.vscode/` directory is intentionally untracked, so this editor configuration
does not travel with a fresh clone; the terminal commands above do.

Codex's built-in single-document compiler currently cannot load the adjacent
custom `MA_Titlepage.sty` file. Use the local commands or VS Code for compilation
and open the resulting PDF; a missing-package error in the built-in preview
does not indicate a failure of the local project.

The adjacent `.gitignore` excludes compilation products and editor backups.
Figure PDFs remain trackable. This directory is not built by `lake build` or
the blueprint workflow.
