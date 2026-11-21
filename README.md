# Sequentially Orderable Proper Edge Colourings

**Author:** Casey Zhang (Independent Researcher, `u6170252806@gmail.com`)

This repository accompanies the paper:

> **Every Proper Edge Colouring of a Connected Graph Other Than $K_2$ or an Even Cycle is Sequentially Orderable**

which resolves **Conjecture 10** of Aleksandra Gorzkowska and Jakub Kwaśny (*"Distinguishing adjacent vertices by ordering edges"*, `arXiv:2609.11832`, 2026).

## Main Result

Every proper edge colouring $w : E(G) \to \mathcal{C}$ of a $2$-connected $d$-regular finite simple graph with $d \ge 3$ is **sequentially orderable**: there exists a strict total order $\prec$ on $E(G)$ such that the induced vertex sequences
$$f_\prec(v) = \bigl(w(e_1), \dots, w(e_d)\bigr) \quad (e_1 \prec \dots \prec e_d \text{ incident with } v)$$
form a proper vertex colouring of $G$. Combined with the results of Gorzkowska and Kwaśny (2026), this proves that $K_2$ and proper $2$-edge-colourings of even cycles are the only connected obstructions.

## Repository Contents

- `paper.tex` / `paper.pdf` — Complete LaTeX manuscript and compiled PDF.
- `SeqOrderable.lean` — Standalone, dependency-free **Lean 4.36.0** formal verification of the main theorem (`SeqOrderable.theorem_regular`), including:
  - Lemma 1 (`final_block_invariance`): deferred final-block suffix invariance,
  - Lemma 2 (`greedy_extension`): greedy spanning-tree extension,
  - Case $d \ge 4$ (`theorem_regular_ge_4`),
  - Lemma 3 (`exists_nonsep_P3`): every $2$-connected cubic simple graph contains a non-separating $P_3$,
  - Case $d = 3$ (`theorem_regular_3`) and unified `theorem_regular`.
- `test_algo.py` — Reference Python implementation and randomized test suite across $d \in \{3, 4, 5, 6\}$.

## Verification

### 1. Lean 4 Formal Proof (Zero External Dependencies)
Tested with **Lean 4.36.0**:
```bash
lean SeqOrderable.lean
```
Expected output:
```text
'SeqOrderable.theorem_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Exit code `0`, zero `sorry`, and only Lean's standard core axioms.

### 2. Constructive Algorithm Test Suite
```bash
python3 test_algo.py
```
Expected output:
```text
ALL <N> TESTS PASSED WITH ZERO ERRORS!
```

### 3. Rebuilding the PDF
```bash
tectonic paper.tex
# or: pdflatex paper.tex && pdflatex paper.tex
```

## Disclosure of AI Assistance

Generative AI assistance (Google Gemini) was used during literature exploration, proof ideation, Lean 4 formalization, and manuscript drafting. All mathematical definitions, proofs, and formal statements were reviewed and verified by the author.
