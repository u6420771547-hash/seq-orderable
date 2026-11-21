# Sequentially Orderable Proper Edge Colourings

[![Lean 4.36.0](https://img.shields.io/badge/Lean-4.36.0-blue)](https://lean-lang.org/)

**Author:** Casey Zhang (Independent Researcher, `u6170252806@gmail.com`)

This repository contains the LaTeX manuscript, standalone Lean 4 formal verification, and reference constructive algorithm for the paper:

> **Every Proper Edge Colouring of a Connected Graph Other Than $K_2$ or an Even Cycle is Sequentially Orderable**

which resolves **Conjecture 10** of Aleksandra Gorzkowska and Jakub Kwaśny (*"Distinguishing adjacent vertices by ordering edges"*, [arXiv:2609.11832](https://arxiv.org/abs/2609.11832), 2026).

---

## Main Result

Let $G$ be a finite simple graph with a proper edge colouring $w : E(G) \to \mathcal{C}$. A strict total order $\prec$ on $E(G)$ induces at each vertex $v \in V(G)$ the sequence of incident edge colours
$$f_\prec(v) = \bigl(w(e_1), w(e_2), \dots, w(e_{d_G(v)})\bigr), \qquad e_1 \prec e_2 \prec \dots \prec e_{d_G(v)}.$$
We call $w$ **sequentially orderable** if there exists a strict total order $\prec$ on $E(G)$ such that $f_\prec$ is a proper vertex colouring ($f_\prec(x) \neq f_\prec(y)$ for every edge $xy \in E(G)$).

- **Theorem 1 (Formally Verified in `SeqOrderable.lean`):** For every integer $d \ge 3$, every proper edge colouring of a $2$-connected $d$-regular finite simple graph is sequentially orderable.
- **Corollary 2 (Resolution of Conjecture 10):** Every proper edge colouring of a connected graph other than $K_2$ or an even cycle is sequentially orderable. More generally, a proper edge colouring $w$ of a connected graph $G$ fails to be sequentially orderable if and only if $G \cong K_2$ or $G$ is an even cycle with $|w(E(G))| = 2$.

---

## Proof Overview

The proof is completely deterministic and constructive for all $d \ge 3$ (replacing the earlier Lovász Local Lemma argument for $d \ge 6$ and settling the open cases $d \in \{3, 4, 5\}$):

1. **Final-Block Suffix Invariance (Lemma 1):** Fix a vertex $v$ with neighbours $u_1, \dots, u_d$ and defer $B = \{v u_2, \dots, v u_d\}$ to a *final block* placed after all edges of $E(G - v) \cup \{v u_1\}$. Because $G$ is simple, each vertex in $G - v$ touches at most one edge of $B$, so permuting $B$ leaves all vertex sequences in $G - v$ unchanged while yielding $(d - 1)!$ pairwise distinct sequences for $v$.
2. **Greedy Extension (Lemma 2):** Process $G - v$ toward the root $u_1$ along an elimination ordering and insert $v u_1$ before $B$ to distinguish $u_1$ from its $d - 1$ neighbours in $G - v$. For all **$d \ge 4$**, $(d - 1)! > d$, so at least one permutation of $B$ avoids all $d$ neighbour sequences of $v$.
3. **Non-Separating $P_3$ Lemma (Lemma 3) & Cubic Case ($d = 3$):** Every $2$-connected cubic simple graph contains a $3$-vertex path $u_2 - v - u_3$ whose removal leaves a connected graph $K = G - \{v, u_2, u_3\}$. Ordering $S_2 = E_{G-v}(u_2) \cup E_{G-v}(u_3)$ by placing all edges of colour $\neq w(v u_1)$ before edges of colour $w(v u_1)$ guarantees that neither $u_2$ nor $u_3$ begins with $w(v u_1)$ and that $f^*(u_2) \neq f^*(u_3)$. Extending greedily on $K$ leaves at most $u_1$ able to conflict with the two candidate orderings of $B = \{v u_2, v u_3\}$.

---

## Repository Contents

| File | Description |
|---|---|
| `paper.tex` / `paper.pdf` | Publication-ready LaTeX manuscript and compiled PDF |
| `SeqOrderable.lean` | Standalone, zero-dependency Lean 4 (v4.36.0) formal proof of Theorem 1 (`SeqOrderable.theorem_regular`) |
| `test_algo.py` | Reference Python implementation and randomized test suite across $d \in \{3, 4, 5, 6\}$ |

---

## Verification & Reproduction

### 1. Lean 4 Formal Proof (Zero External Dependencies)

`SeqOrderable.lean` requires no external packages (no Mathlib). Verified with **Lean 4.36.0**:

```bash
lean SeqOrderable.lean
```

Expected output (exit code `0`, zero `sorry`):

```text
'SeqOrderable.theorem_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Key formalized theorems:
- `SeqOrderable.final_block_invariance` — Lemma 1 (Final-Block Suffix Invariance)
- `SeqOrderable.greedy_extension` — Lemma 2 (Greedy Extension with Deferred Final Block)
- `SeqOrderable.theorem_regular_ge_4` — Theorem 1 for all $d \ge 4$
- `SeqOrderable.exists_nonsep_P3` — Lemma 3 (Non-Separating $P_3$ Lemma)
- `SeqOrderable.theorem_regular_3` — Theorem 1 for $d = 3$
- `SeqOrderable.theorem_regular` — Unified Theorem 1 for all $d \ge 3$

### 2. Constructive Algorithm Test Suite

```bash
python3 test_algo.py
```

### 3. Rebuilding the PDF

```bash
tectonic paper.tex
# or: pdflatex paper.tex && pdflatex paper.tex
```

---

## Disclosure of AI Assistance

Generative AI assistance (Google Gemini) was used during literature exploration, proof ideation, Lean 4 formalization, and manuscript drafting. All mathematical definitions, proofs, and formal statements were reviewed and verified by the author, who takes full responsibility for this work.

## License

The Lean 4 formalization and Python reference implementation are released under the MIT License (see `LICENSE`).
