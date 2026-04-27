[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Almost all primes are partially regular

These files accompany the paper [arXiv:xxxx](https://arxiv.org/abs/xxxxx).

The formal proofs provided in this work were developed and verified using **Lean 4.28.0**. Compatibility with earlier or later versions is not guaranteed due to the evolving nature of the Lean 4 compiler and its core libraries.

## Input files

### Theorem 1

- [`task.md`](input/theorem1/task.md): natural language description of the problem
- [`.environment`](input/theorem1/.environment): specifies the Lean version

### Theorem 2 and Theorem 3

- [`task.md`](input/theorem2and3/task.md): natural language description of the problem
- [`.environment`](input/theorem2and3/.environment): specifies the Lean version
- [`source.tex`](input/theorem2and3/source.tex)
- [`theorem1.lean`](input/theorem2and3/theorem1.lean): this file is a verbatim copy of [`solution.lean`](Biswal/theorem1/solution.lean) in `Biswal/theorem1/solution.lean`.

## Output files (Run with Lean 4.26.0)

### Theorem 1

- [`problem.lean`](Biswal/theorem1/problem.lean): translation of the problem statement into formal language (Lean)
- [`solution.lean`](Biswal/theorem1/solution.lean): solution in formal language (Lean)

### Theorem 2 and Theorem 3

- [`problem.lean`](Biswal/theorem2and3/problem.lean): translation of the problem statement into formal language (Lean)
- [`solution.lean`](Biswal/theorem2and3/solution.lean): solution in formal language (Lean)

## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.

## Repository maintainers

- [Evan Chen](https://github.com/vEnhance)
- [Kenny Lau](https://github.com/kckennylau)
- [Seewoo Lee](https://github.com/seewoo5)
- [Ken Ono](https://github.com/kenono691)
- [Jujian Zhang](https://github.com/jjaassoonn)
