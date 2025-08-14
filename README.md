# Welcome to SMT-IntGen!

**SMT-IntGen** is a Python tool for the automated generation SMT-LIB encoded problems, conforming to linear and non-linear integer arithmetic logics.
---

### 🧰 Installation

1. **Clone the repository:**
   ```bash
   git clone https://github.com/maheenmatin/SMT-IntGen
   cd SMT-IntGen
   ```

2. **Optional: Install Poetry** (if not already installed):
   ```bash
   pipx install poetry
   ```

3. **Install dependencies:**
   ```bash
   poetry install
   ```

4. **Activate virtual environment:**
   ```bash
   poetry env activate
   ```

5. **Run solver:**
   ```bash
   poetry run python -m smt-intgen.eq_converter
   # or
   poetry run python -m smt-intgen.eq_creator
   # or
   poetry run python -m smt-intgen.benchmark_generator
   ```

**Notes:**
- Mathematical equations used as input must conform to QF_LIA or QF_NIA rules for functional SMT-LIB code
- Equations are not parsed to ensure correctness. For example, rational numbers that result in non-integers, e.g. `3/4` must not be used.
- SymPy-appropriate syntax must be used:
   - `*` is used for multiplication
   - `
- Does not catch non-algebraic nonlinearities, e.g. `sin(x)` or `log(x)`
