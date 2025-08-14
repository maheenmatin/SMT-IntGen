from __future__ import annotations
import random
from typing import List, Optional

class Eq_Creator:
    """
    Random equation generator for integer (QF_LIA or QF_NIA) logics.

    Parameters
    ----------
    total_vars : int
        Number of variables to use (variables will be a, b, ..., up to 26 max).
    max_deg : int
        Maximum degree (inclusive). For QF_LIA, this will be forced to 1 internally.
    max_eq : int
        Number of equations to generate per constraint set.
    max_co : int
        Maximum absolute value of coefficients (inclusive).
    total_tests : int
        Number of separate constraint sets to generate in generate_all().
    logic : str
        "QF_LIA" or "QF_NIA".
        - QF_LIA: strictly linear constraints (degree=1; no products of distinct vars).
        - QF_NIA: allows products and powers up to max_deg.
    complex_bias : bool, optional
        If False: spread choices across ranges (more variety).
        If True: skew toward max/near-max (larger degree, more terms, bigger coefficients).
    seed : Optional[int], optional
        Seed for reproducible randomness. If None, a random seed is chosen and stored in self.seed_used.
    """

    def __init__(
        self,
        total_vars: int,
        max_deg: int,
        max_eq: int,
        max_co: int,
        total_tests: int,
        logic: str,
        complex_bias: bool = False,
        seed: Optional[int] = None,
    ):
        if not (1 <= total_vars <= 26):
            raise ValueError("total_vars must be >= 1 and <= 26 (variables are a...z)")
        if max_deg < 1:
            raise ValueError("max_deg must be >= 1")
        if max_eq < 1:
            raise ValueError("max_eq must be >= 1")
        if max_co < 1:
            raise ValueError("max_co must be >= 1")
        if logic not in {"QF_LIA", "QF_NIA"}:
            raise ValueError("logic must be one of {'QF_LIA', 'QF_NIA'}")

        self.total_vars = total_vars
        self.max_deg = max_deg
        self.max_eq = max_eq
        self.max_co = max_co
        self.total_tests = total_tests
        self.complex_bias = complex_bias
        self.logic = logic

        # Seed handling
        if seed is None:
            seed = random.randrange(2**31 - 1)
        self.seed_used = seed
        self._rng = random.Random(seed)

        # Variable names: a, b, c, ...
        self.vars = [chr(ord('a') + i) for i in range(total_vars)]

    def generate_constraint_set(self) -> List[str]:
        """
        Generate a single list of equality constraints (as strings).
        """
        equations: List[str] = []
        eff_logic = self.logic

        for _ in range(self.max_eq):
            # Ensure the LHS is not a pure constant
            lhs = self._random_expression(eff_logic, require_variable=True)
            rhs = self._random_rhs(eff_logic)
            equations.append(f"{lhs} = {rhs}")

        return equations

    def generate_all(self) -> List[List[str]]:
        """
        Generate multiple constraint sets (total_tests).
        Returns a list of constraint sets, each being a list of equation strings.
        """
        return [self.generate_constraint_set() for _ in range(self.total_tests)]

    def _rand_coeff(self) -> int:
        # Avoid zero to keep terms meaningful - allow negative coefficients
        mag = self._biased_int(1, self.max_co, prefer_high=self.complex_bias)
        sign = -1 if self._rng.random() < 0.5 else 1
        return sign * mag

    def _biased_int(self, lo: int, hi: int, prefer_high: bool) -> int:
        """
        Returns an int in [lo, hi] with optional bias:
        - prefer_high=False: roughly uniform
        - prefer_high=True: skew towards hi (by sampling max of a few draws)
        """
        if lo == hi:
            return lo
        if not prefer_high:
            return self._rng.randint(lo, hi)
        # Bias: take the max of multiple draws to skew upward
        draws = [self._rng.randint(lo, hi) for _ in range(3)]
        return max(draws)

    def _rand_var(self) -> str:
        idx = self._biased_int(0, len(self.vars) - 1, prefer_high=self.complex_bias)
        return self.vars[idx]

    def _rand_degree(self, eff_logic: str) -> int:
        if eff_logic == "QF_LIA":
            return 1
        return self._biased_int(1, self.max_deg, prefer_high=self.complex_bias)

    def _rand_term_LIA(self, allow_constant: bool = True) -> str:
        """
        Linear term: c * v  OR just v  OR integer constant (occasionally).
        """
        r = self._rng.random()
        if allow_constant and r < 0.15:
            # constant term
            return str(self._rng.randint(-self.max_co, self.max_co))
        v = self._rand_var()
        c = self._rand_coeff()
        if c == 1:
            return v
        if c == -1:
            return f"-{v}"
        return f"{c}*{v}"

    def _rand_term_NIA(self, allow_constant: bool = True) -> str:
        """
        Nonlinear term: c * (product of variables with exponents) OR a constant sometimes.
        """
        if allow_constant and self._rng.random() < 0.12:
            return str(self._rng.randint(-self.max_co, self.max_co))

        # With complex_bias: more vars per monomial
        # Hard cap at 3 variables; "rarely" allow 4 when complex_bias=True (5% chance).
        base_cap = min(3, self.total_vars)
        allow_four = (
            self.complex_bias
            and self.total_vars >= 4
            and self._rng.random() < 0.05  # 5% chance to go to 4 variables
        )
        max_factors = 4 if allow_four else base_cap
        num_factors = self._biased_int(1, max_factors, prefer_high=self.complex_bias)

        # Choose distinct variables if possible
        if num_factors <= len(self.vars):
            chosen = self._rng.sample(self.vars, k=num_factors)
        else:
            # Fallback if ever requested more than available
            chosen = [self._rand_var() for _ in range(num_factors)]

        deg_cap = self._rand_degree("QF_NIA")
        factors: List[str] = []
        for v in chosen:
            deg = self._biased_int(1, deg_cap, prefer_high=self.complex_bias)
            factors.append(v if deg == 1 else f"{v}**{deg}")

        prod = "*".join(factors) if len(factors) > 1 else factors[0]

        # Prepend coefficient (may be ±1)
        c = self._rand_coeff()
        if c == 1:
            return prod
        if c == -1:
            return f"-{prod}"
        return f"{c}*{prod}"

    def _rand_sum(self, eff_logic: str, allow_constant: bool = True) -> str:
        """
        Create a sum of 2..N terms (N higher if complex_bias).
        """
        hi_terms = 5 if self.complex_bias else 3
        num_terms = self._biased_int(2, hi_terms, prefer_high=self.complex_bias)

        terms: List[str] = []
        for _ in range(num_terms):
            if eff_logic == "QF_LIA":
                t = self._rand_term_LIA(allow_constant=allow_constant)
            else:
                # Mostly nonlinear terms in NIA, but sprinkle linear ones
                if self._rng.random() < 0.8:
                    t = self._rand_term_NIA(allow_constant=allow_constant)
                else:
                    t = self._rand_term_LIA(allow_constant=allow_constant)
            terms.append(t)

        expr = " + ".join(terms)
        expr = expr.replace("+ -", "- ")
        return expr

    def _random_expression(self, eff_logic: str, require_variable: bool = False) -> str:
        """
        Build a left-hand side expression:
        - Mostly sums of terms
        - Occasionally a single term
        If require_variable=True, do not allow pure-constant expressions.
        """
        # Single term branch
        if self._rng.random() < 0.2:
            if eff_logic == "QF_LIA":
                return self._rand_term_LIA(allow_constant=not require_variable)
            else:
                return self._rand_term_NIA(allow_constant=not require_variable)

        # Sum branch
        return self._rand_sum(eff_logic, allow_constant=not require_variable)

    def _random_rhs(self, eff_logic: str) -> str:
        """
        Right-hand side:
        - Often an integer constant (keeps constraints solvable-looking)
        - Sometimes another expression (to vary structure)
        """
        r = self._rng.random()
        if r < 0.6:
            # integer constant in [-max_co*2, max_co*2]
            span = max(2, self.max_co * 2)
            return str(self._rng.randint(-span, span))
        elif r < 0.85:
            return self._rand_term_LIA() if eff_logic == "QF_LIA" else self._rand_term_NIA()
        else:
            # short expression - temporarily soften bias on RHS
            old_bias = self.complex_bias
            try:
                self.complex_bias = False
                return self._rand_sum(eff_logic)
            finally:
                self.complex_bias = old_bias

if __name__ == "__main__":
    creator = Eq_Creator(
        total_vars=5,
        max_deg=3,
        max_eq=4,
        max_co=7,
        total_tests=2,
        logic="QF_NIA",
        complex_bias=True,
        seed=None
    )

    print(f"Seed used: {creator.seed_used}")
    all_sets = creator.generate_all()
    for i, eqs in enumerate(all_sets, 1):
        print(f"\n=== Constraint Set {i} ===")
        for e in eqs:
            print(e)
