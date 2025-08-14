import sympy as sp
from sympy import Eq, sympify
from typing import Set, List, Dict

class Eq_Converter:
    """
    Converts mathematical equations to SMT-LIB format using SymPy for parsing.
    Supports only equality (==) constraints.
    Outputs as SMT2 files and supports QF_LIA and QF_NIA logics.
    """
    def __init__(self):
        self.variables: Set[str] = set()
        self.sympy_expressions: List[sp.Basic] = [] # Basic is base class for all SymPy expressions
        self.original_equations: List[str] = []

    def _extract_vars(self, expr: sp.Basic) -> Set[str]:
        """Extract variable names from a SymPy expression"""
        return {str(var) for var in expr.free_symbols}

    def _to_smt(self, expr: sp.Basic) -> str:
        """Convert a SymPy expression to SMT-LIB format"""
        if isinstance(expr, (sp.Symbol, sp.Integer)):
            return str(expr)
        elif isinstance(expr, sp.Rational):
            # Convert rationals to division (for integer arithmetic)
            return f"(div {expr.p} {expr.q})"
        elif isinstance(expr, sp.Add):
            args = [self._to_smt(arg) for arg in expr.args]
            if len(args) == 1: # edge case for arbitrary addition, or valid SymPy usage
                return args[0]
            return f"(+ {' '.join(args)})"
        elif isinstance(expr, sp.Mul):
            args = [self._to_smt(arg) for arg in expr.args]
            if len(args) == 1: # edge case for valid SymPy usage
                return args[0]  
            return f"(* {' '.join(args)})"
        elif isinstance(expr, sp.Pow):
            base = self._to_smt(expr.base)
            if isinstance(expr.exp, sp.Integer) and expr.exp >= 0:
                exp = int(expr.exp)
                if exp == 0:
                    return "1"
                if exp == 1:
                    return base
                result = base
                # Convert x^n to repeated multiplication if n > 1
                for _ in range(exp - 1):
                    result = f"(* {base} {result})"
                return result
            else:
                raise ValueError(f"Unsupported exponentiation: {expr}")
        elif isinstance(expr, Eq):
            return f"(= {self._to_smt(expr.lhs)} {self._to_smt(expr.rhs)})"
        elif isinstance(expr, sp.Mod):
            return f"(mod {self._to_smt(expr.args[0])} {self._to_smt(expr.args[1])})"
        else:
            raise ValueError(f"Unsupported expression: {expr}")

    def _parse_equation(self, equation_str: str) -> sp.Basic:
        """Parse a mathematical equation (string) and convert to a SymPy expression"""
        s = equation_str.strip()
        # Reject non-equality operators
        if any(op in s for op in ("!=", "<=", ">=", "<", ">")):
            raise ValueError(f"Only '=' equalities are allowed: {equation_str}")
        if '=' not in s:
            raise ValueError(f"Only '=' equalities are allowed: {equation_str}")
        try:
            left, right = s.split('=', 1)
            expr = Eq(sympify(left.strip()), sympify(right.strip()))
            return expr
        except Exception as e:
            raise ValueError(f"Failed to parse equation '{equation_str}': {e}")

    def _add_expr(self, expr: sp.Basic, original_str: str = None) -> None:
        """Add a SymPy expression to the converter"""
        self.variables.update(self._extract_vars(expr))
        self.sympy_expressions.append(expr)
        self.original_equations.append(original_str or str(expr))

    def add_constraint(self, constraint: str) -> None:
        """Convert a constraint from string to SymPy, then store it"""
        sympy_expr = self._parse_equation(constraint)
        self._add_expr(sympy_expr, constraint)

    def generate_smt_lib(self) -> str:
        """Generate the complete SMT-LIB format string"""
        smt_lines = []

        # Write original constraints as comments
        for equation in self.original_equations:
            smt_lines.append(f"; {equation}")
        smt_lines.append("")

        # Write constant declarations
        for var in sorted(self.variables):
            smt_lines.append(f"(declare-const {var} Int)")
        smt_lines.append("")

        # Write assertions
        for expr in self.sympy_expressions:
            smt_lines.append(f"(assert {self._to_smt(expr)})")
        smt_lines.append("")

        return "\n".join(smt_lines)

    def save_to_file(self, filename: str) -> None:
        """Save SMT-LIB content to an SMT2 file"""
        if not filename.endswith('.smt2'):
            filename += '.smt2'
        with open(filename, 'w') as f:
            f.write(self.generate_smt_lib())
        print(f"SMT-LIB file saved as: {filename}")

    def clear(self) -> None:
        self.variables.clear()
        self.sympy_expressions.clear()
        self.original_equations.clear()

    def get_info(self) -> Dict:
        return {
            'variables': sorted(self.variables),
            'num_equations': len(self.sympy_expressions),
            'equations': self.original_equations
        }

    def execute(self, constraints: List[str], out_file: str = "constraints.smt2") -> str:
        """
        Parse a list of string constraints, store them, and write valid SMT-LIB
        to the given file name (.smt2 extension added if missing).

        Only supports equalities (=).
        Returns the output file path on success; raises ValueError if any constraint fails.
        """
        self.clear()  # Reinitialize the converter

        errors = []
        for i, c in enumerate(constraints, 1):
            try:
                self.add_constraint(c)
            except Exception as e:
                errors.append(f"[constraint {i}] {c!r}: {e}")

        if errors:
            raise ValueError("Failed to add constraints:\n" + "\n".join(errors))

        self.save_to_file(out_file)
        return out_file

if __name__ == "__main__":
    converter = Eq_Converter()
    constraints = [
        "x + y = 10",
        "2*x - 3*y = 5",
        "x**2 + y**2 = 25",
        "z % 2 = 0",
    ]

    output_path = converter.execute(constraints, "example.smt2")
    print("Wrote:", output_path)
