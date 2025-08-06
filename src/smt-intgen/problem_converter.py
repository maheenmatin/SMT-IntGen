import re
import os
from typing import List, Set, Dict, Tuple, Optional, Union
from enum import Enum
import sympy as sp
from sympy import symbols, sympify, Eq, And, Or, Not
from sympy import Gt, Lt, Ge, Le, Ne
from sympy.core.relational import Relational
from sympy.logic.boolalg import BooleanFunction

class SMTLogic(Enum):
    QF_LIA = "QF_LIA" # Quantifier-Free Linear Integer Arithmetic
    QF_NIA = "QF_NIA" # Quantifier-Free Nonlinear Integer Arithmetic

class SMTEquationConverter:
    """
    Converts mathematical equations to SMT-LIB format using SymPy for parsing.
    Outputs as SMT2 files and supports QF_LIA and QF_NIA logics.
    """
    def __init__(self, logic: SMTLogic = SMTLogic.QF_LIA):
        self.logic = logic
        self.variables: Set[str] = set()
        self.sympy_expressions: List[sp.Basic] = [] # Basic is base class for all SymPy expressions
        self.original_equations: List[str] = []
        
    def extract_variables_sympy(self, expr: sp.Basic) -> Set[str]:
        """Extract variable names from a SymPy expression"""
        return {str(var) for var in expr.free_symbols}
    
    def is_nonlinear_sympy(self, expr: sp.Basic) -> bool:
        """Check if a SymPy expression contains nonlinear terms"""
        # Modulo is nonlinear in SMT logic
        if expr.has(sp.Mod):
            return True
        # Check polynomial degree for each variable
        for var in expr.free_symbols:
            try:
                # Attempt to create a polynomial
                poly = sp.Poly(expr, var)
                if poly.degree() > 1:
                    return True
            except (sp.PolynomialError, sp.GeneratorsNeeded):
                # If polynomial cannot be created, it still might be nonlinear
                # So check for multiplication of variables
                if expr.has(sp.Mul) and len([arg for arg in expr.args if arg.has(var)]) > 1:
                    return True
        return False
    
    def sympy_to_smtlib(self, expr: sp.Basic) -> str:
        """Convert a SymPy expression to SMT-LIB format"""
        if isinstance(expr, (sp.Symbol, sp.Integer)):
            return str(expr)
        elif isinstance(expr, sp.Rational):
            # Convert rationals to division (for integer arithmetic)
            return f"(div {expr.p} {expr.q})"
        elif isinstance(expr, sp.Add):
            args = [self.sympy_to_smtlib(arg) for arg in expr.args]
            if len(args) == 1: # edge case for arbitrary addition, or valid SymPy usage
                return args[0]
            return f"(+ {' '.join(args)})"
        elif isinstance(expr, sp.Mul):
            args = [self.sympy_to_smtlib(arg) for arg in expr.args]
            if len(args) == 1: # edge case for valid SymPy usage
                return args[0]  
            return f"(* {' '.join(args)})"
        elif isinstance(expr, sp.Pow):
            base = self.sympy_to_smtlib(expr.base)
            if isinstance(expr.exp, sp.Integer) and expr.exp >= 0:
                exponent = int(expr.exp)
                if exponent == 0:
                    return "1"
                elif exponent == 1:
                    return base
                else:
                    # Convert x^n to repeated multiplication if n > 1
                    result = base
                    for _ in range(exponent - 1):
                        result = f"(* {base} {result})"
                    return result
            else:
                raise ValueError(f"Unsupported exponentiation: {expr}")
        elif isinstance(expr, Eq):
            left = self.sympy_to_smtlib(expr.lhs)
            right = self.sympy_to_smtlib(expr.rhs)
            return f"(= {left} {right})"
        elif isinstance(expr, Gt):
            left = self.sympy_to_smtlib(expr.lhs)
            right = self.sympy_to_smtlib(expr.rhs)
            return f"(> {left} {right})"
        elif isinstance(expr, Lt):
            left = self.sympy_to_smtlib(expr.lhs)
            right = self.sympy_to_smtlib(expr.rhs)
            return f"(< {left} {right})"
        elif isinstance(expr, Ge):
            left = self.sympy_to_smtlib(expr.lhs)
            right = self.sympy_to_smtlib(expr.rhs)
            return f"(>= {left} {right})"
        elif isinstance(expr, Le):
            left = self.sympy_to_smtlib(expr.lhs)
            right = self.sympy_to_smtlib(expr.rhs)
            return f"(<= {left} {right})"
        elif isinstance(expr, Ne):
            left = self.sympy_to_smtlib(expr.lhs)
            right = self.sympy_to_smtlib(expr.rhs)
            return f"(not (= {left} {right}))"
        elif isinstance(expr, And):
            args = [self.sympy_to_smtlib(arg) for arg in expr.args]
            return f"(and {' '.join(args)})"
        elif isinstance(expr, Or):
            args = [self.sympy_to_smtlib(arg) for arg in expr.args]
            return f"(or {' '.join(args)})"
        elif isinstance(expr, Not):
            arg = self.sympy_to_smtlib(expr.args[0])
            return f"(not {arg})"
        elif hasattr(expr, 'func') and expr.func == sp.Mod:
            left = self.sympy_to_smtlib(expr.args[0])
            right = self.sympy_to_smtlib(expr.args[1])
            return f"(mod {left} {right})"
        else:
            raise ValueError(f"Unsupported SymPy expression type: {type(expr)} - {expr}")
    
    def add_constraint_from_string(self, equation_str: str) -> None:
        """
        Add a SymPy expression from a mathematical equation (string) using SymPy parsing
        
        Args:
            equation_str: Mathematical equation as string (e.g. "x + y == 5", "x**2 + y**2 <= 25")
        """
        try:
            # Parse the equation string with SymPy
            # Replace == with Eq for SymPy
            processed_str = equation_str.replace('==', '= temp_eq_marker =')
            
            # Handle different comparison operators
            if '= temp_eq_marker =' in processed_str:
                left, right = processed_str.split('= temp_eq_marker =')
                expr = Eq(sympify(left.strip()), sympify(right.strip()))
            elif '>=' in equation_str:
                left, right = equation_str.split('>=')
                expr = Ge(sympify(left.strip()), sympify(right.strip()))
            elif '<=' in equation_str:
                left, right = equation_str.split('<=')
                expr = Le(sympify(left.strip()), sympify(right.strip()))
            elif '!=' in equation_str:
                left, right = equation_str.split('!=')
                expr = Ne(sympify(left.strip()), sympify(right.strip()))
            elif '>' in equation_str:
                left, right = equation_str.split('>')
                expr = Gt(sympify(left.strip()), sympify(right.strip()))
            elif '<' in equation_str:
                left, right = equation_str.split('<')
                expr = Lt(sympify(left.strip()), sympify(right.strip()))
            else:
                # Try to parse as a general expression
                expr = sympify(equation_str)
            
            self.add_sympy_expression(expr, equation_str)
            
        except Exception as e:
            raise ValueError(f"Failed to parse equation '{equation_str}': {e}")
    
    def add_sympy_expression(self, expr: sp.Basic, original_str: str = None) -> None:
        """
        Add a SymPy expression directly
        
        Args:
            expr: SymPy expression
            original_str: Original string representation
        """
        # Update class variables
        vars_in_expr = self.extract_variables_sympy(expr)
        self.variables.update(vars_in_expr)
        self.sympy_expressions.append(expr)
        self.original_equations.append(original_str or str(expr))

        # Check if nonlinear
        if self.is_nonlinear_sympy(expr) and self.logic == SMTLogic.QF_LIA:
            print(f"Warning: Expression contains nonlinear terms. Consider using QF_NIA logic.")
    
    def add_constraint(self, constraint: Union[str, sp.Basic]) -> None:
        """Add a constraint from string or SymPy expression"""
        if isinstance(constraint, str):
            self.add_constraint_from_string(constraint)
        else:
            self.add_sympy_expression(constraint)
    
    def generate_smt_lib(self) -> str:
        """Generate the complete SMT-LIB format string"""
        smt_content = []
        
        # Set logic
        smt_content.append(f"(set-logic {self.logic.value})")
        smt_content.append("")
        
        # Declare variables
        for var in sorted(self.variables):
            smt_content.append(f"(declare-fun {var} () Int)")
        smt_content.append("")
        
        # Add assertions
        for expr in self.sympy_expressions:
            try:
                smt_assertion = self.sympy_to_smtlib(expr)
                smt_content.append(f"(assert {smt_assertion})")
            except ValueError as e:
                print(f"Warning: Could not convert expression {expr}: {e}")
        
        smt_content.append("")
        
        # Add check-sat and get-model commands
        smt_content.append("(check-sat)")
        smt_content.append("(get-model)")
        smt_content.append("(exit)")
        
        return "\n".join(smt_content)
    
    def save_to_file(self, filename: str) -> None:
        """Save SMT-LIB content to an SMT2 file"""
        if not filename.endswith('.smt2'):
            filename += '.smt2'
        
        smt_content = self.generate_smt_lib()
        
        with open(filename, 'w') as f:
            f.write(smt_content)
        
        print(f"SMT-LIB file saved as: {filename}")
    
    def clear(self) -> None:
        """Clear all equations and variables"""
        self.variables.clear()
        self.sympy_expressions.clear()
        self.original_equations.clear()
    
    def set_logic(self, logic: SMTLogic) -> None:
        """Change the SMT logic"""
        self.logic = logic
    
    def get_info(self) -> Dict:
        """Get information about the current state"""
        return {
            'logic': self.logic.value,
            'variables': list(self.variables),
            'num_equations': len(self.sympy_expressions),
            'equations': self.original_equations,
            'sympy_expressions': [str(expr) for expr in self.sympy_expressions]
        }
    
    def simplify_expressions(self) -> None:
        """Simplify all stored SymPy expressions"""
        self.sympy_expressions = [sp.simplify(expr) for expr in self.sympy_expressions]
    
    def expand_expressions(self) -> None:
        """Expand all stored SymPy expressions"""
        self.sympy_expressions = [sp.expand(expr) for expr in self.sympy_expressions]

# Example usage with SymPy
if __name__ == "__main__":
    print("=== SMT-LIB Converter with SymPy Examples ===\n")
    
    # Example 1: Using string equations with SymPy parsing
    print("=== Example 1: String-based equations ===")
    converter = SMTEquationConverter(SMTLogic.QF_LIA)
    
    # Add equations using string parsing
    converter.add_constraint_from_string("x + 2*y == 10")
    converter.add_constraint_from_string("3*x - y >= 5")
    converter.add_constraint_from_string("x > 0")
    converter.add_constraint_from_string("y >= 0")
    
    print("Generated SMT-LIB:")
    print(converter.generate_smt_lib())
    converter.save_to_file("sympy_linear_example")
    
    print("\n" + "="*60 + "\n")
    
    # Example 2: Using SymPy expressions directly
    print("=== Example 2: Direct SymPy expressions ===")
    converter2 = SMTEquationConverter(SMTLogic.QF_NIA)
    
    # Create SymPy symbols
    x, y, z = symbols('x y z')
    
    # Add equations using SymPy expressions
    converter2.add_sympy_expression(Eq(x**2 + y**2, 25), "x^2 + y^2 = 25")
    converter2.add_sympy_expression(Le(x * y, 12), "x * y <= 12")
    converter2.add_sympy_expression(Eq(x + y + z, 10), "x + y + z = 10")
    converter2.add_sympy_expression(Ge(x, 1), "x >= 1")
    converter2.add_sympy_expression(Ge(y, 1), "y >= 1")
    converter2.add_sympy_expression(Ge(z, 0), "z >= 0")
    
    print("Generated SMT-LIB:")
    print(converter2.generate_smt_lib())
    converter2.save_to_file("sympy_nonlinear_example")
    
    print("\n" + "="*60 + "\n")
    
    # Example 3: Complex expressions with simplification
    print("=== Example 3: Complex expressions with SymPy operations ===")
    converter3 = SMTEquationConverter(SMTLogic.QF_NIA)
    
    # Create complex expressions
    a, b, c = symbols('a b c')
    
    # Add a quadratic equation: ax^2 + bx + c = 0 where a=1, b=5, c=6
    converter3.add_sympy_expression(Eq(x**2 + 5*x + 6, 0), "x^2 + 5x + 6 = 0")
    
    # Add constraints
    converter3.add_constraint_from_string("x >= -10")
    converter3.add_constraint_from_string("x <= 10")
    
    # Before simplification
    print("Before simplification:")
    print("Expressions:", [str(expr) for expr in converter3.sympy_expressions])
    
    # Simplify expressions
    converter3.simplify_expressions()
    
    print("\nAfter simplification:")
    print("Expressions:", [str(expr) for expr in converter3.sympy_expressions])
    
    print("\nGenerated SMT-LIB:")
    print(converter3.generate_smt_lib())
    converter3.save_to_file("sympy_complex_example")
    
    print(f"\nConverter info: {converter3.get_info()}")
    
    print("\n" + "="*60 + "\n")
    
    # Example 4: Boolean logic combinations
    print("=== Example 4: Boolean logic with SymPy ===")
    converter4 = SMTEquationConverter(SMTLogic.QF_LIA)
    
    p, q, r = symbols('p q r')
    
    # Complex boolean constraint: (p > 0 AND q > 0) OR (r < 0)
    complex_constraint = Or(And(p > 0, q > 0), r < 0)
    converter4.add_sympy_expression(complex_constraint, "(p > 0 AND q > 0) OR (r < 0)")
    
    # Additional constraints
    converter4.add_sympy_expression(Eq(p + q + r, 0), "p + q + r = 0")
    
    print("Generated SMT-LIB:")
    print(converter4.generate_smt_lib())
    converter4.save_to_file("sympy_boolean_example")
    