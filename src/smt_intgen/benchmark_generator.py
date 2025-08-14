from __future__ import annotations
from pathlib import Path
from typing import List, Optional
from smt_intgen.eq_creator import Eq_Creator
from smt_intgen.eq_converter import Eq_Converter

class Benchmark_Generator:
    """
    Orchestrates generation (Eq_Creator) -> SMT-LIB export (Eq_Converter).

    Parameters
    ----------
    creator : Eq_Creator
        Configured generator instance.
    output_dir : str
        Directory to write .smt2 files into (created if missing).
    base_name : str
        Prefix for output filenames.
    overwrite : bool
        If False and the target file exists, a numeric suffix will be added.
    """

    def __init__(
        self,
        creator: Eq_Creator,
        output_dir: str = "out",
        base_name: str = "constraints",
        overwrite: bool = True,
    ):
        self.creator = creator
        self.output_dir = Path(output_dir)
        self.base_name = base_name
        self.overwrite = overwrite
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def _build_filename(self, set_index: int) -> Path:
        """
        Build a descriptive filename that encodes the key params + seed.
        """
        name = (
            f"{self.base_name}"
            f"_logic-{self.creator.logic.lower()}"
            f"_vars-{self.creator.total_vars}"
            f"_deg-{self.creator.max_deg}"
            f"_co-{self.creator.max_co}"
            f"_seed-{self.creator.seed_used}"
            f"_set-{set_index}.smt2"
        )
        return self.output_dir / name

    def _resolve_collision(self, path: Path) -> Path:
        """
        If overwrite=False and path exists, add a numeric suffix.
        """
        if self.overwrite or not path.exists():
            return path
        i = 1
        while True:
            candidate = path.with_name(f"{path.stem}_{i}{path.suffix}")
            if not candidate.exists():
                return candidate
            i += 1

    def run_all(self) -> List[str]:
        """
        Generate creator.total_tests constraint sets and write each to a .smt2 file.
        Returns the list of written file paths.
        """
        written: List[str] = []
        # Generate each set on-demand so the seed advances predictably
        for idx in range(1, self.creator.total_tests + 1):
            constraints = self.creator.generate_constraint_set()
            out_path = self._resolve_collision(self._build_filename(idx))

            conv = Eq_Converter()
            conv.execute(constraints, str(out_path))
            written.append(str(out_path))
        return written

    def run_once(self, out_file: Optional[str] = None) -> str:
        """
        Generate a single constraint set and write it to a .smt2 file.
        If out_file is None, an auto name is used.
        Returns the written file path.
        """
        constraints = self.creator.generate_constraint_set()
        path = (
            self._resolve_collision(self._build_filename(1))
            if out_file is None
            else Path(out_file)
        )
        path.parent.mkdir(parents=True, exist_ok=True)
        conv = Eq_Converter()
        conv.execute(constraints, str(path))
        return str(path)


if __name__ == "__main__":
    creator = Eq_Creator(
        total_vars=5,
        max_deg=3,
        max_eq=4,
        max_co=7,
        total_tests=2,
        logic="QF_NIA",
        complex_bias=True,
        seed=None,
    )

    generator = Benchmark_Generator(creator, output_dir="out", base_name="sample", overwrite=True)
    paths = generator.run_all()
    print("Wrote:")
    for p in paths:
        print("  ", p)
