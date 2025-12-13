# LeanJavaScripty - Abstract Interpretation with LLM-Guided Widening

A static analyzer for a simple imperative language implemented in Lean 4, featuring interval-based abstract interpretation with LLM-guided widening for improved precision.

## Project Structure

```
code/LeanJavaScripty/
├── LeanJavaScripty.lean          # Root module (imports all library modules)
├── Main.lean                      # Executable entry point for testing
├── lakefile.lean                  # Lake build configuration
├── lean-toolchain                 # Lean version specification (v4.25.2)
│
├── LeanJavaScripty/               # Core library modules
│   ├── Syntax.lean                # AST definitions (Expr, BoolExp, Stmt)
│   ├── Semantics.lean             # Concrete operational semantics (big-step)
│   ├── Interval.lean              # Interval abstract domain (bounds, operations)
│   ├── StaticAnalyzer.lean        # Abstract interpreter with widening
│   ├── Slicer.lean                # Program slicing for targeted analysis
│   ├── LLMGuide.lean              # LLM integration via Ollama API
│   └── ConcreteDomain.lean        # (Unused) Concrete domain definitions
│
└── Tests/                         # Test suites
    ├── StaticAnalyzerTests.lean   # Tests for abstract interpretation
    └── WideningTests.lean         # Tests for widening strategies
```

## Module Descriptions

| Module | Description |
|--------|-------------|
| **Syntax.lean** | Defines the abstract syntax tree: expressions (`Expr`), boolean expressions (`BoolExp`), and statements (`Stmt`) including assignments, sequencing, conditionals, and while loops. |
| **Semantics.lean** | Implements concrete big-step operational semantics for the language. |
| **Interval.lean** | Defines the interval abstract domain with `Bound` (±∞ or integer) and `Interval` types, along with abstract operations (add, sub, join, widen, etc.) and abstract values (`AbsVal`). |
| **StaticAnalyzer.lean** | Core abstract interpreter implementing `exec` for statement analysis, `evalAbs` for expression evaluation, and both pure widening and LLM-guided widening strategies. |
| **Slicer.lean** | Program slicing utilities to identify relevant variables and statements, enabling targeted analysis of specific program properties. |
| **LLMGuide.lean** | Integration with local LLM (Ollama/Llama3) to provide intelligent widening suggestions during fixed-point computation. |

## Prerequisites

- **Lean 4** (v4.25.2) - Install via [elan](https://github.com/leanprover/elan)
- **Ollama** (optional) - For LLM-guided widening features. Install from [ollama.ai](https://ollama.ai)

## Compilation

```bash
# Navigate to the project directory
cd code/LeanJavaScripty

# Build the library and executable
lake build

# Run tests
lake build Tests

# Run the main executable (if Ollama is running)
lake exe llmtest
```

### Clean Build

```bash
lake clean
lake build
```

## Usage

### Running with LLM-Guided Widening

1. Start Ollama with Llama3:
   ```bash
   ollama run llama3
   ```

2. Run the analyzer:
   ```bash
   lake exe llmtest
   ```

### Example Program Analysis

The analyzer can process programs like:
```
x := 0;
while (x < 100) {
    x := x + 1
}
```

And produce interval bounds for variables at each program point.

## Known Bugs & Limitations

- **LLM Consistency**: In certain scenarios, the LLM may provide inconsistent or suboptimal widening suggestions, leading to less precise analysis results.

- **Variable Naming**: The current slicing implementation assumes that all variables are uniquely named, which may not hold in all programs. An easy fix is to implement variable renaming (alpha-conversion) to ensure uniqueness.

- **Integer-Only Support**: Current implementation only supports integers. A significant extension would be heap abstractions and summarization of object properties, which would enable analysis of more complex JavaScript-like programs and reduce false positives.

## References

- Cousot, P., & Cousot, R. (1977). *Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints.*
- The Lean 4 Theorem Prover: [leanprover.github.io](https://leanprover.github.io/) 