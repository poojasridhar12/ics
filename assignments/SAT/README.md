# CDCL SAT Solver Implementation

## The SAT Problem Challenge

This project implements a Conflict-Driven Clause Learning (CDCL) SAT solver, an algorithm. The solver determines whether Boolean formulas in Conjunctive Normal Form (CNF) are satisfiable, returning either a satisfying assignment or proof of unsatisfiability.

## Implementation Requirements
1. DIMACS CNF format support
2. Outputs SAT with satisfying assignment, else outputs UNSAT

### Core Algorithm Components

1. **Unit Propagation**: When a clause has all but one literal falsified, the remaining literal must be true. This is done by the unit_propagation function iteratively scans all clauses, identifies unit clauses, and assigns the forced literal. Assignments are tagged with the current decision level and the clause that forced them (the antecedent).
2. **Conflict Analysis**: This is executed through the conflict_analysis function that resolves clauses along the implication graph, beginning from the conflict clause, repeatedly resolving on variables at the current decision level until only one remains (the First UIP).
3. **Backtracking**: After learning a clause, backtrack to the second-highest decision level in the learned clause. This is executed through the backtrack function which removes all assignments with decision level greater than the computed backtrack level, resetting the solver to a safer state.
4. **Variable Selection**: This chooses an unassigned variable for the next decision. This is done through the pick_branching_variable function selects the first unassigned variable from the sorted variable list. 
5. **Value Selection**: This choses a truth value for the selected variable. This is executed via the pick_branching_variable function which always pairs the selected variable with true at first.

## Implementation
- **`src/sat_solver.ml`**: Core CDCL algorithm
- **`src/parser.ml`**: DIMACS format parsing and solution writing
- **`main.ml`**: Main entry point and program flow

## DIMACS CNF Format

The DIMACS CNF format is the standard format for representing Boolean formulas in Conjunctive Normal Form.

### Format Specification

- **Comments**: Lines starting with 'c' are comments
- **Problem line**: `p cnf <num_variables> <num_clauses>`
- **Clauses**: Each clause is a space-separated list of integers ending with 0
  - Positive integers represent positive literals (e.g., 1 = x₁)
  - Negative integers represent negative literals (e.g., -1 = ¬x₁)
  - 0 marks the end of each clause


## Project Structure

```
SAT/
├── src/
│   ├── parser.ml      # DIMACS parsing and solution writing
│   ├── sat_solver.ml  # Core CDCL algorithm implementation
│   └── main.ml        # Main entry point
├── tests/
│   ├── input/         # Test input files (test_1.cnf to test_6.cnf)
│   └── output/        # Expected output files
└── README.md
```

This code has worked with all the test cases provided, and has returned the expected output. 
