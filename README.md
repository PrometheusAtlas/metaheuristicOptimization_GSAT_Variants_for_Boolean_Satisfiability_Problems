# Project: Metaheuristic Optimization — GSAT Variants for Boolean Satisfiability Problems

Implements a comprehensive stochastic local search framework for solving Boolean Satisfiability (SAT) problems.  
The system encodes, evaluates, and compares multiple GSAT-derived algorithms—**GSAT, GWSAT, HSAT, HWSAT, GSAT-Tabu**, and a novel hybrid **GrimesSAT**—across benchmark SAT instances.  
This project serves as a full experimental suite for metaheuristic optimization and stochastic reasoning under combinatorial search constraints.

## Description
The framework parses CNF-formatted problem files, performs randomized local search to minimize unsatisfied clauses, and tracks convergence statistics across algorithmic variants.  
Each solver implements a unified architecture with modular heuristic definitions, parameter tuning, and runtime instrumentation.

## Technical Highlights
- **Algorithms implemented:** GSAT, GWSAT, HSAT, HWSAT, GSAT-Tabu, GrimesSAT (hybrid).  
- **SAT parsing:** Reads DIMACS `.cnf` files; builds literal-to-clause mappings for fast evaluation.  
- **Core design:** Tracks `makecounts`, `breakcounts`, unsatisfied clauses, and Tabu memory; supports adaptive walk probabilities and aspiration logic.  
- **Experiment automation:** Batch tests with `run_all_experiments()` over benchmark sets (e.g., `uf50-218`, `uf150-645`).  
- **Statistical reporting:** Computes mean, standard deviation, median, min, max, and IQR for runtime and performance.  
- **Visualization:** Generates boxplots and runtime distribution histograms using Matplotlib.  
- **Performance metrics:** Objective value, restarts, flips, runtime distributions.

## Tools and Libraries
Python 3 · NumPy · Pandas · Matplotlib · SciPy · random · time.perf_counter

## Summary
This project represents a rigorous research pipeline in stochastic optimization and metaheuristics—demonstrating algorithmic innovation (GrimesSAT) and empirical evaluation of stochastic local search for Boolean Satisfiability.
