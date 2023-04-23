# CS 5232 Final Project - Formal Specification and Verification of Sparse Matrix in Dafny

Adi Suryanata Herwana (A0144889J)

Wei Letong (A0248544X)


# Instructions

The main project directory contains all implementations and proofs mentioned as part of the report, 
separated into the following files for greater clarity:

- `csr.dfy`          - CSR Matrix class definition and common lemmas
- `GetSubmatrix.dfy` - implementation and verification of get_csr_submatrix()
- `GetIntXInt.dfy`   - implementation and verification of _get_intXint()
- `matrix.dfy`       - Dense Matrix predicate definition
- `SetIntXInt.dfy`   - 
- `SetMany.dfy`      - 

- `main.dfy`         - main class containing sample test cases for above library function verifications

The main class is runnable using Visual Studio Code.

Each file should be expected to verify in a timely manner (it verified within the default 20s timeout period on our machines)
