# CS 5232 Final Project - Formal Specification and Verification of Sparse Matrix in Dafny

Adi Suryanata Herwana (A0144889J)

Wei Letong (A0248544X)


# Instructions

The main project directory contains all implementations and proofs mentioned as part of the report, 
separated into the following files to enhance performance and readability:

- `csr.dfy`          - CSR Matrix class definition and common lemmas
- `GetIntXInt.dfy`   - implementation and verification of _get_intXint()
- `GetSubmatrix.dfy` - implementation and verification of get_csr_submatrix()
- `matrix.dfy`       - Dense Matrix predicate definition
- `AddDense.dfy`     - implementation and verification of _add_dense()
- `CsrToDense.dfy`   - implementation and verification of csr_todense()
- `SetIntXInt.dfy`   - implementation and verification of _set_intXint()
- `SetMany.dfy`      - implementation and verification of _set_many()
- `SampleOffsets.dfy`- implementation and verification of csr_sample_offsets()
- `InsertMany.dfy`   - (incomplete) implementation and verification of _insert_many()

- `main.dfy`         - main class containing sample test cases for above library function verifications

The main class is runnable using Visual Studio Code.

Each file should be expected to verify in a timely manner (it verified within the default 20s timeout period on our machines)
