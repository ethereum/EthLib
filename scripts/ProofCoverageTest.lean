module

public import ProofCoverageTest.Rules
public import ProofCoverageTest.Proofs.Rules

/-!
# Fixtures for the proof coverage report

Each rule says, in its doc comment, the forks of its window.

Each theorem says the pairs that it touches.

`scripts/test_proof_coverage.sh` writes the claims and compares the grades.
-/
