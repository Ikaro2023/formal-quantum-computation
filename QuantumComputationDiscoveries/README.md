# Discovered Quantum Algorithms

This folder contains the implementations, correctness proofs, and resource consumption measures
of the algorithm discovered in [Discovering formally verified quantum programs with AI](https://arxiv.org/abs/2611.09822).

The proofs can be checked (slowly) with

```bash
lake comparator --config QuantumComputationSpecs/ChallengeJsons/Algorithms/GroverFindAllRelCost.json
lake comparator --config QuantumComputationSpecs/ChallengeJsons/Algorithms/GroverFindAnyRelCost.json
lake comparator --config QuantumComputationSpecs/ChallengeJsons/Algorithms/P450GroundEnergy.json
lake comparator --config QuantumComputationSpecs/ChallengeJsons/Algorithms/Photochemistry.json
lake comparator --config QuantumComputationSpecs/ChallengeJsons/Algorithms/StoppingPower.json
lake comparator --config QuantumComputationSpecs/ChallengeJsons/Primitives/ArcsinK25ConstCost.json
```

## Statistics

The table below shows, for each discovered solution in this folder, the time to build it with `lake build`, the time to check it against its specification with `lake comparator`, and the peak memory used by that comparator run.

| Solution | `.lean` modules | Lines | Build time | Comparator run | Comparator peak RAM |
|---|---:|---:|---|---|---|
| Grover FindAny | 4 | 2,709 | 2 min | 3 min | small |
| ArcSin | 16 | 22,335 | 16 min | 4 min | small |
| P450 | 160 | 199,831 | 21 min | 35 min | 230 GB + swap |
| Photochemistry | 74 | 196,621 | 2 h 04 min | 59 min | 233 GB + swap |
| StoppingPower | 176 | 457,154 | 1 h 41 min | 2 h 27 min | 232 GB + swap |
| Grover FindAll | 200 | 554,952 | 1 h 19 min | 1 h 04 min (sharded) | 28 GB per process, no swap |
