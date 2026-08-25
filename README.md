# Most Influential Multi-type Community Search (MIMCS)

This repository contains the experimental C++ implementation and runtime
configuration files for the MIMCS research project. It searches a
heterogeneous information network for a connected, budget-feasible multi-type
community satisfying typed degree constraints while maximizing RR-set
influence coverage.

The public solver exposes two query-conditioned exact algorithms:

- `baseline_enum`: MIMC-Enum.
- `advanced_full`: MIMC-B&B / Advanced-Full.

Author and citation information will be added later.

## Contents

```text
CMakeLists.txt          C++17 build configuration
src/mimc_lift.cpp      experimental implementation
experiments/configs/   95 runtime configurations used for five datasets
README.md               build, input, and execution instructions
```

No graph dataset, concrete query vertex, experimental output, plotting code,
or cluster script is included in this version.

## Build

Requirements: CMake 3.16 or newer and a C++17 compiler.

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel
```

The executable is `build/mimcs`. Show the complete public interface with:

```bash
./build/mimcs --help
```

## Input graph

The whitespace-delimited graph format is:

```text
n m ntypes
type_0 cost_0
...
type_(n-1) cost_(n-1)
u_0 v_0
...
u_(m-1) v_(m-1)
```

Vertex IDs are implicit, contiguous, and zero-based. Each of the following
`m` rows is an undirected edge. Self-loops are ignored and duplicate edges are
deduplicated. The experimental node-cost rule is `1 + log1p(degree)`.

## Configuration

Configuration files accept either `key value` or `key=value`; `#` begins a
comment. Important fields include repeatable typed constraints, the allowed
type set, target type, meta-paths, influence model, budget, RR-set counts, and
ball parameters. The files in `experiments/configs/` are the released runtime
configurations for DBLP, IMDb, TMDB, DBpedia, and PubMed.

Configuration names have the form:

```text
cfg_<dataset>_3T_S<setting>_G<gamma>.txt
```

They encode three-type settings and constraint levels `gamma=2,3,4,5,6`.
There are 15 DBLP, 15 IMDb, 25 TMDB, 25 DBpedia, and 15 PubMed configurations.

## Run

First validate a reconstructed graph and configuration:

```bash
./build/mimcs --mode config \
  --graph /path/to/dataset_graph.txt \
  --config experiments/configs/cfg_DBLP_3T_S1_G4.txt
```

Run MIMC-Enum:

```bash
./build/mimcs --mode query_exact \
  --algo baseline_enum \
  --graph /path/to/dataset_graph.txt \
  --config experiments/configs/cfg_DBLP_3T_S1_G4.txt \
  --query QUERY_VERTEX_ID --seed 1 --timelimit 3600
```

Run MIMC-B&B:

```bash
./build/mimcs --mode query_exact \
  --algo advanced_full \
  --graph /path/to/dataset_graph.txt \
  --config experiments/configs/cfg_DBLP_3T_S1_G4.txt \
  --query QUERY_VERTEX_ID --seed 1 --timelimit 3600
```

Use `--budget B` to override the budget stored in a configuration.

`query_exact=yes` means the query-conditioned search completed and proved the
reported optimum. If the time limit is reached first, the program reports the
best feasible incumbent found so far, a certified upper bound, and a gap; that
return is not a proved optimum.

The graph inputs and query vertices are intentionally not distributed in this
minimal code release. Users must supply normalized graphs whose zero-based
type and vertex numbering matches the selected configuration.
