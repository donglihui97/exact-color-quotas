# Exact Color Quotas on Paths and Cycles: experiment code

This repository contains the code and raw results for the experiments in Section 6 of

> Lihui Dong and Zhuo Li. *Exact Color Quotas on Paths and Cycles.* Submitted to *Constraints*.

The paper studies proper coloring of a path in which some vertices are precolored and each color must occur a prescribed number of times. The code compares two ways of filtering the domains of the free vertices:

- **Joint filtering** is domain consistency for the conjunction of the adjacency rule (adjacent vertices get different colors) and the exact quotas. It is computed with the constant-time support tests of Algorithm 1 (Theorem 7 of the paper).
- **Separate filtering** is the fixed point of domain consistency for the two constraints taken one at a time. It alternates arc consistency on the chain of disequalities, which equals domain consistency for `regular` on a path, with Régin's matching-based domain consistency for `gcc`.

## Requirements

Python 3.8 or later. The code uses only the standard library. The results in the paper were produced with Python 3.14.4 on an Intel Core i9-12900HX with 64 GB of memory.

## Usage

```
python quotas.py validate   # correctness check on 4000 small random instances
python quotas.py root       # filtering at the root          -> Table 2 of the paper
python quotas.py search     # depth-first search             -> Table 3 of the paper
python quotas.py timing     # time of one filtering pass     -> Table 4 of the paper
python quotas.py all        # all four, in this order
```

The option `--seed S` sets the random seed. The default is 2026, which gives the instances used in the paper. Every experiment reseeds the generator, so `all` prints the same numbers as the four separate runs. Node counts, percentages, and instance counts are deterministic. Running times depend on the machine.

On the machine above, `validate` takes about 1 second, `root` about 5 seconds, `timing` about 15 seconds, and `search` about 90 seconds. Rerunning `root` and `search` with the default seed reproduces `results/root.txt` and `results/search.txt` exactly, apart from the time columns.

## What each experiment does

**validate.** Generates 4000 instances with at most 10 vertices and at most 4 colors. On each instance it checks that three methods give the same supports: the fast algorithm (`supports_fast`), a naive algorithm that fixes every vertex-color pair and reruns the singleton and pair tests of Theorem 2 (`supports_naive`), and exhaustive enumeration (`supports_brute`). It also checks that separate filtering never removes a supported value. The expected output is `joint mismatches 0, unsound separate 0`.

**root.** For n in {20, 50, 200}, k in {3, 5, 8}, bias β in {0, 0.6}, and δ in {0, 2}, it generates 100 instances and filters them once at the root. The paper reports the rows with δ = 2.

**search.** For n in {20, 40, 60}, k in {3, 4}, and δ in {1, 2}, with β = 0.6, it solves 50 instances by depth-first search. Both solvers branch on the leftmost free vertex and try the smallest color first. Search with separate filtering stops after 20000 nodes. The script also asserts that the two solvers agree on satisfiability whenever separate search finishes.

**timing.** Measures one filtering pass at the root on feasible instances with n in {10^3, 10^4, 10^5} and k in {4, 16}.

## Random instances

`generate(n, k, p, skew, delta, rng)` builds an instance in four steps.

1. Draw a random proper coloring of a path with `n` vertices and `k` colors. With probability `skew` (β in the paper), a vertex takes color 0 whenever its predecessor has a different color. Otherwise it takes a uniformly random color different from its predecessor.
2. Precolor each vertex independently with probability `p`. All experiments use `p = 0.2`.
3. Set the quotas to the color counts on the free vertices.
4. Move `delta` quota units, one at a time, from a random color with positive quota to another random color.

With `delta = 0` the instance is always feasible. With `delta > 0` it may be infeasible.

## Output format

Each command prints a title line followed by comma-separated rows.

| Experiment | Columns |
|---|---|
| root | `n,k,p,skew,delta,feasible,sep_detect,sep_removed_pct,joint_removed_pct` |
| search | `n,k,delta,instances,unsat,sep_limit,sep_nodes_median,sep_nodes_max,joint_nodes_median,joint_failures,sep_s,joint_s` |
| timing | `n,k,regions,joint_tests,joint_s,separate_s` |

The column meanings are as follows.

- `sep_detect` is the number of infeasible instances on which separate filtering empties a domain, out of all infeasible instances in the row.
- The `*_removed_pct` columns give the mean percentage of free vertex-color pairs removed, over the feasible instances.
- Node counts include the root. A value of 20001 in `sep_nodes_max` means that the node limit was reached.
- Times are in seconds. In `search` they are totals over the instances of a row.

The folder `results/` holds the outputs that produced the tables in the paper.

## Code structure

All code is in `quotas.py`.

| Function | Role |
|---|---|
| `gaps_of`, `cut_stats`, `feasible` | gaps between precolored vertices, cut statistics, and the singleton and pair tests (Theorem 2) |
| `supports_fast` | joint filtering with constant-time support tests (Algorithm 1, Theorem 7) |
| `supports_naive`, `supports_brute` | reference implementations used by `validate` |
| `ac_neq`, `gcc_dc`, `separate_filter` | separate filtering: arc consistency on the disequalities and Régin's algorithm for `gcc` |
| `search_separate`, `search_joint` | depth-first search with each kind of filtering |
| `generate` | random instances |
| `exp_validate`, `exp_root`, `exp_search`, `exp_timing` | the four experiments |

The implementation handles paths. The theory in the paper also covers cycles and disjoint unions of paths and cycles.

## Citation

If you use this code, please cite the paper above. The bibliographic details will be added after publication.
