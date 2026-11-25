# The Wilson trace in Robin Miller’s Factorial Oracle

The Wilson construction starts with factorial input $n=n_1$ and candidate $p=n+1$. In the GeoGebra file, setting $\phi_1=1$ and $\phi_3=0$ puts the detuning $n_7$ at $-1$. The active shell then has size $M=n!+1$. The file computes $r=M\bmod p$ and $d_p=\min(r,p-r)$.

| GeoGebra object or operation | Lean declaration | Meaning |
|---|---|---|
| $d_p$ at the active detuning | `active_gate_iff_prime` | $d_p=0$ exactly when $p$ is prime, for every natural $n\ge1$. |
| `TextWilson` and the polyline guard | `readout`, `polygon_iff` | The integral-input drawing branch requires $n_7=-1$, $1\le n\le18$, and a passing gate. At $p=2$ the file reports an antipodal cycle and suppresses the polyline. |
| $t_c$ and `orbitvertices` | `step_times_candidate`, `vertex_eq` | At a passing gate $t_c=M/p$ is integral. Vertex $j$ is the signed amplitude $a_1$ times $\exp(2\pi i/p)^j$. |
| Original Steps control at $s=2$ | `trace_at_spin_two`, `trace_recovers_vertices` | An integer carrier $t_1$ contributes a whole number of turns. Setting Steps to $j t_c$ recovers vertex $j$ of the derived polygon. |
| Selecting a phase by integer Steps | `prime_iff_integer_steps` | There exists an integer Steps value that selects a phase of exact order $p$ if and only if $p$ is prime. |
| Distinct vertices and closure | `plotted_polygon`, `antipodal_vertices`, `zero_radius` | With nonzero amplitude, indices $0,\ldots,p-1$ give distinct tips and the tip returns to its start exactly at multiples of $p$. At zero amplitude every tip is zero. |

GeoGebra assigns the displayed `closureangle` and `closuregap` literal zeros when the guard passes. The Lean argument for closure uses the exponential in `orbitvertices` and the order of its root of unity. The radius condition matters because GeoGebra’s arithmetic gate does not inspect $a_1$.

## The older viewer with panels

The October 4 merged Monodromy viewer supplies two Wilson readouts. On its eligible factorial successor shell, the gearbox compares the spectral defect $p-1-\varphi(p)$ to the residency test $p\mid M$. The theorem `gearbox_zero_iff_resident` proves their zero tests agree. The independent candidate card accepts $p$ directly. Its arithmetic criterion $p\mid(p-1)!+1$ is `independent_candidate` for every $p\ge2$. These results specify the mathematics of the panels. The JavaScript primality routine, rendering, and the GeoGebra evaluator have separate implementation boundaries.

## Reproducible settings

| Input | Result |
|---|---|
| Saved file, $n=4$, $n_7=0$ | $p=5$, $n_3=24$, and $d_p=1$. The probe is inactive. |
| Same $n=4$, switched to $n_7=-1$ | $M=25$, $p=5$, $t_c=5$. The polygon branch is active. |
| $n=6$, $n_7=-1$ | $M=721=7\cdot103$. Steps $0,103,206,309,412,515,618$ give the seven vertices. Step $721$ returns to the start. |
| $n=3$, $n_7=-1$ | $M=7$, $p=4$, and $d_p=1$. The gate misses. |

The source inspected is [WilsonFactorial Oracle.ggb](WilsonFactorial%20Oracle.ggb), SHA-256 `c6f0d578e2391b7af48a2f5ba976825bd0cc1253b753a8b6696d9f6cf7a18203`. The merged HTML is `MCOMB_FCA_M7_COMBINED_BCD_RHM_AF_v0_1_20261004/monodromy-31-linked-reduction.html`, SHA-256 `b4cee4e30a753eda7c62f72e8043d6d5c9b3f69c3c2e1dd0da9a3f9ab5b8e248`. The October 18 FASTSTART launcher serves that source.

Lean 4.35.0 checked all 20 theorems. Of the 13 printed axiom reports, 12 list only `propext`, `Classical.choice`, and `Quot.sound`. The saved-state example uses no axioms. The [verification log](WILSON_VERIFICATION.log) records the source and compiled module hashes and the compiler output.

The proofs are in [WilsonOracle.lean](WilsonOracle.lean). With the pinned dependencies available, run `lake build WilsonOracle`.
