# The Factorial Oracle of Robin Miller (saphir) and the centered Fourier comb

The original two points in the GeoGebra file are exactly the first and second teeth of the two-tooth comb when the comb uses the file’s shell and common amplitude. Their sum is the endpoint of its ordered walk. The proof allows any real spin parameter $s$. The saved GeoGebra slider advances $s$ in steps of one.

## Source and conventions

The source is [Factorial Oracle.ggb](Factorial%20Oracle.ggb), SHA-256 `e293de7d0c6a532f4162e29c413a2f13f1b2285d7ae19d2136f27fef4831ac92`. Its `geogebra.xml` defines

$$
N=n_1!-(\phi_3-\phi_1),\quad a_1=(n_6 N)^\alpha,\qquad
k_1=Nt_1-t_2,\quad k_2=Nt_1+t_2,\qquad z_j=a_1 e^{\pi i k_j s/N}.
$$

Here $N$ is the file’s $n_3$. The Fourier formulas require $N\ne0$. The amplitude definition uses integer powers, covering all three stops of the file’s $\alpha$ slider, including negative bases. At $\alpha=-1$ the source interpretation requires $n_6N\ne0$. For an amplitude supplied independently, the pair and comb identities hold for every real value, including zero. The saved settings give $N=a_1=24$, $k_1=23$, $k_2=25$, and $s=2$.

The later Fourier viewer fixes $\phi_1=1$ and uses $\rho=n_6 N^\alpha$. The two radius formulas can differ. For example, at $n_6=-1$ and $\alpha=0$ the file gives $+1$ and the viewer gives $-1$. The common-amplitude parameter in the proof lets each instrument use its own convention. The extension follows the centered offsets of the October 2026 viewer. Odd combs use consecutive integers centered at zero. Even combs use consecutive odd integers centered at zero.

## Theorems

Write $u=e^{\pi i t_1s}$ and $x=t_2s/N$. The following declarations are in [FourierHelix.lean](FourierHelix.lean).

| Declaration | Result |
|---|---|
| `Oracle.pair_is_first_comb`, `Oracle.sum_is_walk` | Each original point agrees with its corresponding tooth. GeoGebra’s $z_0=z_1+z_2$ is the second walk vertex. |
| `Oracle.factorial_pair` | The original factorial construction gives $z_0=2a_1u\cos(\pi x)$. |
| `Oracle.difference`, `Oracle.tip_distance` | The file’s $C=z_1-z_2$ equals $-2i a_1u\sin(\pi x)$. Its measured tip distance is $2\lvert a_1\rvert\lvert\sin(\pi x)\rvert$. |
| `Oracle.saved_labels` | Exact evaluation of the saved shell, amplitude, and both labels. |
| `full_comb` | For every tooth count $m$, the full walk is $\rho u\sum_c\cos(\pi c x)$ over the actual offsets. Pairing $c$ with $-c$ cancels the imaginary part of the spread factor. |
| `walk_geometric` | Every ordered prefix of length $j$ is the first tooth times $\sum_{r=0}^{j-1}q^r$, where $q=e^{\pi i d x}$ and $d$ is the offset spacing. |
| `alignment_readout`, `aligned_walk` | The common ratio is one at $x\in2\mathbb Z$ for odd $m$ and $x\in\mathbb Z$ for even $m$. Each aligned prefix is $j$ copies of its first tooth. |
| `closes_iff` | For $\rho\ne0$ and $q\ne1$, the prefix closes exactly when $q^j=1$. Taking $j=m$ gives full-comb cancellation. |
| `chart_on_sphere` | The viewer’s scale-A chart maps each complex point, including every walk vertex, to the unit sphere. This is a property of the later 3D display. |

These statements concern exact mathematical values. Verification of GeoGebra’s evaluator, the browser’s floating-point output, and the optional unequal-amplitude tilt lie outside the proof.

## Walking the divisor lattice in both directions

[FactorPath.lean](FactorPath.lean) starts at a positive integer `N`. At each
shell above 1 it runs the factorial-stride scan until the tooth's orbit first
shortens. The stride index gives the least prime factor `p`, and the new orbit
has order `N / p`. The pen records `p` and repeats the scan on that lower shell.
This uses the first drop at every shell. The separate `factor?` shortcut can
return a composite factor and skip intermediate divisors.

For `720`, the downward labels are `[2, 2, 2, 2, 3, 3, 5]`. Starting at 1
and multiplying by those labels in reverse gives
`1 → 5 → 15 → 45 → 90 → 180 → 360 → 720`.

`FactorSearch.Path.replay_every_shell` proves that the upward walk retraces
every vertex of this canonical descent for every positive starting shell.
At 1 the path has one vertex and no edges. The example
`FactorSearch.Path.round_trip_720` checks both vertex lists.
The [verification log](FACTOR_PATH_VERIFICATION.log) records the compiler,
axiom checks, kernel replay, and four executable walks.

## Provenance

This construction comes from the GeoGebra file "Factorial Oracle" (2024) by Robin Miller (saphir, GitHub `hypatiaa`). Its gearbox $k_1=N-1$, $k_2=N+1$ on the factorial shell $N=n!$ is the two-tooth comb proved here. Its lineage is: hand-drawn residue-ray diagrams (2018–19) → GeoGebra residue rays under the handle hypatiaa (2019) → the Factorial Oracle (2024) → the formal helix family of the FVLT kernel (v2.6.1, §9.1a, Lemma 9.3a) → the centred Fourier comb viewer (October 2026) → these Lean proofs (25 November 2026).

Public GeoGebra records (dates as GeoGebra's server reports them, UTC):

- [factorialpacman](https://www.geogebra.org/m/nseeyegv), created 24 July 2024. It already contains the gearbox $k_1=n_2!\,t_1-t_2$, $k_2=n_2!\,t_1+t_2$ with $z_j=n_1!\,e^{2\pi i k_j/n_3}$, the early form of the Factorial Oracle. GeoGebra also records a modification on 25 November 2026; the creation date says when the material was made, not that every detail is unchanged since then.
- [Wilson's Theorem](https://www.geogebra.org/m/zanuhgw7), created 11 August 2026, published 25 November 2026.

## Reproduction

The [Wilson trace and polygon gate](WILSON.md) document the companion construction from `WilsonFactorial Oracle.ggb`, its integer Steps protocol, and the two Wilson readouts of the older merged viewer.

The [reverse factor search](FactorSearch.lean) takes a direct integer shell $N\ge2$. At spin $s=2$, it probes the positive tooth with Steps $t=k!\bmod N$. Its exact phase order is $N/\gcd(N,k!)$. The first order drop occurs at the least prime factor of $N$. The executable `FactorSearch.factor?` first probes $k=\lfloor\sqrt N\rfloor$. Full order certifies primality, an intermediate order yields a proper divisor, and order one triggers a scan for the first drop. For $N=221$, Steps $195$ at $k=14$ gives order $17$ and factor $13$. Build this module with `lake build FactorSearch`.

On 25 November 2026 the local Lean 4.35.0 compiler checked all 25 theorems and exited successfully. All 13 printed axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The [verification log](VERIFICATION.log) records the source hash, toolchain, mathlib commit, exit status, and axiom output.

Use Lean 4.35.0 with the mathlib commit in [lakefile.toml](lakefile.toml). In a fresh checkout run `lake update`, `lake exe cache get`, and `lake build`. The module prints the axioms of its main results.
