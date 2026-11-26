---
title: The small-field Wilson estimates for one blocking step
subtitle: Worked W2 exercise and mathematical proof register
---

## Scope and main result

For the exact two-link spatial block, the first visible free transverse pole has unit limiting speed in inherited time. Its equal-time covariance already has a linear relative correction at small axial momentum. The bare mixed Schur correction divided by retained energy tends to $3/4$, even though the signed gap margin is positive. These facts distinguish the free estimates that can enter a paper from the proposed interacting comparisons.

The six units contain 44 numbered targets. The pinned project includes 74 public kernel-checked theorems and 17 private proof lemmas. Every entry below gives its statement from the integrated prompt and a derivation, counterexample or specific missing estimate. Individual Lean names identify the exact scope of the formal evidence.

| Unit | Research question | Targets |
|---|---|---|
| W2a-R | The physical clock and Wilson calibration | 10 |
| W2b | The exact Gaussian block | 11 |
| W2c | Gauge reduction and the eliminated gap | 6 |
| W2d | Transport and the retained form | 7 |
| W2e | Conditional scores and the Schur form | 5 |
| W2f | Small-field assembly and transfer | 5 |

**Conventions.** $x=g^2$ is the squared coupling, $a$ the fine spacing, and $2a$ the coarse spacing. The reference gap $m$ is positive. A “free proof” uses the specified Gaussian model. A “conditional proof” lists extra physical or trajectory premises. A typed conjecture gives a proposition whose proof is outstanding. Local records use Lean 4.36.0 and Mathlib v4.36.0.

**Publication fields.** GitHub repository [GITHUB-URL] · archival DOI for this exercise [DOI-PENDING]. The source clock paper has its own published identifier, given in the references.

# W2a-R • The physical clock and Wilson calibration

## Proposition W2a-R.1 • Full and truncated calibrations

**Status.** Conditional proof.

**Statement.** Let M_c bound the remainder of 1/c_ref: |1/c_ref(g) − 1 + c₁g²| ≤ M_c g⁴ on (0, g∗]. Under the hypotheses of W2a Theorem 8:

(A) Scheme A: M_match = 0 and C_ξ^A = [|c₁|A₊Q + M_c(1 + Q²)]/d₀.

(B) Scheme B: M=0 for the linear calibration. Under Bx*≤A/2, A₊x*≤1/2 and |c₁|x*≤1/2, Cξᴮ=6A|c₁| and Mmatchᴮ≤M_c(1+Q²)/d₀. In both schemes d₀=1−|c₁|x*−M_c x*²>0 is a floor for the full inverse clock.

In both schemes the actual block error per step is at most [C_ξ + M_match + C_ξM_match x∗²]gₖ⁴.

**Derivation.** Write $x=g^2$, $y=g_{k+1}^2$, $A_+=A+Bx_*$ and $Q=(1-A_+x_*)^{-1}$. The running inequality gives $y\le Qx$ and $0\le y-x\le A_+Qx^2$. If $u(x)=1+sx+e(x)$ with $|e(x)|\le Mx^2$, subtract its values at $x,y$ and divide by $u(x)\ge d=1-|s|x_*-Mx_*^2>0$. This gives $C_\xi=(|s|A_+Q+M(1+Q^2))/d$. The reciprocal calibration transports exactly in Scheme A, so $M_{\mathrm{match}}=0$. In Scheme B the linear calibration has no Taylor remainder and the smallness assumptions give $C_\xi\le 6A|c_1|$. Comparison to the full reciprocal costs at most $M_c(1+Q^2)/d$ with $s=-c_1,M=M_c$. Expanding the product of two factors adds the cross term $C_\xi M_{\mathrm{match}}x_*^2$ to the coefficient. These are inequalities conditional on the specified uniform inputs.

**Lean proofs.** `W2.W2aR.step_error_schemeA`, `W2.W2aR.step_error_schemeB`, `W2.W2aR.clock_step_bound`.

**Related definitions or hypotheses.** `W2.Common.ClockRegularityHyp`.

## Proposition W2a-R.2 • Physical time transport along a weak trajectory

**Status.** Conditional proof.

**Statement.** Under (i)–(iii) of W2a Theorem 15, with ξ ≡ 1 at every step the per-step clock factor is Fₖ = c_ref(gₖ)/c_ref(gₖ₊₁) = 1 − c₁A gₖ⁴ + O(gₖ⁶), and Π_{k=0}^{J−1} Fₖ = c_ref(g₀)/c_ref(g_J) → 1/c_ref(g_J) as the cutoff is removed at fixed g_J, uniformly over the family of W2a Theorem 8.

**Derivation.** Time covariance and speed preservation give $F_k=c(x_k)/c(x_{k+1})$. All intermediate factors cancel, including for the empty product. The reciprocal-running lower decrement makes $x_0\to0$ at fixed $x_J$, uniformly under the stated trajectory bounds. Since $c(0)=1$, the product tends to $1/c(x_J)$. With the stated local expansion and cubic remainder, subtract successive values to obtain the first correction $-c_1 A x_k^2$. The physical identity presupposes a common spectral branch and the named time-covariance hypothesis.

**Lean proofs.** `W2.W2aR.isotropic_telescopes`, `W2.W2aR.physical_clock_composes`, `W2.W2aR.clock_product_telescope`.

**Related definitions or hypotheses.** `W2.Common.DispersionHyp`, `W2.Common.ClockRegularityHyp`, `W2.Common.cubicClockExpansion`.

## Corollary W2a-R.3 • Criterion for a drifting clock multiplier

**Status.** Conditional proof.

**Statement.** A multiplier with a genuine nonzero term κg² gives the power-law drift on the specified trajectory. The physical clock telescopes under its hypotheses. A Wilson-truncated local reading is one possible source of a nonzero coefficient. Its optional group-specific shift is unresolved.

**Derivation.** For $x_j=(b+Aj)^{-1}$ and positive factors, the product of $1+\kappa x_j$ is a ratio of two rising products. Applying the gamma recurrence term by term and taking its asymptotic ratio gives a constant times $K^{\kappa/A}$. A nonzero $\kappa$ therefore changes the power. The physical clock in W2a-R.2 telescopes. At coefficient level regular time covariance would require $(1-\rho)s=\kappa$ with $\rho=1$. The optional local Wilson response is one possible distinct reading and its group-specific slope is undetermined.

**Lean proofs.** `W2.W2aR.drift_gamma_identity`, `W2.W2aR.drift_asymptotic`, `W2.W2aR.drift_iff_kappa_ne_zero`, `W2.W2aR.no_regular_clock`, `W2.W2aR.first_order_compat`.

**Related definitions or hypotheses.** `W2.Common.DispersionHyp`.

## Definition W2a-R.4 • A sector-resolved finite-volume clock

**Status.** Definition.

**Statement.** Use Definition 4.1 of [Clock]. In the centre-neutral Gauss-law sector track the same branch at p₁=(2π/L,0,0) and at rest. With Δ(p)=E₁(p)−E₀, define the positive speed from c_L²=[Δ(p₁)²−Δ(0)²]/|p₁|² whenever positive.

**Definition and verification.** Choose a common excitation branch at rest and at the first axial momentum, orthogonal to the vacuum when at rest. In the torus gauge theory use the Gauss-law sector with trivial characters for the three centre actions. With $\Delta(p)=E(p)-E_0$, take the positive square root of the difference of squared gaps divided by $|p_1|^2$ whenever this quotient is positive. Adding a scalar to every energy cancels inside each difference, as the Lean identity shows. Branch identification is a physical input.

**Lean proofs.** `W2.Research.gap_shift_invariant`.

**Related definitions or hypotheses.** `W2.Common.boxClockSq`.

## Lemma W2a-R.5 • Finite-volume clock error

**Status.** Free proof; interacting conjecture.

**Statement.** On the weak interval, c_L[H(g)] = c_ref(g) + O(L⁻²) + O(g⁴ L⁻²), uniformly in g ≤ g∗. At order g⁰ (free theory), c_L = sin(π/L)/(π/L) = 1 − π²/(6L²) + O(L⁻⁴) exactly.

**Argument and outstanding estimate.** For the prescribed free branch the rest mass cancels in the difference of squared gaps. With $t=\pi/L$ the positive speed is $\sin(t)/t$. Integrating the elementary signed sine Taylor bounds gives $0\le c_L-1+t^2/6\le t^4/120$ for $L\ge2$. For the interacting case one needs common $U,V\ge0$ chosen before $L$ and $x$, such that the absolute error is at most $(U+Vx^2)L^{-2}$ throughout the weak interval. Neither the free proof nor the four box values establishes this estimate.

**Lean proofs.** `W2.Common.free_clock_sinc_bounds`.

**Related definitions or hypotheses.** `W2.Common.finiteVolumeBound`.

## Proposition W2a-R.6 • Lowest pole under the free two-link block

**Status.** Free proof.

**Statement.** For the exact free two-link block the lowest visible transverse pole in inherited physical time has phase speed 1+O((aₖ|p|)²). Use [Clock], Proposition 5.1.

**Derivation.** The two-link factor is nonzero on the retained transverse polarization near zero momentum. Any switched low component replaces a squared sine by a squared cosine and raises the energy for $|ap_j/2|<\pi/4$. In inherited time the finite sum of exponentials, divided by its lowest exponential, tends to the positive lowest residue. The pole therefore has the fine-lattice energy and its phase speed tends to one with quadratic error. W2b.9 gives the normalization and the zone-boundary exception. The proof uses the free spectral representation in the physical clock paper, Proposition 5.1.

**Lean proofs.** `W2.W2b.alias_energy_separation`, `W2.W2b.isolated_pole_limit`, `W2.W2b.blocked_symbol_speed`.

## Theorem W2a-R.7 • One-loop preservation of physical dispersion

**Status.** Open conjecture.

**Statement.** Through one loop, the effective dispersion of the blocked theory at scale k + 1 has speed c_ref(gₖ) in physical units: c[Heff,ₖ₊₁] = c_ref(gₖ)(1 + O(gₖ⁴)) + O((aₖp)²).

**Argument and outstanding estimate.** No interacting two-time estimate is supplied. In particular multiplying a positive Hamiltonian by $1+x$ leaves its eigenvectors and vacuum unchanged but scales every gap upward by $1+x$. Its squared speed changes at first order by $2x+x^2$, while a lower form bound can still hold. To close the target one must identify the same centre-neutral branch and bound its moving-minus-rest squared gaps on both sides, uniformly through one loop. The Lean witness verifies the obstruction to the proposed deduction.

**Lean proofs.** `W2.W2d.upward_shift_witness`.

**Related definitions or hypotheses.** `W2.Research.dispersionAtOneLoop`.

## Theorem W2a-R.8 • Wilson coefficient in the B2 convention

**Status.** Analytic reduction and numerical quadrature.

**Statement.** In B2 convention the Wilson coefficient from the reduced kernel is c₁(N)=αN+β/N. Reproduce −0.167509851556 for SU(2) and −0.334167632989 for SU(3) from [Clock] §§6–7. Record the residual against the printed Hamiltonian-limit pairs.

**Derivation.** The reduced Wilson kernel in the clock paper §§6–7 gives $c_1(N)=-(5I_1+4I_2)N/72+I_1/(6N)$. Collecting the colour factors over a common denominator proves this identity symbolically. Quadrature of the two published reduced integrals, cross-checked using the independent Bessel representation, gives $-0.167509851556$ for SU(2) and $-0.334167632989$ for SU(3). The absolute discrepancies from the printed Hamiltonian-limit pairs are $5.0148\times10^{-5}$ and $6.2367\times10^{-5}$. They exceed pair-rounding alone. The field-theoretic kernel derivation is cited and the numerical quadrature is reproducible in Python.

**Lean proofs.** `W2.Research.kernel_group_dependence`.

## Proposition W2a-R.9 • Optional shift from Wilson truncation

**Status.** Conditional identity; group values open.

**Statement.** With the stated truncation convention, κ_local=(κ_E−κ_B)/2=−Δc_irr. Give the coefficient argument. Group-specific values require additional input.

**Argument and outstanding estimate.** For electric and magnetic slopes the square root of their ratio has linear coefficient $(\kappa_E-\kappa_B)/2$. In the stated truncation convention the discrepancy relative to the physical response contributes $-\Delta c_{\mathrm{irr}}$. Differentiating the normalized product gives exactly this slope because the physical multiplier has value one and zero first derivative. Numerical SU(2) and SU(3) shifts would need the omitted irrelevant-operator responses. The free W2b and Scheme A comparisons do not require these values.

**Lean proofs.** `W2.Research.local_shift_derivative`.

## Theorem W2a-R.10 • Regularity of the interacting reference clock

**Status.** Open conjecture.

**Statement.** c[H(g)] exists for 0 < g ≤ g∗, is C² as a function of g² with c_ref(g) = 1 + c₁g² + R(g), |R(g)| ≤ M_c′ g⁴, uniformly in L through Lemma W2a-R.5.

**Argument and outstanding estimate.** A normalized positive $C^2$ branch with a uniform quadratic remainder throughout the weak interval is the missing assertion. If $c=1+c_1x+e$, $|e|\le M x^2$, and $c\ge d>0$, then $1-c(1-c_1x)=c_1^2x^2-e(1-c_1x)$. Division by $c$ proves the inverse-clock remainder with constant $(c_1^2+(1+|c_1|x_*)M)/d$. This last inequality is checked. Neither it nor a Taylor fit constructs a nonperturbative clock or its strong-coupling endpoint.

**Lean proofs.** `W2.Research.reciprocal_remainder`.

**Related definitions or hypotheses.** `W2.Research.positiveWeakClock`, `W2.Common.ClockRegularityHyp`.

# W2b • The exact Gaussian block

## Proposition W2b.1 • Transverse Gaussian vacuum

**Status.** Free proof.

**Statement.** The transverse positive-frequency part of H₀ is coupling free. With K=d*d its vacuum covariance is ½K^(−1/2) on this subspace. Specify the treatment of periodic harmonic zero modes before taking the inverse.

**Derivation.** Use $U=\exp(gA)$, $E\mapsto E/g$ on the linearized phase space. The quadratic electric and magnetic terms both lose their factors of $g$. On the Gauss-law quotient diagonalize $K=d^*d$ on its positive subspace. At frequency $\omega>0$, differentiating $\exp(-\omega x^2/2)$ twice gives the oscillator energy $\omega/2$. Squaring and normalizing the wave function gives position variance $1/(2\omega)$. Functional calculus restores $K^{-1/2}/2$. Remove periodic harmonic coordinates before inversion. The finite computations use one Maxwell component and the linear Gaussian sector.

**Lean proofs.** `W2.W2b.quadratic_coupling_cancel`, `W2.W2b.gaussian_derivative`, `W2.W2b.oscillator_ground_equation`, `W2.W2b.oscillator_variance`.

## Proposition W2b.2 • Periodic and open transverse gaps

**Status.** Free proof.

**Statement.** With ω(k)² = Σᵢ 4 sin²(kᵢ/2), k ∈ (2π/L)ℤ³: Γₖ = 2 sin(π/L)/aₖ, Γₖ₊₁ = sin(2π/L)/aₖ, Γₖ/Γₖ₊₁ = 1/cos(π/L) = 1 + π²/(2L²) + O(L⁻⁴).

**Derivation.** The periodic difference symbol is $e^{iaq_j}-1$ and its transverse singular value is $2\sqrt{\sum_j\sin^2(aq_j/2)}/a$. The smallest positive value occurs on an axial first momentum. With $t=\pi/L$ the two physical gaps are $2\sin(t)/a$ and $\sin(2t)/a$. Both are positive for even $L\ge4$ and the double-angle formula gives $\sec t$. For the open cubical path complex with $L$ links and $L+1$ vertices per axis, the first free transverse mode requires two nonzero path indices. Its gap is $2\sqrt{2}\sin(\pi/(2(L+1)))/a$. Compare to the coarse complex with $L/2$ links and spacing $2a$. The exact periodic ratio in Lean begins from the two explicit gap formulas. The optional full operator diagonalization is analytic and numerical here.

**Lean proofs.** `W2.W2b.gap_ratio_eq_inv_cos`, `W2.W2b.angle_bounds`.

## Corollary W2b.3 • Fourth-order remainder of the periodic gap ratio

**Status.** Free proof.

**Statement.** With m = Γₖ₊₁, aₖm = sin(2π/L) = 2π/L + O(L⁻³), hence Γₖ/Γₖ₊₁ − 1 = (aₖm)²/8 + O((aₖm)⁴). The free value of the lattice-artifact constant is C_a^free = 1/8.

**Derivation.** Put $t=\pi/L$, $h=\cos t$ and $am=\sin(2t)$ for the coarse gap $m$. The error $1/h-1-\sin^2(2t)/8$ factors as $(1-h)^2(2+2h+2h^2+h^3)/(2h)$. On this range $1/2\le h\le1$, the last factor is at most seven and $1-h\le\sin^2(2t)$. Consequently the error lies between zero and $7(am)^4$. This proves the coefficient $1/8$ with a finite-box remainder.

**Lean proofs.** `W2.W2b.free_artifact_constant`, `W2.W2d.free_Ca_matches`.

## Lemma W2b.4 • Axial covariance of the exact spatial block

**Status.** Free symbol proof; both polarizations tested.

**Statement.** Compute the complete blocked covariance including all fine-zone aliases. For momentum (p,0,0), a transverse component i=2 and z=a|p|, let R(z)=Varν(B₂)/Varμ(B₂) in link coordinates with matched leading normalization. The normalized ratio has a nonzero linear correction.

$$R(z) = \frac{\sin z}{2}\left( \frac{1}{s} + \frac{1}{h} + \frac{1}{\sqrt{1 + s^{2}}} + \frac{1}{\sqrt{1 + h^{2}}} \right).$$

$$R(z) = 1 + \left( 1 + \frac{1}{2\sqrt{2}} \right)z + O\left( z^{2} \right).$$

Set s=sin(z/2), h=cos(z/2) and use unitary Fourier transforms. The fine-to-coarse variance factor is 1/8. Four transverse aliases are visible for this polarization. Three gapped contributions at equal time account for the positive slope; the same contributions decay at large time.

**Derivation.** Take $z=a|p|$, $s=\sin(z/2)$ and $h=\cos(z/2)$. For momentum along axis 1, polarization 2, the two-link factor kills the four aliases with $r_2=1$. The other four have unit transverse projector entry, squared form factor four and dimensionless energies $2s,2h,2\sqrt{1+s^2},2\sqrt{1+h^2}$. The unitary Fourier volume ratio is $1/8$. Dividing the variance by its coarse Wilson value gives $R=(\sin z/2)(1/s+1/h+1/\sqrt{1+s^2}+1/\sqrt{1+h^2})$. The singular term simplifies to $h$, and differentiating the smooth continuation gives $R(0)=1$, $R'(0)=1+1/(2\sqrt2)$. Thus the earlier quadratic relative covariance estimate fails already on the axis. For a general direction write $ap=zu$, $|u|=1$, and use link-midpoint phases. In the zero alias, $2\cos(ap_j/2)=2+O(z^2)$, both unit gradient directions equal $u+O(z^2)$, and the dimensionless coarse/fine frequency ratio is $2+O(z^2)$. The normalized lowest-alias operator is therefore $I+O(z^2)$ on the coarse transverse plane. For a nonzero alias with $k$ switched axes, the frequency at zero is $2\sqrt{k}$. Its form factor vanishes on switched axes; on the unswitched ones the transverse projector is the identity. After the volume factor, its linear coefficient is the diagonal projection onto the unswitched axes divided by $2\sqrt{k}$. Each coordinate occurs in two singleton contributions and one doubleton contribution. The sum is $(1+1/(2\sqrt2))I$. High-alias symbols are smooth near zero and there are only seven of them. Thus both transverse eigenvalues equal $1+(1+1/(2\sqrt2))z+O(z^2)$ uniformly in direction. Lean checks the scalar background identity and the exact axial derivative. The projector expansion is the analytic step. The numerical tables test both polarizations.

**Lean proofs.** `W2.W2b.axis_alias_reduction`, `W2.W2b.axialRatio_zero`, `W2.W2b.axis_ratio_slope`, `W2.W2b.alias_background_is_scalar`.

## Proposition W2b.5 • Kinetic normalization and Gaussian transport

**Status.** Free proof.

**Statement.** At equal free couplings rₖ=4. In the normalized axial channel the covariance-matching transport has multiplier R(z)^(−1/2). Its limit is one and its first correction is linear in z. State the time, physical link and unitary Fourier normalizations.

**Derivation.** With $c_k=g^2/(2a)$ and $c_{k+1}=g^2/(4a)$, summing two fine link gradients gives $r_k=2c_k/c_{k+1}=4$. In the normalized scalar channel a linear map from the blocked law to the reference rescales by the standard-deviation ratio $R^{-1/2}$. From W2b.4 it has value one and derivative $-(1+1/(2\sqrt2))/2$ at the origin. Equal-time transport and retained-time spectral comparison therefore require separate calculations.

**Lean proofs.** `W2.W2b.normalization_scalar`, `W2.W2b.axis_transport_slope`.

## Theorem W2b.6 • Eliminated gap, Gaussian score and Schur correction

**Status.** Finite and axial result; uniform claim open.

**Statement.** Measure (a) the eliminated gap on the gauge quotient, with the computed chaos sector and harmonic convention identified, (b) the conditional score and its covariance in the original group coordinate, and (c) the Schur correction divided by retained energy at λ=m on the first axial mode. Derive or refute the proposed quadratic scaling and give the sign of the combined Schur margin.

For a unit-variance retained axial oscillator put E₀=2 sin(z/2), m=sin z in fine units, wᵢ=(1/Eᵢ)/Σⱼ(1/Eⱼ) on the four visible aliases, and A=Σwᵢ Eᵢ. Compare the matrix resolvent with A−m−[Σwᵢ/(Eᵢ−m)]⁻¹. Report the normalized bare correction, the Schur margin and the full fine gap separately.

**Argument and outstanding estimate.** In units $a=1$, let $m=\sin z$, let $E_i$ be the four positive axial energies of W2b.4, and set $w_i=(1/E_i)/\sum_j1/E_j$. The normalized retained coordinate has energy $A=\sum_iw_i E_i=4/\sum_i1/E_i$. In its orthogonal complement compress the diagonal energy to $D$ and denote the coupling by $B$. Taking the retained entry of the inverse of $H-mI$ gives the positive margin $J_*=(\sum_i w_i/(E_i-m))^{-1}$. The bare correction is $A-m-J_*$. Put $h=m/E_0\to1$, $T=\sum_i E_0/E_i\to1$ and $b=J_*/E_0$. Keeping just the first positive summand gives $0<b\le(1-h)T$. Hence $(A-m-J_*)/A=1-(h+b)T/4\to3/4$. This disproves a vanishing bare ratio in the axial free channel while preserving a positive signed margin at each finite box. The companion independently computes the full first-chaos compressions, score, eliminated gaps and mixed norms. Higher chaoses, the colour-singlet physical sector and the interacting uniform estimate remain separate.

**Lean proofs.** `W2.Framework.schur_all_retained`, `W2.W2b.axial_harmonic_mean`, `W2.W2b.resolvent_entry_identity`, `W2.W2b.resolvent_remainder`, `W2.W2b.raw_schur_limit`.

**Related definitions or hypotheses.** `W2.Research.uniformEliminated`, `W2.Research.uniformSignedSchur`.

## Proposition W2b.7 • Spatial tails of the precision and score kernels

**Status.** Open uniform bounds; finite evidence.

**Statement.** Test the |k| singularity of the free precision and its predicted |x|⁻⁴ tail in three dimensions. Estimate the conditional-score covariance kernel separately. Report shell exponents and absolute row sums, and state what volume-uniform majorants remain unproved.

**Argument and outstanding estimate.** The precision symbol has the infrared degree of $|p|$. Its continuum homogeneous transform has degree $-4$ in three dimensions. To turn this into a lattice bound uniform in volume requires control of the projection, smooth remainder and periodization. If the norm at radius $n$ is at most $C/n^4$ and a shell has at most $Kn^2$ sites, its total is at most $KC/n^2$, which is summable. The measured precision exponents approach four. The score row sums grow across the four grids and the fitted score exponent does not establish a uniform summable majorant. A separate estimate for that kernel is missing.

**Lean proofs.** `W2.W2b.shell_bound`.

**Related definitions or hypotheses.** `W2.Research.polynomialKernelBound`.

## Corollary W2b.8 • A conditional obstruction to exponential envelopes

**Status.** Conditional proof.

**Statement.** Exponential cluster methods do not apply directly to ψₖ²; local norms in W2d and W2e must allow polynomial tails.

**Derivation.** Assume a sequence of separations with kernel norm bounded below by $c n^{-4}$, $c>0$. For fixed $C,\mu>0$, $Ce^{-\mu n}<cn^{-4}$ along that sequence eventually. An exponential norm bound contradicts the lower bound. An upper polynomial estimate by itself cannot give this conclusion. A summable weighted framework may instead be obtained from W2b.7 if its uniform hypotheses can be established. The plain map passes the tested free linear gap comparison. Adequacy on the full physical space remains open.

**Lean proofs.** `W2.W2b.tail_obstruction`, `W2.W2b.shell_bound`.

**Related definitions or hypotheses.** `W2.Research.polynomialKernelBound`.

## Proposition W2b.9 • Lowest visible pole in inherited physical time

**Status.** Free proof.

**Statement.** For the exact two-link block the lowest visible transverse pole has energy ω(p) and phase speed ω(p)/|p|=1+O((aₖ|p|)²) at small nonzero physical momentum in inherited time. Cite [Clock], Proposition 5.1.

$$C_{ii}(p,\tau)\  \propto \ \sum_{r}^{}\left| 1 + e^{iaq_{r,i}} \right|^{2}\, P_{ii}^{T}\left( q_{r} \right)\,\frac{e^{- \omega\left( q_{r} \right)|\tau|}}{2\omega\left( q_{r} \right)},$$

$$\omega(q) = \frac{2}{a}\sqrt{\sum_{j}^{}\sin^{2}\left( aq_{j}/2 \right)}.$$

**Derivation.** The two-time covariance is a finite sum $\sum_r w_r e^{-E_r|\tau|}$ with $w_r\ge0$. At small nonzero momentum choose a transverse link component with nonzero retained form factor and residue $w_0>0$. Switching any fine alias replaces at least one $\sin^2(ap_j/2)$ by a strictly larger $\cos^2(ap_j/2)$. Multiplication by $e^{E_0|\tau|}$ leaves a function tending to $w_0$. Taking $-|\tau|^{-1}\log(C(\tau)/C(0))$ recovers $E_0$. The explicit sine bounds give phase speed $1+O((a|p|)^2)$. At $L=4$ the two lowest axial energies coincide. Their residues add. This argument uses inherited time as in Proposition 5.1 of the clock paper.

**Lean proofs.** `W2.W2b.alias_energy_separation`, `W2.W2b.isolated_pole_limit`, `W2.W2b.blocked_symbol_speed`.

## Lemma W2b.10 • Signed finite-box sinc estimate

**Status.** Free proof.

**Statement.** For dimensionless k₁=(2π/L,0,0), use Δ(k)=E₁(k)−E₀ on the same rest and moving branch. In the gauge-theory definition impose Gauss' law and trivial character of all three centre transformations. For prescribed free squared dispersion μ²+4Σⱼsin²(kⱼ/2), μ≥0, and L≥2 the signed quartic bound below holds.

$$c_{L}^{2} = \frac{\Delta\left( k_{1} \right)^{2} - \Delta(0)^{2}}{\left| k_{1} \right|^{2}},\quad\quad c_{L} = \frac{\sin t}{t},\quad\quad 0 \leq c_{L} - 1 + \frac{t^{2}}{6} \leq \frac{t^{4}}{120}.$$

**Derivation.** For the prescribed squared dispersion the rest mass and energy origin cancel. The positive root gives $c_L=\sin t/t$, $t=\pi/L$. For $0\le t\le\pi/2$, the sine is between $t-t^3/6$ and $t-t^3/6+t^5/120$, as follows by successive integration of the elementary cosine bounds. Dividing by $t>0$ proves the signed estimate. It is the same released declaration as W2a-R.5, counted once in the inventory. The box table gives a numerical check on this exact result.

**Lean proofs.** `W2.Common.free_clock_sinc_bounds`, `W2.Research.gap_shift_invariant`.

**Related definitions or hypotheses.** `W2.Common.finiteVolumeBound`.

## Proposition W2b.11 • Angular dependence of the lattice dispersion

**Status.** Free proof.

**Statement.** For the exact free block, ω(p)²=|p|²−(aₖ²/12)Σⱼpⱼ⁴+O(aₖ⁴|p|⁶). The limiting speed is one. Test the angular dependence and cite the scope of any formal remainder bound.

**Derivation.** Expand $2(1-\cos y)=y^2-y^4/12+O(y^6)$, whose fourth derivative at zero is $-2$. Apply this in each component and divide by $a^2$. The result is $\omega^2=|p|^2-a^2\sum_jp_j^4/12+O(a^4|p|^6)$. Taylor's theorem bounds the componentwise remainder by $|ap_j|^6/(360a^2)$. Lean checks the fourth derivative and a nonasymptotic all-direction phase bound. The numerical pole table includes axial and diagonal momenta. This expansion concerns the free branch.

**Lean proofs.** `W2.W2b.blocked_symbol_speed`, `W2.W2b.lattice_fourth_derivative`.

# W2c • Gauge reduction and the eliminated gap

## Proposition W2c.1 • Gauge reduction of a blocking fibre

**Status.** Analytic proof; group identity checked.

**Statement.** The eliminated gauge group fixes every coarse product. The disintegration of the invariant law has invariant conditional measures almost everywhere. Specify an equivariant version for pointwise statements. Gauge-invariant conditionally centred functions descend to the quotient fibres.

**Derivation.** A fine gauge transformation equal to the identity at every retained vertex acts within each fibre. At a midpoint the two transformed links have product $(U_1h^{-1})(hU_2)=U_1U_2$. Invariance of the parent law implies invariance of its conditional distributions almost everywhere by uniqueness of disintegration. Haar averaging over the compact eliminated group gives invariant versions on those fibres. Invariant measurable functions factor through the quotient, and subtracting the conditional mean gives the centred subspace. A pointwise statement for every boundary datum requires a specified equivariant version of the conditional law. Lean checks the group cancellation. The disintegration argument is given here.

**Lean proofs.** `W2.W2c.midpoint_preserves_product`.

## Proposition W2c.2 • Bulk and open-box fibre dimensions

**Status.** Analytic proof; integer count checked.

**Statement.** Per coarse vertex in three dimensions: 8 fine vertices (1 retained, 3 edge midpoints, 3 face centres, 1 body centre) and 24 fine links (6 on coarse paths, 18 unused). The fibre has dimension 21·dim G, G_elim has dimension 7·dim G, and the quotient has dimension 14·dim G per coarse vertex in the bulk.

**Derivation.** In a periodic block with $V$ coarse vertices there are $24V$ fine links and $3V$ coarse link-product constraints. The block map is a submersion because its coarse paths use disjoint pairs of links. The $7V$ eliminated vertices act freely with retained vertices fixed on a connected box. The quotient dimension is $(24-3-7)V\dim G=14V\dim G$. For an open cube with $n$ coarse links per axis, put $V(s)=(s+1)^3$ and $E(s)=3s(s+1)^2$. Subtract the coarse constraints and the eliminated gauge dimensions to get $[E(2n)-E(n)-V(2n)+V(n)]\dim G$. Boundary corrections follow by expansion, giving $(14n^3+9n^2)\dim G$.

**Lean proofs.** `W2.W2c.fibre_dimension_count`, `W2.W2c.open_dimension_count`.

## Theorem W2c.3 • Uniform conditional Poincaré inequality on a quotient

**Status.** Open conjecture.

**Statement.** On the small-field region, the conditional law on fibre/G_elim satisfies a Poincaré inequality with constant C⊥ ≤ gₖ²/c, uniformly in W, the box, the scale and the cutoff, with c explicit.

**Argument and outstanding estimate.** One needs $c>0$ chosen before the box, scale, cutoff and admissible coarse field, with conditional variance at most $(g_k^2/c)$ times the tangential Dirichlet integral. Compactness at fixed dimension gives no such uniform constant. Gauge reduction removes the exact symmetry directions, but it does not yield curvature or comparison estimates for every small-field conditional law. The predicate records the quantifier order. No proof for the interacting Wilson law is available here.

**Related definitions or hypotheses.** `W2.Research.uniformFibrePoincare`.

## Corollary W2c.4 • Eliminated gap from a fibre inequality

**Status.** Conditional proof.

**Statement.** Dₖ ≥ cₖ/C⊥ ≥ c/(2aₖ) =: κ/aₖ on gauge-invariant conditionally centred small-field functions.

**Derivation.** Apply W2c.3 on each fibre to a conditionally centred function and integrate over the coarse field. The tangential gradient norm is controlled by the fine gradient. Multiplication by $c_k=g_k^2/(2a_k)$ gives $D_k(f)\ge c\operatorname{Var}(f)/(2a_k)$. The Rayleigh quotient has the claimed lower bound with $\kappa=c/2$. Lean checks this last implication with the integrated inequalities as premises.

**Lean proofs.** `W2.W2c.eliminated_gap_of_fibre_poincare`.

**Related definitions or hypotheses.** `W2.Research.uniformFibrePoincare`.

## Corollary W2c.5 • Separation of retained and eliminated energies

**Status.** Conditional proof.

**Statement.** With 1 + σ = Λ⊥/m ≥ κ/(aₖm) and aₖm ≤ a_K m · exp[−(gₖ⁻² − g_K⁻²)/(6b₀)] (W2d Proposition W2d.5): s = σ/(1 + σ) ≥ 1 − aₖm/κ → 1 along weak trajectories, uniformly in the box.

**Derivation.** For $m,a,\kappa>0$ and $\Lambda\ge\kappa/a$, inversion yields $m/\Lambda\le am/\kappa$. Thus $s=1-m/\Lambda\ge1-am/\kappa$. Inserting W2d.5 makes the error decay exponentially in the inverse squared coupling along the specified weak trajectory. A numerical lower bound at $x_*=1/6$ still needs $a_Km$ and the interacting $\kappa$. A first-chaos measured gap cannot supply that constant.

**Lean proofs.** `W2.W2c.cor_5_separation`, `W2.W2d.lattice_artifact_decay`.

**Related definitions or hypotheses.** `W2.Research.uniformEliminated`.

## Proposition W2c.6 • A fibre measure with collapsing Rayleigh quotient

**Status.** Analytic proof; Rayleigh bound checked.

**Statement.** Wb’s negative control (density e^(s x²) with a centred odd function whose gradient lives in |x| ≤ 1/4) collapses the eliminated gap as s grows. A uniform lower bound on the conditional Hessian (log-concavity up to O(gₖ²)) excludes it on small fields.

**Derivation.** On $[-1,1]$ use weight $e^{sx^2}$, $s\ge0$. Take the odd function $f(x)=\max(-1,\min(1,4x))$. Its weighted mean is zero, and its derivative is supported on $|x|<1/4$. The unnormalized energy is at most $8e^{s/16}$. On $|x|\ge1/2$ its squared norm is at least $e^{s/4}$ after integration. The common partition function cancels. Its Rayleigh quotient is at most $8e^{-3s/16}$ and tends to zero. A volume-uniform positive curvature hypothesis for the negative log density would exclude this example; that hypothesis for the actual small-field measure is open.

**Lean proofs.** `W2.W2c.negative_control`.

# W2d • Transport and the retained form

## Lemma W2d.1 • Derivative bounds for coarse-field transport

**Status.** Open conjecture.

**Statement.** A bound on ‖DΦₖ − (scale)·I‖ in a local norm allowing the polynomial tails of W2b Proposition W2b.7, uniform in the volume, and the resulting comparison of |∇u|² dνₖ with |∇F|² dμₖ₊₁.

**Argument and outstanding estimate.** On the axial free channel the derivative of the multiplier with respect to momentum has nonzero first coefficient by W2b.5. This fixes a normalization and rules out a blanket quadratic symbol estimate at that point. A field-space derivative bound in a volume-uniform, polynomially weighted local norm needs an explicit transport, its regularity and its derivative estimates for the interacting measures. The momentum derivative in Lean does not supply these field-space estimates.

**Lean proofs.** `W2.W2b.axis_transport_slope`.

**Related definitions or hypotheses.** `W2.Research.uniformTransport`.

## Theorem W2d.2 • Uniform small-field retained-form defect

**Status.** Open conjecture with a Gaussian obstruction.

**Statement.** Uniformly in box, scale and cutoff: Dₖ^small(F) ≥ −½Rₖ(F) − (C_S gₖ⁴ + C_a(aₖm)²) m Var_{μₖ₊₁}(F).

**Argument and outstanding estimate.** For an axial linear observable of unit variance at the reference gap, $R_{\mathrm{excess}}=0$. Since $r=4$ and $A=4m/R(z)$, the normalized defect is $A/(4m)-1=R(z)^{-1}-1=-(1+1/(2\sqrt2))z+O(z^2)$. At order $g^0$ this violates the proposed lower bound with only $C_a(am)^2$ for all large boxes, if the observable class includes this channel. The full interacting statement needs a sector argument or a changed comparison retaining sufficient excess. A counterexample on a single Maxwell component alone is insufficient to draw the same conclusion for all gauge-invariant singlet observables.

**Lean proofs.** `W2.W2b.axial_harmonic_mean`, `W2.W2b.normalized_defect_slope`.

**Related definitions or hypotheses.** `W2.Research.uniformDefect`.

## Corollary W2d.3 • Retained gap from a defect bound

**Status.** Conditional proof.

**Statement.** 𝒜ₖ(u) ≥ (1 − αₖ) m ‖u‖² with αₖ ≤ C_S gₖ⁴ + C_a(aₖm)², using rₖ ≥ 1 (A g∗² + B g∗⁴ ≤ 3/4 suffices).

**Derivation.** Write the reference energy as $mV+R$ with $R\ge0$, and $D=A/r-(mV+R)$. If $D\ge-R/2-bmV$, then $A/r\ge(1-b)mV+R/2$. Assuming $0\le b\le1$, $mV\ge0$ and $r\ge1$, multiplication by $r$ preserves the asserted lower bound. Insert $b=C_Sg^4+C_a(am)^2$ in its stated range. This implication can be applied only after the actual retained comparison has been established.

**Lean proofs.** `W2.W2d.retained_of_defect`.

**Related definitions or hypotheses.** `W2.Research.uniformDefect`.

## Proposition W2d.4 • Cancellation of the order-$g^2$ defect coefficient

**Status.** Conditional coefficient identity; completeness open.

**Statement.** Test whether the g² coefficient lies in the span of the coupling and physical-clock mismatches. Under this completeness assumption, zero mismatches give zero coefficient. Control of the remaining terms, including any linear lattice term, requires its own bound.

**Argument and outstanding estimate.** If the coefficient equals $u\bar\kappa+v\kappa_{\mathrm{phys}}$, it vanishes when both mismatches vanish. Lean proves that algebraic implication. It remains to derive this representation for the full interacting form, uniformly over observables, and to bound the remainder. The nonzero Gaussian lattice term in W2d.2 is independent of this order-in-coupling argument.

**Lean proofs.** `W2.W2d.no_quadratic_term`.

**Related definitions or hypotheses.** `W2.Research.completeMismatch`.

## Proposition W2d.5 • Exponential suppression along a weak run

**Status.** Conditional proof.

**Statement.** With m fixed in physical units, K the last weak step, A₊ = 3A/2 under Bg∗² ≤ A/2: aₖm ≤ a_K m · exp[−(gₖ⁻² − g_K⁻²)/(6b₀)], hence (aₖm)² ≤ (a_K m)² exp[−(gₖ⁻² − g_K⁻²)/(3b₀)], smaller than e^(−c/gₖ^δ) for δ < 2 as gₖ → 0.

**Derivation.** Write $n=K-k$, $d=g_k^{-2}-g_K^{-2}$. The upper decrement gives $d\le n A_+$ with $A_+=6b_0\log2$ under the stated smallness bound. Since $a_k=a_K2^{-n}$, exponentiating $-n\log2\le-d/(6b_0)$ gives the required bound. Squaring doubles the exponent. As $g\to0$ at fixed endpoint, a negative constant times $g^{-2}$ dominates $-c g^{-\delta}$ for $0<\delta<2$. The Lean inequality explicitly takes the upper decrement as input, separate from the lower decrement for product transfer.

**Lean proofs.** `W2.W2d.lattice_artifact_decay`.

**Related definitions or hypotheses.** `W2.Common.RunningBoundHyp`.

## Corollary W2d.6 • Geometric sum of lattice artifacts

**Status.** Proof.

**Statement.** Σₖ(aₖmₖ)² ≤ (4/3)(a_w m̄)², with mₖ ≤ m̄ and a_w the last weak spacing [W2a Theorem 12].

**Derivation.** If the final weak spacing is bounded by $a_w$ and masses by $\bar m$, the squared contributions backward from the last step are bounded by $(a_w\bar m)^2\,4^{-j}$. Summing the finite geometric series gives a bound of $4(a_w\bar m)^2/3$. The checked proof includes the empty run and requires positivity and doubling at the actual steps.

**Lean proofs.** `W2.W2d.artifact_geometric_sum`.

## Theorem W2d.7 • Spectral bridge from retained forms to a moving pole

**Status.** Open conjecture.

**Statement.** Obtain the interacting dispersion through one loop on the same centre-neutral branch from two-time physical evolution. Supply two-sided control of the squared-gap difference. The one-sided defect and cancellation of one coefficient leave an upward shift possible.

**Argument and outstanding estimate.** A form lower bound does not determine the slope of a moving-minus-rest squared gap. Even the family $H_x=(1+x)H_0$ has the same vacuum at each $x$ and allows positive first-order change in the speed. The checked identity gives the squared change $2x+x^2$. A proof needs the same isolated physical branch, overlap under blocking, and a two-sided estimate in inherited time to the claimed order. For a positive reference speed, factoring the difference of squares bounds the speed error by the two-sided squared-speed error divided by the reference speed. Lean checks this sufficient bridge.

**Lean proofs.** `W2.W2d.upward_shift_witness`, `W2.W2d.speed_from_squared_gap`.

**Related definitions or hypotheses.** `W2.Research.dispersionAtOneLoop`.

# W2e • Conditional scores and the Schur form

## Proposition W2e.1 • Leading scale of the conditional score

**Status.** Gaussian computation; interacting estimate open.

**Statement.** Expanding log ρₖ = 2 log ψₖ on small fields, the order-g⁰ (Gaussian) coupling between retained and eliminated modes for 𝒞ₖ either vanishes, giving Sᵢ = O(gₖ), or does not, giving Sᵢ = O(gₖ⁻¹), Jₖ = O(gₖ⁻²) and ζₖ = O(1).

**Argument and outstanding estimate.** In fine Gaussian coordinates let $T$ be the two-link map restricted to the transverse quotient, $TT^*=2I$, and $Q=2\Omega$ the fine precision. Differentiating the conditional Gaussian log density gives residual precision covariance $TQT^*/4-C_\nu^{-1}$. Its largest eigenvalue is positive on the sampled boxes. In original group coordinates a derivative contributes $1/g$, so the free score covariance contributes at order $g^{-2}$. The four measured values of $g^2J_k$ are given in the table. Establishing uniform interacting bounds on the expansion requires control of its remainder.

**Lean proofs.** `W2.Framework.uniform_score_lift`.

**Related definitions or hypotheses.** `W2.Research.scoreBounds`.

## Theorem W2e.2 • Uniform score route to a small loss

**Status.** Conditional route; cancellation premise fails in tested model.

**Statement.** Investigate the uniform score route where its Gaussian cancellation premise holds. The plain map already has a nonzero Gaussian score in the tested quotient. State the scope of any remaining interacting row-sum estimate.

**Derivation.** When the covariance bound and $\Lambda_\perp>m$ hold, the resolvent norm is bounded by $(\Lambda_\perp-m)^{-1}$. Substituting the score bound gives a constant times the retained energy. The Lean implication checks the scalar lift. For the plain product block the free transverse Gaussian has a nonzero score contribution, so the cancellation premise of the proposed quartic route already fails in that channel. A row-sum or a norm estimate for a different map, sector or subtracted score requires independent evidence.

**Lean proofs.** `W2.Framework.uniform_score_lift`.

**Related definitions or hypotheses.** `W2.Research.uniformScoreRoute`, `W2.Research.scoreBounds`.

## Theorem W2e.3 • Direct Schur comparison with retained excess

**Status.** Axial counterexample; signed conjecture open.

**Statement.** For the plain map compute the mixed correction together with the retained energy above the spectral threshold. Obtain an explicit signed Schur lower bound or identify the obstruction. The raw quadratic target on every low-momentum mode is challenged by W2b.6(c).

**Argument and outstanding estimate.** At trial energy $m$ the bare correction divided by retained energy tends to $3/4$ on the first axial Gaussian mode by W2b.6. A uniform $C(am)^2$ bare estimate on a class containing this mode is impossible in the free limit. Nevertheless $A-m-B^*(D-mI)^{-1}B>0$ at each tested axial momentum. Completion of squares gives the exact equivalence between positivity of the block form and its signed Schur complement. For the interacting model the remaining target is a uniform lower bound on $A$ minus the correction at the chosen trial gap. This must use the correct observable class and the positive eliminated denominators.

**Lean proofs.** `W2.Framework.schur_criterion`, `W2.Framework.schur_all_retained`, `W2.W2b.raw_schur_limit`.

**Related definitions or hypotheses.** `W2.Research.uniformMixedBound`, `W2.Research.uniformSignedSchur`.

## Corollary W2e.4 • Loss bound under a Schur comparison

**Status.** Conditional proof.

**Statement.** If either route supplies the required one-step comparison, the loss is bounded by the sum of its retained and mixed allowances. When using the signed route state the bound on retained energy minus the correction directly.

**Derivation.** Given retained and mixed allowances $\alpha,\epsilon\ge0$ yielding a comparison at $(1-\alpha)(1-\epsilon)m$, expand the relative loss as $\alpha+\epsilon-\alpha\epsilon\le\alpha+\epsilon$. A bound made directly on the signed form instead gives its own trial gap by the Schur criterion. The nonvanishing raw correction of W2e.3 cannot be inserted as a vanishing allowance.

**Lean proofs.** `W2.W2e.loss_of_mixed_bound`, `W2.Framework.schur_all_retained`.

**Related definitions or hypotheses.** `W2.Research.uniformSignedSchur`.

## Lemma W2e.5 • Clock invariance of the resolvent ratio

**Status.** Proof.

**Statement.** For every ξₖ > 0: βₖ² ⟨h⊥ᵤ, (ξₖDₖ − ξₖλ)⁻¹ h⊥ᵤ⟩ / 𝒜ₖ^ξ(u) = (2cₖ)² ⟨h⊥ᵤ, (Dₖ − λ)⁻¹ h⊥ᵤ⟩ / 𝒜ₖ(u).

**Derivation.** Let $\xi>0$. Diagonalize the eliminated block at energies $d_i$ with $d_i>\lambda$. Under time scaling its resolvent denominators acquire a factor $\xi$, the squared mixed coupling gains $\xi^2$ and the retained energy gains $\xi$. Substitution cancels all three powers, term by term. Lean verifies the finite-eigenbasis formula with arbitrary coefficients. In a self-adjoint operator formulation the same identity follows from the resolvent scaling law on its resolvent set.

**Lean proofs.** `W2.W2e.resolvent_ratio_clock_invariant`.

# W2f • Small-field assembly and transfer

## Theorem W2f.1 • Conditional one-step small-field gap

**Status.** Conditional proof.

**Statement.** Assume W2c (Λ⊥ ≥ κ/aₖ), W2d (αₖ) and W2e (mixed term). In the isotropic convention, by Wb Theorem 3: ηₖ^small ≤ (C_S + C_M)gₖ⁴ + (C_a + C′_a)(aₖm)² =: C₄gₖ⁴ + C_a″(aₖm)².

**Derivation.** In Scheme A the exactly matched clock contributes no per-step mismatch. Given retained and mixed allowances, add their $g^4$ and $(am)^2$ coefficients to get $C_4=C_S+C_M$ and $C_a''=C_a+C'_a$. Alternatively, diagonalize the positive eliminated block and use a signed lower estimate directly. Completing the square in each eliminated coordinate gives the target quadratic-form lower bound at the resulting trial gap. The Lean master theorem exposes the signed estimate as its premise. Its validity for the interacting small-field sector is conditional on the estimates identified above.

**Lean proofs.** `W2.W2f.small_field_loss`, `W2.W2f.master_small_field`, `W2.Framework.schur_all_retained`.

**Related definitions or hypotheses.** `W2.Research.uniformEliminated`, `W2.Research.uniformDefect`, `W2.Research.uniformSignedSchur`.

## Proposition W2f.2 • Orientation of the endpoint clock

**Status.** Conditional proof.

**Statement.** Under physical speed preservation and time covariance the product of inherited-time step factors is c_ref(g₀)/c_ref(g_J). Fix a consistent endpoint convention when translating a certificate back to isotropic units. State every additional regularity or interval hypothesis.

**Derivation.** Each inherited-time step contributes $c(x_k)/c(x_{k+1})$ in the convention of W2a-R.2, hence $Z_{\mathrm{clock}}=c(x_0)/c(x_J)$. With $c(x_0)\to1$ the limit is $1/c(x_J)$. When a certificate is expressed in a clock-scaled Hamiltonian one converts its gap back by dividing by the incoming clock. This explicit division prevents counting a reciprocal twice. Bounds on step ratios yield the exponential estimate by $1+y\le e^y$.

**Lean proofs.** `W2.W2f.clock_endpoint_factor`, `W2.W2aR.kinetic_ratio_clock`.

**Related definitions or hypotheses.** `W2.Common.ClockRegularityHyp`, `W2.Common.DispersionHyp`.

## Corollary W2f.3 • Mismatch allowance for truncated time calibration

**Status.** Conditional proof.

**Statement.** Under Scheme B the clock contributes M_match^B gₖ⁴ per step, i.e. C₄ = C_S + C_M + M_match^B, and Z_clock is replaced by ξ_B(g_J)/ξ_B(g₀).

**Derivation.** Set $\xi_B(x)=1-c_1x$. Its adjacent ratios give the endpoint factor $\xi_B(x_J)/\xi_B(x_0)$ exactly. The pointwise Scheme B estimate from W2a-R.1 bounds the mismatch by $M_{\mathrm{match}}^B x_k^2$. Adding it to the retained and mixed step losses changes $C_4$ to $C_S+C_M+M_{\mathrm{match}}^B$. The checked inequalities specify the positivity and smallness assumptions needed for these ratios.

**Lean proofs.** `W2.W2f.small_field_loss_schemeB`, `W2.W2aR.step_error_schemeB`.

**Related definitions or hypotheses.** `W2.Common.ClockRegularityHyp`.

## Theorem W2f.4 • Positive product through the weak interval

**Status.** Conditional proof.

**Statement.** With the large-field bound of W3, ηₖ^large ≤ C_L e^(−c/gₖ^δ), and ηₖ ≤ r < 1 on weak steps: Σηₖ ≤ S, S = (C₄ + C_L D_δ)(g∗⁴ + g∗²/A₋) + (4/3)C_a″(a_w m̄)², D_δ = (4/(ecδ))^(4/δ), and the weak-step product is at least exp[−S/(1 − r)].

**Derivation.** Maximizing $u^{4/\delta}e^{-u}$ gives $e^{-c/g^\delta}\le D_\delta g^4$ with $D_\delta=(4/(ec\delta))^{4/\delta}$. The inverse-coupling decrement and integral comparison bound $\sum x_k^2$ by $x_*^2+x_*/A_-$. Add the geometric artifact sum of W2d.6 to get the stated $S$. For $0\le\eta_k\le r<1$, integration of $(1-t)^{-1}$ gives $\log(1-\eta_k)\ge-\eta_k/(1-r)$. Multiply the factors to obtain $\prod(1-\eta_k)\ge e^{-S/(1-r)}$. The physical W3 large-field estimate and the uniform step bound are external premises.

**Lean proofs.** `W2.W2f.exp_le_Ddelta`, `W2.W2f.weak_product_floor`, `W2.W2d.artifact_geometric_sum`.

**Related definitions or hypotheses.** `W2.Common.RunningBoundHyp`.

## Theorem W2f.5 • Conditional transfer to the fine-scale gap

**Status.** Conditional proof.

**Statement.** Under (H_int) and (B_int) of Section 9: Γ₀ ≥ Z_clock · z_L m_IR · b^M · exp[−S/(1 − r)], with M ≤ ⌈(g∗⁻² − g₁(N)⁻²)/A_int⌉ and z_L the endpoint clock.

**Derivation.** Sum the assumed intermediate inverse-coupling decrement to bound the number $n$ of intermediate steps by $M=\lceil(g_*^{-2}-g_1^{-2})/A_{\mathrm{int}}\rceil$. For $0<b\le1$ the intermediate product is at least $b^n\ge b^M$. Combine this with W2f.4 and the positive calibrated infrared endpoint to obtain the displayed fine-gap inequality. Two positive functions can agree throughout the weak interval and differ at a later endpoint, so specifying the strong clock or an independently controlled bridge is essential. The Lean proof checks the product comparison and this endpoint nonuniqueness; the W3/W4 physical inputs remain open.

**Lean proofs.** `W2.W2f.fine_scale_gap`, `W2.W2aR.intermediate_step_count`, `W2.W2f.endpoint_not_determined`, `W2.W2f.weak_product_floor`.

**Related definitions or hypotheses.** `W2.Common.RunningBoundHyp`.

# Finite-box evidence

Each periodic box has $L$ fine links per side and physical length $La$. The computations set $a=1$, use unitary Fourier transforms, remove the harmonic zero mode and retain both transverse coordinates. The linear Gaussian space consists of centred linear functions of the Gaussian field. It is the first Wiener chaos. The tables report calculations in that space.

## Periodic gap, clock and static covariance

| $L$ | Fine gap | Coarse $m$ | Gap ratio | $c_L$ | $R(2\pi/L)$ |
|---|---|---|---|---|---|
| 4 | 1.414214 | 1.000000 | 1.414214 | 0.900316 | 2.230710 |
| 8 | 0.765367 | 0.707107 | 1.082392 | 0.974495 | 1.896452 |
| 16 | 0.390181 | 0.382683 | 1.019591 | 0.993587 | 1.500282 |
| 32 | 0.196034 | 0.195090 | 1.004839 | 0.998394 | 1.259423 |

The two gap columns use the same physical time. The equal-time column divides the blocked variance by its coarse Wilson reference. The signed sinc remainder and its upper bound are retained at full precision in the data files.

## Signed margin at the first axial mode

| $L$ | Retained $A$ | Correction | Correction / $A$ | Margin | Defect / $m$ |
|---|---|---|---|---|---|
| 4 | 1.793151 | 0.232321 | 0.129560 | 0.560830 | -0.551712 |
| 8 | 1.491431 | 0.669751 | 0.449066 | 0.114573 | -0.472700 |
| 16 | 1.020297 | 0.626171 | 0.613715 | 0.011443 | -0.333459 |
| 32 | 0.619618 | 0.423333 | 0.683217 | 0.001194 | -0.205986 |

The margin is $A-m-B^*(D-mI)^{-1}B$. The final column is the W2d defect for a unit-variance observable. The exact limiting bare ratio is $3/4$. The positive finite margin explains how the free gap comparison can pass.

## Open-box calibration

The open path complex has $L+1$ vertices per axis; the coarse path has $L/2+1$. The first co-closed mode has two active path frequencies. The paths in the two complexes determine the open spectrum independently of the periodic formula.

| Fine links / side | Fine gap | Coarse gap | Open ratio |
|---|---|---|---|
| 4 | 0.874032 | 0.707107 | 1.236068 |
| 8 | 0.491151 | 0.437016 | 1.123875 |
| 16 | 0.260974 | 0.245576 | 1.062705 |
| 32 | 0.134582 | 0.130487 | 1.031381 |

# Scores, spectra and spatial kernels

## Gaussian first-chaos comparisons

| $L$ | $\alpha$ | $a\Lambda_\perp$ | Mixed norm | $g^2J$ | $\zeta$ |
|---|---|---|---|---|---|
| 4 | 0.000000 | 1.414214 | 0.258819 | 0.138701 | 0.334853 |
| 8 | 0.000000 | 1.391793 | 0.485528 | 0.377938 | 0.551988 |
| 16 | 0.000000 | 1.391793 | 0.682703 | 0.777413 | 0.770395 |
| 32 | 0.000000 | 1.391043 | 0.780396 | 1.134785 | 0.948855 |

The mixed norm is the maximum of the singular norm of $D^{-1/2}BA^{-1/2}$ over coarse momenta. With $a=1$, $2c_k=g^2$, hence $\zeta=g^2 J/(\Lambda_\perp-m)$. $J$ uses an operator norm over Fourier blocks. The absolute row sums below are separate, stronger real-space diagnostics.

| $L$ | Precision row sum | Score row sum | Precision exponent | Score exponent |
|---|---|---|---|---|
| 4 | 15.614511 | 0.209769 | — | — |
| 8 | 17.121930 | 1.165468 | 3.546517 | — |
| 16 | 17.833493 | 2.676945 | 3.898304 | 1.647908 |
| 32 | 18.183673 | 4.576503 | 3.948826 | 2.238188 |

Shell exponents are log–log fits of Frobenius-norm shell means from radius two to half the sampled side. A dash means fewer than three shells were available. Finite fits depend on the fit window. The tests do not establish an infinite-volume score bound.

## Independent checks

At $a|p|=0.001$ in direction $(1,2,3)$, the two relative covariance slopes are 1.353390 and 1.353466, converging to the common coefficient 1.353553. The file angular.csv checks five directions and three radii. The scripts diagonalize the discrete periodic and open path Laplacians, Fourier transform a two-link real-space impulse, and compare the four-pole resolvent with independent retained/eliminated matrices. For each of 4,676 nonzero coarse momenta, the archive includes both transverse covariance ratios. The 64 pole records cover all eight aliases for axial and diagonal momenta at all four sizes, with zero-overlap aliases identifiable from their residues. At $L=4$ equal lowest energies are combined when reading the long-time pole.

The supplemental Wb one-block values quoted in the master prompt remain literature benchmarks. Their original model discretization was not supplied as part of this exercise. They are separate from the Gaussian block matrices tabulated here.

# Constants and publication evidence

| Constant | Definition or use | Evidence |
|---|---|---|
| $A,A_-,A_+,B,x_*$ | Inverse-coupling decrement and weak interval | Running bounds assumed; $A=11N\log2/(12\pi^2)$ in B2 |
| $c_1,M_c,C_\xi$ | Wilson slope, reciprocal remainder, step error | Kernel evaluated; uniform interacting remainder open |
| $\kappa,c$ | Eliminated gap $\ge\kappa/a$, fibre constant $g^2/c$ | Interacting input W2c.3; $\kappa=c/2$ conditionally |
| $C_S,C_a$ | Uniform retained defect | Open; $1/8$ belongs to the free gap ratio |
| $C_M,C'_a$ | Mixed allowance or signed Schur bound | Raw quadratic estimate obstructed in the free axial sector |
| $C_L,c_{LF},\delta,D_\delta$ | Large fields and exponential absorption | W3 input; explicit $D_\delta$ checked |
| $r,a_w,\bar m$ | Loss cap, last weak spacing, mass ceiling | Positive product conditional on $r<1$ and bounds |
| $A_{int},b,M,g_1$ | Intermediate decrement, step factor, count, threshold | W4 inputs; conditional count checked |
| $z_L,Z_{clock}$ | Strong endpoint and weak time conversion | Strong calibration open; weak product telescopes |

## Verification record

The master local transcript contains 91 proof-axiom records. Public statements and their L1/L2 classifications appear in `scripts/released.tsv`. An L1 proof can have ordinary mathematical hypotheses; L2 identifies an implication consuming a physical estimate or trajectory premise. Shared proofs are counted once. The common prelude separately checks 26 declarations. The Lean kernel audit permits only propext, Classical.choice and Quot.sound. Open predicates are displayed with #check and never entered as proofs.

The archive includes module sources; the combined proof file `packets/W2_final.lean`; the retained local stdout `records/w2-v1/final.local.out`; and the per-module checks. Python executes 9,579 numerical assertions including the original 46 baseline checks, the clock quadrature, the finite Gaussian comparisons and the W2c–W2f diagnostics. Repeated checks at distinct momenta count separately. The official hosted check-only transcript remains outstanding.

## References

R. Cooperman and A.E. Petrunina V.V. *The Physical Clock under Spatial Blocking in SU(N) Lattice Yang–Mills*. First draft, 22 November 2026. DOI 10.5281/zenodo.24446069. In particular Definition 4.1, Lemma 4.2, Proposition 5.1, §§6–9, and Appendix A.

R. Cooperman and A.E. Petrunina V.V. *Weak-Coupling Series Prompt W2*, revision of 21 November 2026, §§1–10. *Amendments to Prompt W2b*, 23 November 2026. The integrated generator retains the supplied series bibliography.

Series dependencies cited by the prompt include *Proving a Uniform Gap Comparison Across Yang–Mills Scales* (DOI 10.5281/zenodo.24348403), *Spectral Comparison Across One Yang–Mills Blocking Step* (DOI 10.5281/zenodo.24365904), and *Two-Coupling One-Loop Matching and the Running Time Unit Under Spatial Blocking in SU(N) Lattice Yang–Mills* (DOI 10.5281/zenodo.24395118).

# License

MIT License

Copyright (c) 2026 Roger Cooperman; A.E. Petrunina V.V.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
