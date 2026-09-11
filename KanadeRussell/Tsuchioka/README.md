# Tsuchioka formalization

The concrete vertex-operator construction, all three admissible-word spanning
bounds, Heisenberg character factorizations, integrability and highest-weight
structure are proved. The actual three characters are evaluated
through the proved root-multiplicity recurrence, denominator equation and G2
sum. [Theorems.lean](../Theorems.lean) supplies `principalCharacterFormulas`,
`standardCharacters`, `lowerBounds`, and the six original KR
targets: three series equalities and their three `HasSum` forms.

The entry point [KanadeRussell.Tsuchioka](../Tsuchioka.lean) collects the
concrete construction and spanning bounds. The representation and q-series
modules evaluate the three concrete characters and combine them with these
bounds in the final KR proof.

The tables below describe the scope of individual components. Each concrete
application discharges the hypotheses of its abstract reduction lemma.

## Source and corrections

The source is Shunsuke Tsuchioka, *A vertex operator reformulation of the Kanade–Russell conjecture modulo 9*, [arXiv:2211.12351v3](https://arxiv.org/abs/2211.12351v3), especially Sections 3–4. Its spanning argument supplies dimension bounds; the character evaluations and rigidity argument complete the KR identities in the separate theorem assembly.

The Lean proofs check two repairs to the source calculation:

- The constant coefficient of `G6 = G4 - (P/Q) G5` is `-1 - 2*w + w^3`. The sign of the cubic term printed in Section 4.3 is incorrect. `Coefficients.c60_corrected` proves the corrected value from the actual ratio, and `f3_coefficient_from_ratios` verifies the resulting F3 coefficient.
- When `A > B` and `(A-B) mod 12 = 7`, the difference of the first operator relations at `(A,B)` and `(A-1,B+1)` cancels the second-root term. `Coefficients.exceptional_cancellation` proves cancellation for all integer indices. `exceptional_ordering_reduction` proves that every other quadratic term is strictly higher and the target coefficient is one, provided the stated finite operator relations hold.

## Three concrete sectors

| Seed | Affine highest weight | Polynomial degree | Admissible minimum |
|---|---|---|---|
| [Degree-one difference](AffineSkewHighestWeight.lean) | `(1,1,0)` | 1 | 1 |
| [Polynomial vacuum](AffineHighestWeight.lean) | `(3,0,0)` | 0 | 2 |
| [Alternating polynomial](AffineAlternatingHighestWeight.lean) | `(0,0,1)` | 3 | 3 |

Each seed is proved nonzero and lies in the positive Heisenberg kernel.
The module grading subtracts the displayed polynomial degree, placing its
highest-weight vector in grade zero. The [vacuum spanning theorem](RootCyclicSpanning.lean)
and [other two spanning bounds](../Sectors/SpanningBounds.lean) bound the
dimension in relative grade `n` by `Partitions.count s n`, where `s` is the
admissible minimum in the table. [ThreeSectorIntegrability.lean](../Representation/ThreeSectorIntegrability.lean)
proves integrability of all three actual tensor cyclic modules.
[ConcreteHeisenbergCharacter.lean](../Representation/ConcreteHeisenbergCharacter.lean)
proves their full-character/vacuum-character factorizations, and
[ConcreteHighestWeight.lean](../Representation/ConcreteHighestWeight.lean)
packages their highest-weight module structure.

## Component map

| File | Mathematical content | Hypotheses that matter |
|---|---|---|
| `Words.lean` | Injectivity of suffix sums; well-foundedness of the higher-word order on highest-weight support; preservation under homogeneous word contexts; exact all-integer classification of the forbidden pairs and triples | The support restriction is essential for well-foundedness; equal total index is essential for a left context |
| `Straightening.lean` | Grading of word values; vanishing when a suffix has positive total index; degree-preserving induction from local reductions to normal-word spanning; finite-dimensional cardinality inequality | An explicitly supplied graded action; the local reductions; for the last inequality, a spanning family |
| `Coefficients.lean` | Twelfth-root polynomial identities; the nonzero F2–F6 coefficients; the exact exceptional residue class; corrected constant coefficient and actual ratios | A characteristic-zero field and a root of `w^4-w^2+1` |
| `Phases.lean` | Integer-power factorization; the actual leading coefficient vanishes exactly in the exceptional class; cancellation in the repaired relation for all integer indices | The same cyclotomic root condition |
| `ExceptionalReduction.lean` | Extraction of the repaired exceptional ordering reduction from two finite skew relations | The two finite relations, with a common second-root coefficient |
| `OrderingReduction.lean` | F1 in every residue class, with the source's actual cyclotomic coefficients | Finite truncations of the first two relations of Theorem 3.2, plus the shifted first relation |
| `PairReductions.lean` | F2 and F3, including the cancellation of the reversed adjacent pair and the corrected nonzero leading coefficient | Finite combined relations and the displayed initial coefficients of G2, G3 and G6 |
| `LocalReduction.lean` | Transport of local reductions into arbitrary word contexts; admissible-word spanning from the six reductions and initial conditions; proof that the endpoint condition imposes the minimum on every index | Local pair/triple reductions on every suffix vector, and the initial reductions |
| `RootData.lean` | The D4 Cartan form, reflections, triality, and twisted Coxeter transformation; preservation of the form; sixth and twelfth powers; derivation of the first-root pairing sequence | An explicit integral root lattice, with the source's node conventions |
| `FormalExponential.lean` | Formal exponential by substitution; finite degreewise cutoff; differential uniqueness; multiplication, finite-sum, inverse, and coefficient-map laws; initial coefficients | Zero constant term of the input series |
| `Fock.lean` | Three-tensor polynomial Fock field by creation and finite annihilation substitution; linear mode operators; local finiteness; exact vacuum values at indices 0, -1, -2 and all positive indices | A characteristic-zero field; explicit creation and annihilation operators |
| `Contractions.lean` | Exact Fourier pairing coefficients; periodicity for all natural indices; nonvanishing exactly in residues 1, 5, 7, 11 modulo 12 | A root of the twelfth cyclotomic polynomial; the pairing sequence is derived from the root lattice |
| `FockGrading.lean` | Weight preservation by the concrete modes; vanishing in negative degrees; a constructed `HighestWeightAction`; the minimum-two initial reduction; finite quadratic tails on every suffix vector | The explicit polynomial Fock action |
| `NormalOrdering.lean` | Concrete creation-annihilation Wick factorization; scalar square/inverse factors for equal/distinct tensor positions; equality with the three-factor creation product; exact first Wick coefficient | All four source operator relations are now proved on the constructed modes |
| `BinomialFactors.lean` | Full rational binomial expansion equals the formal logarithmic exponential; integer-exponent and shift laws; coefficient-map and variable-rescaling laws | A commutative rational algebra; identities in every coefficient |
| `ScalarFactors.lean` | The constructed Wick scalar equals the full twelve-root binomial product and the source's six-factor G1; same/distinct Wick identities use the actual source G1 | The cyclotomic root condition |
| `RationalFactors.lean` | Explicit polynomial numerator and denominator for G1 cubed, including an invertible denominator | Equality in every coefficient |
| `PrimitivePhases.lean` | The polynomial root is a primitive twelfth root; all twelve phases are distinct | A characteristic-zero field |
| `SourceSeries.lean` | Ordinary source H and G1,...,G5; exact rational forms for all eight products G1 squared times Gi and G1 inverse times Gi, for i=2,...,5 | Integer exponent identities |
| `SourceEmbedding.lean` | A ring homomorphism substituting the ratio of the field variables; coefficientwise identification of ordinary source G1 with the actual Fock scalar | Coefficientwise formal-series identities |
| `FormalFourier.lean` | Algebraic geometric and Euler-geometric expansions; bilateral coefficient functions; the second and fifth identities of source Proposition 3.3 for every integer exponent | SourceFourier supplies the other six identities; G1Commutator, G2Anticommutator, and PartialModeRelations supply the four operator identities |
| `SourceCoefficients.lean` | The constant and first coefficients of the actual source G1,...,G6, including the corrected G6 constant term | Derived from the rational binomial definitions and the cyclotomic root condition |
| `SourceReductions.lean` | F2/F3 instantiated with the proved source-series coefficients | ConcretePairs now discharges these finite-relation hypotheses for the constructed modes |
| `ScalarPhases.lean` | Exact polynomial representatives and inverses of all twelve source phases | The cyclotomic root condition |
| `PartialFractionCertificates.lean` | Seven exact polynomial identities for the partial fractions, including the first-root commutator | Generated certificates checked by Lean in an arbitrary commutative ring |
| `PartialFractions.lean` | Complete geometric-series expansions of all six remaining normalized products in Proposition 3.3 | Explicit unit denominators; identities of full formal series |
| `FourierSymmetry.lean` and `FourierAssembly.lean` | Reciprocal-pair Fourier formulas and linear assembly, including the necessary constant-coefficient condition | Bilateral coefficient functions at every integer exponent |
| `SourceFourier.lean` | The other six Fourier identities of Proposition 3.3, with the source phases and constants | The cyclotomic root hypothesis |
| `CombinedFourier.lean` | Both Fourier identities for the actual G6 combination, with the sign used in Section 3.6 | The proved nonvanishing of Q |
| `CommutatorScalar.lean` | G1 cubed and its full Fourier expansion; the two residues printed in Section 3.4 and the central Euler-delta coefficient | G1Commutator now derives the actual operator identity using the proved summed Euler residue |
| `RootFunctional.lean` | An explicit Coxeter eigenfunctional on the D4 lattice and the four root-addition identities at the noncentral commutator poles | Derived from the integral Coxeter action |
| `RootFock.lean` | Root-dependent creation and annihilation operators, including the second-root field; equality of the first-root specialization with the existing Fock operators | Constructed polynomial operators; affine-module structure is developed in the subsequent Representation modules |
| `RootCovariance.lean` | Primitive phases on the Heisenberg modes, covariance of the creation exponential, and its four pole-fusion identities | Creation-part identities; PoleFusion supplies the full normal-product fusion |
| `LaurentRescaling.lean` | Laurent-variable rescaling by units as a ring homomorphism, with unchanged support and compatibility with power series | Every integer coefficient, including negative exponents |
| `AnnihilationCovariance.lean` | Coxeter covariance of the concrete annihilation substitutions, complete root fields, and every integer mode | The cyclotomic root condition and explicit annihilation substitutions |
| `PoleFusion.lean` | Full normal-ordered specializations at the four noncentral commutator poles; the central-pole specialization is the identity | Both creation factors and both finite annihilation shifts are included on arbitrary polynomial inputs |
| `JointAnnihilation.lean` | A universal polynomial in two inverse field variables; its Laurent embedding equals the composition of annihilation maps, and its pole evaluation equals the substitution in PoleFusion | Evaluation of the finite polynomial at each pole |
| `TwoFields.lean` | Exact Wick normal ordering of actual sequential tensor operators with the source G1 factors; coefficient interpretation as mode composition; normalized complete-field sum with factor 1/144 | One iterated Laurent expansion; RatioContraction now compares coefficients of the opposite expansions |
| `TwoVariableSupport.lean` | Separate lower bounds on the exponents of the actual normal product, and finite support of every fixed-total-exponent contraction | Proved for every input polynomial from the finite annihilation representation |
| `DeltaContraction.lean` | Finite bilateral scalar contractions; exact delta evaluation and Euler-delta evaluation with the inner derivative term retained | A proved separate lower bound, instantiated by the normal product |
| `DiagonalEvaluation.lean` | Laurent convolution as a finite sum; diagonal evaluation of separated factors and arbitrary monomial shifts | Finite Laurent convolution of separated factors |
| `NormalProductEvaluation.lean` | Equality of coefficientwise diagonal evaluation with the concrete full pole-normal product; actual delta residues | All polynomial annihilation inputs and every total exponent |
| `ModeResidues.lean` | The four noncentral delta residues as first- and second-root modes, with the source phases and normalization 1/12 | The root-addition premises of the common lemma are discharged in all four applications |
| `NormalProductSymmetry.lean` | Coefficientwise symmetry under exchange of variables and tensor positions | Exchange symmetry of the finite inverse-variable polynomial |
| `RatioContraction.lean` | Coefficient extraction for actual ratio-series multiplication; finite support; comparison of forward/reverse expansions with symmetric and antisymmetric Fourier kernels | Scalar kernels are coefficient functions, and every contraction used is finite |
| `WeightedFields.lean` | Weighted sequential fields reduce to the actual source G1 squared/inverse Fourier kernels; weighted full-field coefficients are finite quadratic mode convolutions | All four relations are assembled from these kernels, including the total-mode restriction in G3/G6 |
| `ScalarContraction.lean` | Finite scalar contractions are linear in their bilateral coefficient kernel | Separate lower bounds for the contracted normal product |
| `MixedPole.lean` | At ratio 1, two distinct tensor positions fuse to the negative-root field on their complementary position; the six ordered pairs give twice the complete tensor sum | All polynomial inputs; the three tensor exponents sum to zero |
| `CentralDelta.lean` | The ratio -1 delta residue is the identity with the source sign and normalization; negative-root modes have phase (-1)^i | Pure delta evaluation; CentralEuler now proves the summed Euler derivative cancellation |
| `ResidueMaps.lean` | Same-position and mixed-position contractions as linear maps; all six pole evaluations needed by G2 with source phases | The cyclotomic root condition and constructed contraction maps |
| `OperatorKernels.lean` | Full symmetric and skew mode convolutions split into the two source Fourier kernels | Proved for actual sequential operators; each convolution has finite support |
| `G2Anticommutator.lean` | The complete second relation of Theorem 3.2, including both root families, the central term, and the mixed-position term | Constructed Fock modes on every polynomial input; representation structure is developed in the subsequent Representation modules |
| `FiniteModeRelations.lean` | Finite natural-index symmetric and skew sums on suffix vectors; the actual G2 relation for every sufficiently large finite cutoff | Cutoffs are obtained from the proved grading and pair-tail vanishing |
| `EulerDiagonal.lean` | Laurent Euler coefficients, separated-factor evaluation, and the exact extra weight under an inverse-monomial shift | All diagonal sums are finite by the established separate lower bounds |
| `EulerPolynomial.lean` | Full Euler evaluation of a normal product, with the negative derivative of its first inverse variable | Polynomial induction retains both creation and annihilation derivative terms |
| `CentralCreationEuler.lean` | The sum of the creation logarithms is zero; central creation fusion reduces the summed derivative to this identity | Cancellation is proved after summing all three tensor positions |
| `CentralAnnihilationEuler.lean` | Central evaluation of the annihilation substitution is the identity; the summed inverse-variable derivative vanishes on every polynomial | The product rule and zero sum on each generator supply the full polynomial proof |
| `CentralEuler.lean` | The summed inner Euler derivative is zero, and the normalized Euler-delta residue is A*(-1)^A/48 in total mode zero | Each derivative is retained until the tensor sum is taken |
| `G1Commutator.lean` | The complete first relation of Theorem 3.2 and its finite natural-index form on every word suffix | Constructed modes with the actual source G1 coefficients |
| `ConcreteOrdering.lean` | F1 on every suffix vector, including the exceptional residue class, from the proved G1/G2 relations and the shifted G1 relation | The cyclotomic root condition; the F1 relation hypotheses are discharged |
| `MixedPhase.lean` | Exact cyclic phase identity for ratios w^2 and w^(-2) on every allowed oscillator mode | The cyclotomic root condition and zero sum of the tensor exponents |
| `MixedCreationCycle.lean` | Cyclic covariance of the full mixed creation exponential | Equality in every coefficient, obtained from the logarithm |
| `MixedPoleCycle.lean` | Cyclic covariance of mixed annihilation substitutions and full pole-normal products on every polynomial input | Both creation and annihilation factors are included |
| `MixedPoleSupport.lean` | The six-term mixed pole sum is invariant under the cyclic rescaling, and its coefficients vanish outside degrees divisible by 3 | Both mixed poles; all integer degrees |
| `MixedResidueVanishing.lean` | The normalized mixed residues at w^2 and w^(-2) vanish when 3 does not divide A+B | The mode restriction is explicit |
| `PartialModeRelations.lean` | Complete G3 anticommutator and G6 commutator, and their finite natural-index forms on every suffix | Constructed modes; exactly the source restriction that 3 does not divide A+B |
| `ConcretePairs.lean` | Concrete F2/F3 and the resulting reduction for every forbidden pair | All finite operator-relation hypotheses are discharged; F1 is imported from ConcreteOrdering |
| `SecondRootCoefficient.lean` | The second-root G2 coefficient is nonzero for equal or consecutive indices; these cover every total integer mode | Exact cyclotomic inverse certificates |
| `SecondRootElimination.lean` | Pointwise second-root elimination; first-root-stable subspaces and graded families are second-root-stable | All quadratic convolutions have proved finite support |
| `RootGeneration.lean` | A second-root mode is in the span of first-root words of length at most two with the same total index; both root families generate exactly the first-root homogeneous span from every polynomial seed | The concrete G2 relation and second-root elimination |
| `RootCyclicSpanning.lean` | Admissible minimum-two words span the cyclic space of all 24 root modes on the triple vacuum; each degree is finite-dimensional and bounded by the corresponding partition count | Uses the concrete F1-F6 proofs in [Straightening/FockPairs.lean](../Straightening/FockPairs.lean) |
| `RootOrbits.lean` | Every norm-two D4 lattice vector lies in exactly one of two length-twelve Coxeter orbits; an explicit equivalence proves that there are 24 roots | Exhaustiveness follows from proved orthogonal-coordinate bounds for arbitrary integral vectors |
| `AllRootGeneration.lean` | Uniform mode covariance to the two representatives; elimination, grading, and homogeneous cyclic generation for every root | The proved orbit classification |
| `DegreeOperator.lean` | The concrete monomial degree operator E, its grading eigenvalues, and [E,Z_i]=-i Z_i for every root; d=-E has the affine sign | The operator is constructed on the polynomial space and the identities hold on all inputs |
| `ZCyclicGeneration.lean` | The algebra generated by all root modes, c=3 Id, and d has the same cyclic span as the first-root family on a homogeneous seed | Finite elimination on each polynomial input |
| `ZCyclicGrading.lean` | Homogeneous projection identifies the true degree slices of the full concrete cyclic algebra action; the triple-vacuum slices are finite-dimensional and bounded by the minimum-two partition count | The slice is the intersection with the polynomial degree subspace |
| `CoefficientDerivations.lean` | Coefficientwise Laurent derivations satisfy the product rule, and derivations killing a creation logarithm kill its full formal exponential | Every convolution and exponential coefficient uses a proved finite sum |
| `DiagonalDerivations.lean` | The sum of the three partial derivatives kills every root creation field and commutes with every root annihilation substitution and root mode | Arbitrary lattice elements and arbitrary polynomial inputs |
| `DegreeDerivation.lean` | The energy operator satisfies the polynomial product rule; diagonal derivatives commute and obey their degree commutator | The previously constructed degree operator is used |
| `DiagonalHeisenberg.lean` | Source-normalized positive and negative diagonal Heisenberg operators, level-three brackets, the common positive-mode kernel, and invariance under root modes and energy | Nonzero Fourier pairings identify the kernel with the common diagonal-derivative kernel |
| `HeisenbergCyclicSpace.lean` | Root modes also commute with the negative Heisenberg operators; the full concrete Z algebra preserves the vacuum, and its cyclic spaces from vacuum seeds lie in that kernel | Inclusion in the full triple-Fock vacuum |
| `PolynomialDerivativeKernel.lean` | In characteristic zero a partial derivative vanishes exactly when its variable is absent; deleting such variables fixes the polynomial | Proved coefficientwise for arbitrary polynomials |
| `VacuumCoordinates.lean` | An explicit idempotent relative-coordinate projection has image exactly the full diagonal Heisenberg vacuum | The proof conjugates diagonal differentiation to ordinary partial differentiation |
| `VacuumPolynomialModel.lean` | A polynomial ring in two independent oscillator families is linearly equivalent to the full triple-Fock Heisenberg vacuum | An explicit embedding and extraction prove both generation and independence |
| `VacuumProjection.lean` | The centered projection kills every diagonal creation variable and fixes the full Heisenberg vacuum | This is the projection along the actual negative Heisenberg variables |
| `HeisenbergSpanning.lean` | Finite negative-Heisenberg-word spans are stable under the required operators; their intersection with the vacuum is precisely the starting vacuum subspace | Arbitrary vacuum subspaces |
| `OscillatorCyclicity.lean` | The cyclic action generated by Heisenberg operators, all root Z modes, c, and d is the negative-Heisenberg span of its Z-cyclic space; its vacuum equals that Z-cyclic space | The combined concrete action is defined explicitly; its minimum-two vacuum degree bound is inherited from the proved spanning theorem |
| `TensorRootFields.lean` | The source basic-representation tensor fields are constructed with trivial lattice character; X=DZ and Z=D^(-1)X hold as full Laurent-field identities on all vacuum inputs | The diagonal creation logarithm, inverse exponential, and annihilation agreement are proved, with local finiteness of every root mode |
| `TensorHeisenberg.lean` | Tensor root fields obey the negative Heisenberg commutator, with the exact all-integer shift i-n | The explicit tensor fields and Heisenberg action |
| `DressingCoefficients.lean` | Both dressing factors have coefficients in the diagonal creation algebra; finite Laurent convolution preserves negative-Heisenberg-stable subspaces | Every polynomial input and every coefficient |
| `ModeDressing.lean` | Tensor and Z mode stability transfer in both directions on vacuum inputs; tensor modes preserve negative-Heisenberg spans of Z-stable vacuum spaces | The proved dressing identities and finite convolution |
| `TensorCyclicity.lean` | The source tensor cyclic space equals the negative-Heisenberg span of the Z-cyclic space; its vacuum is exactly the Z-cyclic space, with the minimum-two grade bound | Any vacuum seed for the space equality; the triple vacuum for the minimum-two bound |
| `ExponentialDerivation.lean` | The coefficientwise derivation chain rule for formal exponentials, proved by finite products and formal differential uniqueness | A rational coefficient algebra and zero constant term of the exponent |
| `PositiveTensorHeisenberg.lean` | The positive Heisenberg commutator of each source tensor root mode; both signs packaged as endomorphism identities | Every lattice vector, every integer root-mode index, and every allowed positive Heisenberg mode |
| `TensorGrading.lean` | Principal grading of the tensor fields, positive root-mode annihilation of the triple vacuum, and the derivation brackets with tensor roots and both Heisenberg halves | Constructed polynomial operators |
| `ProjectedRootPairing.lean` | The exact Fourier projection of the D4 Cartan pairing gives both source Heisenberg-root commutator coefficients | Polynomial identities on arbitrary lattice inputs, then all positive and negative allowed mode indices |
| `TensorNormalOrdering.lean` | Actual Wick factorization for arbitrary tensor root pairs; equal positions give G1 cubed for the first root, distinct positions give scalar one | Exact creation and annihilation operators on every polynomial input |
| `TensorJointAnnihilation.lean` | A finite two-variable polynomial represents tensor annihilation; separate Laurent bounds, exchange symmetry, diagonal evaluation, and commutation in distinct tensor positions | Every lattice pair and every integer mode index; finite polynomial evaluation |
| `TensorCommutatorKernel.lean` | The actual normalized tensor first-root commutator equals the finite contraction with the source four-pole and central Euler-delta kernel | Distinct positions cancel; TensorFirstRootCommutator now evaluates every residue |
| `TensorCovariance.lean` | Coxeter covariance of tensor creation, annihilation, fields, and modes; zero-root specialization | Every lattice vector, polynomial input, and integer mode |
| `TensorPoleFusion.lean` | Full same-position pole fusion and diagonal evaluation for tensor normal products | The finite inverse-variable polynomial supplies the actual annihilation specialization |
| `TensorModeResidues.lean` | The four noncentral tensor residues are first- and second-root modes with their exact phases | All integer indices and every polynomial input |
| `TensorCentralAnnihilationEuler.lean` | Central inverse-variable differentiation is an explicitly constructed polynomial derivation; its sum gives positive Heisenberg modes | Polynomial induction and the product rule |
| `TensorCentralCreationEuler.lean` | The central creation derivative reduces to the Euler derivative of the logarithm; its sum gives negative Heisenberg modes | Coefficients outside allowed oscillator degrees vanish |
| `TensorCentralEuler.lean` | The summed central Euler coefficient in every integer degree d is -12 times the Heisenberg mode with index -d | Both signs and absent oscillator degrees are proved |
| `TensorResidueMaps.lean` | All tensor delta residues and the complete normalized central Euler residue | The Heisenberg term is retained in every degree, with the central scalar in total mode zero |
| `TensorFirstRootCommutator.lean` | The complete actual first-root tensor commutator, with first-root, second-root, Heisenberg, and level-three central terms | The mixed bracket is proved in TensorMixedRootCommutator; TensorSecondRootCommutator supplies the second-root self bracket; affine-module structure is developed in the subsequent Representation modules |
| `OrbitPairingFactorization.lean` | The full orbit Fourier polynomial factors into the two Coxeter weights and the first-root pairing polynomial | Every twelfth root and arbitrary integral lattice inputs; exact bilinear polynomial certificate |
| `TensorScalarFactors.lean` | The arbitrary-root tensor Wick exponential equals the product with integer Cartan-pairing exponents | Every coefficient, including absent oscillator modes |
| `TensorRootScalars.lean` | Ordinary rational scalar series for all lattice pairs, their ratio embeddings, and unit polynomial denominators | The mixed and second-root exponent lists are derived from the lattice |
| `TensorAllRootKernel.lean` | Every actual tensor root commutator is a finite contraction of its forward and reverse rational scalar expansions | Both ordered lattice pairs and all integer indices |
| `MixedRootScalarCertificates.lean` | Exact polynomial certificates for the two mixed-root partial fractions | Checked in an arbitrary commutative ring from the cyclotomic equation and geometric denominators |
| `MixedRootScalarExpansion.lean` | Complete mixed-root scalar expansions and their four-pole Fourier identity | Every integer coefficient, including the zero coefficient |
| `TensorPairResidues.lean` | Linear finite residue maps and pole-fusion coefficients for arbitrary tensor root pairs | Every claimed fusion uses a proved lattice equality |
| `TensorMixedRootCommutator.lean` | The complete mixed first/second-root tensor commutator as an explicit sum of the two root families | The four proved lattice fusions |
| `TensorRootCentralAnnihilation.lean` | Arbitrary-root central annihilation derivatives scale the first-root coefficient derivation by the Coxeter weight | Polynomial induction and the actual oscillator shifts |
| `TensorRootCentralEuler.lean` | Both creation and annihilation central derivatives have the same degreewise root weight; their sum is the projected Heisenberg mode | Every lattice root and every integer Laurent degree |
| `TensorRootCentralResidues.lean` | The complete normalized central delta and Euler residues for every tensor root self pair | Root-weighted Heisenberg term and level-three scalar are both retained |
| `SecondRootScalarExpansion.lean` | The second-root scalar equals G1 cubed with w replaced by -w; its complete four-pole and central Fourier kernel | Derived from the actual Cartan exponents and unit-denominator identities |
| `TensorSecondRootCommutator.lean` | The complete actual second-root self bracket with both root families, projected Heisenberg term, and centre | All four lattice fusions and every integer index are proved |
| `TensorModeBrackets.lean` | All three root-family brackets as endomorphism identities; all-integer Heisenberg-root, Heisenberg-central, and derivation brackets | The same concrete Fock operators and cyclotomic root condition |
| `TensorLieCoordinates.lean` | Four-coordinate structure constants and a proved evaluation map taking every coordinate bracket to the actual operator bracket | Absent Heisenberg degrees are explicitly normalized to zero |
| `CyclotomicPhaseReduction.lean` | Degree-three polynomial representatives of every integer phase | The reduction holds for every integer exponent |
| `SerreUniversal.lean` | A system satisfying all six Serre relation families defines a Lie homomorphism from mathlib's integer-matrix Serre quotient | A general universal property; AffineChevalley discharges its hypotheses concretely |
| `ChevalleyCoefficients.lean` | Explicit E, F, and H coordinates for the source D4^(3) Cartan matrix; every HH, HE, HF, and EF coefficient identity | Exact characteristic-zero polynomial identities, checked by Lean |
| `ChevalleySerreCoefficients.lean` | All 24 successive coordinate identities needed for the positive and negative Serre families | The intermediate polynomial identities are proved |
| `TensorCoordinateIteration.lean` | Coordinate iteration evaluates to powers of the actual adjoint operator | An induction for every natural iteration count |
| `AffineChevalley.lean` | A Lie algebra homomorphism from the source Cartan matrix's Serre quotient to the concrete tensor endomorphisms, with explicit generator evaluations | All six defining relation families are proved |
| `TensorVacuumWeights.lean` | Every root zero mode acts on the polynomial vacuum by 1/4; positive Heisenberg modes annihilate it | Exact actions of the constructed operators |
| `AffineHighestWeight.lean` | The vacuum is a nonzero highest-weight vector of weight (3,0,0); dual marks (1,2,3) give scalar level three; its principal degree is zero | Highest-weight conditions for the concrete vacuum |
| `TensorLieDerivation.lean` and `AffinePrincipalDegree.lean` | Principal-derivation brackets for arbitrary coordinates and for E, F, H, with degrees +1, -1, 0 | The central coordinate has degree zero |

The local higher-word spans explicitly retain the total index. Thus the ordering reduction has the homogeneity required by the spanning induction. The induction discards nonsurviving words by a proved grading argument and uses finite linear combinations in the algebraic span.

The Fock field uses the formal variable `t = zeta^(-1)`. Its mode `i` is the Laurent coefficient at `-i`. Creation is a formal exponential with a proved finite coefficient formula; annihilation is a polynomial substitution, so the field is an actual Laurent series on each input polynomial. Grading is proved for arbitrary inputs of fixed weight, then used to instantiate the abstract highest-weight action. In particular, Lean proves `Z_i 1 = 0` for `i > 0`, `Z_0 1 = 1/4`, `Z_(-1) 1 = 0`, and an explicit nonzero quadratic formula for `Z_(-2) 1`. The scalar at index zero is retained as a shorter-word reduction.

This construction follows the normal-ordered tensor formula in Section 3.5 and establishes the polynomial action. The three explicit highest-weight seeds and their concrete spanning statements are listed above. The chosen Heisenberg residue classes have the correct nonzero Fourier pairings. The subsequent Representation modules establish the actual cyclic modules and evaluate their characters; the final assembly is in `KanadeRussell/Theorems.lean`.

The normal-ordering calculation is now proved directly from these operators, in power series with Laurent-series coefficients. Applying annihilation to a creation exponential gives the original exponential times an explicit scalar factor. The tensor pairing is 6 on equal positions and -3 on distinct positions, producing the square and inverse scalar factors in Section 3.5. The combined creation exponential is proved equal to the product of the three tensor-factor exponentials. Its scalar factor has the source's first coefficient `(-6 - 4*w + 2*w^3)/3`. The whole scalar series is now identified with the source's binomial product. This follows from the full formal binomial theorem and the actual twelve-root pairing sequence. An explicit ring homomorphism embeds the ordinary source variable as the ratio of the field variables, and its coefficient formula identifies all source coefficients with the concrete Fock scalar coefficients.

All eight Fourier identities in Proposition 3.3 are now proved for every integer exponent. The proof first identifies each normalized product with an explicit rational expression, verifies its polynomial partial-fraction identity, and then extracts its bilateral coefficients from geometric and Euler-geometric series. The constant terms are checked as part of the symmetric formulas. Bilateral distributions are represented by coefficient functions.

The two G6 combinations are also proved directly from `G6 = G4 - (P/Q) G5`. In particular, its distinct-position identity has `(P/3) (delta(w^(-2) x) - delta(w^2 x))`, with the sign used in Section 3.6. The full scalar identity for the first generalized commutator is proved as well: the G1-cubed residues are `P` and `-52 + 104*w^2 + 90*w^3` at the source phases, and its central coefficient is `84 + 96*w - 48*w^3`. WeightedFields now connects these scalar kernels with actual sequential operators. All four relations of Theorem 3.2 are assembled on the concrete modes. For the partial G3/G6 relations, the mixed-position pole sum at each of w^2 and w^(-2) is proved invariant under a rescaling that cycles the tensor positions. Its coefficient in a degree not divisible by 3 therefore vanishes. This proves precisely the restriction on A+B stated in the source.

The second-root field is constructed on the same polynomial Fock space. Its coefficients use an explicit lattice functional satisfying Coxeter covariance, and the first-root specialization is proved equal to the original field. Covariance is now proved for the annihilation substitutions, complete fields, and every integer mode. The full normal-ordered specializations at the four noncentral poles follow from checked root additions, including the two sums that produce the second root. At the central pole the normal product is the identity on every polynomial input.

The two annihilation shifts are also represented by one polynomial in the two inverse field variables. Its iterated Laurent embedding is proved equal to the composition of the original annihilation maps; evaluating the polynomial at a pole gives the substitution used in the fusion theorem. The actual sequential tensor operators now have a proved normal-ordering formula in iterated Laurent series, with the complete source G1 squared or inverse factor. Extracting the inner and outer coefficients gives actual mode composition, and the full-field double sum has the checked factor 1/144. Separate lower bounds in the two variables are now proved for this normal product on every polynomial input. They make each diagonal contraction a finite sum over an explicit interval. The delta and Euler-delta evaluation formulas are proved coefficientwise, with the inner derivative term retained in the latter. Diagonal evaluation is identified with the concrete pole-normal product, and the four noncentral residues reduce to the actual first- and second-root modes with the source phases and normalization 1/12. The central delta and the mixed-position contraction at ratio 1 are now evaluated. The summed Euler derivative contribution is now proved to vanish: the creation contribution reduces to the zero sum of the three creation logarithms, and the annihilation contribution is a derivation that vanishes after summing its values on each polynomial generator. For the Euler-delta calculation in Section 3.6, each individual derivative is retained until the tensor sum is taken. Cancellation is proved for that sum.

The common normal product is now proved symmetric under simultaneous exchange of variables and tensor positions. Multiplication by the source ratio series is identified with finite coefficientwise convolution. This proves comparison of the forward and reversed expansions against the symmetric and antisymmetric Fourier kernels. Weighted sequential operators reduce to the source G1 squared or inverse kernels, and the normalized complete-field coefficient is the quadratic mode convolution. A separate theorem proves finite support, so the convolution is a finite sum.

The complete G2 anticommutator now follows from these constructed operators. The same-position Fourier kernel gives the four noncentral mode terms and the central delta. At ratio 1, each ordered pair of distinct tensor positions has a complementary position, and its full normal product is the negative-root field there. Summing the six pairs gives the remaining `(-1)^(A+B)/3` mode term. A separate finite-sum theorem proves the same G2 identity in the exact natural-index form used by the straightening lemmas, on every word suffix and at every sufficiently large cutoff.

The first generalized commutator is now proved on every polynomial input. Its central Euler-delta term uses the checked summed derivative cancellation, with normalization `A*(-1)^A/48` before multiplication by the scalar Fourier coefficient. Both G1 and G2 have finite natural-index versions on every suffix vector. These discharge the hypotheses of the F1 ordering argument, including the exceptional class where the shifted G1 relation is required. These relations prove `Fock.local_ordering_reduction` for the concrete operators. The finite G3/G6 relations now also discharge the F2/F3 hypotheses: the G2 minus (T/M) G3 combination eliminates the second-root term, and G6 cancels the reversed adjacent pair. `Fock.local_pair_reduction` proves the local reduction for every forbidden pair.

The `Straightening` modules normalize the source pair relations modulo strictly shorter words and prove the F4-F6 overlap reductions. All six local reductions and the minimum-two initial condition are instantiated in `Straightening/FockPairs.lean`. Thus the first-root cyclic grade on the triple vacuum is spanned by the minimum-two admissible words, with a proved finite-dimensional bound by `Partitions.count 2 n`.

Section 4.1's second-root elimination is now proved for the constructed operators. For an arbitrary total index, the G2 relation is specialized to equal or consecutive indices. Its second-root coefficient is proved nonzero, so each second-root mode on a polynomial input is a finite linear combination of first-root words of length at most two and the same total index. Consequently, the two-root and first-root cyclic spans agree in every total index, for any polynomial seed. On the triple vacuum this transfers the minimum-two admissible spanning theorem and dimension bound to the two-root cyclic span. The equality here concerns the two concrete cyclic spans. The representation modules supply the module identifications used in the final assembly.

The two chosen roots now cover every root in the concrete D4 lattice. The Cartan norm is written as a sum of four squares in orthogonal coordinates. Norm two forces each coordinate to lie between -1 and 1, and the resulting exhaustive proof places every root in one of the two length-twelve Coxeter orbits. The two length-twelve orbits partition the 24 roots. Full mode covariance therefore extends the elimination and homogeneous generation statements to all 24 roots.

The degree operator E is constructed diagonally on the polynomial monomial basis. Its commutator with the mode of any root is -i times that mode, so the source-sign affine derivation is d=-E. For every homogeneous polynomial seed, the subalgebra generated by all root modes, the level-three scalar c, and d has exactly the first-root cyclic span. The equality of cyclic spans uses finite elimination on each polynomial input. Weighted homogeneous projection further identifies each actual degree slice of this cyclic space with its fixed-total-index word span. On the triple vacuum, that slice has the established minimum-two admissible spanning and dimension bound.

The diagonal Heisenberg action is now constructed on the polynomial space with the source normalization: beta_1(n) is (n*kappa_n/12) times the sum of the three partial derivatives, and beta_1(-n) is multiplication by the sum of the three variables. Its mixed bracket is (n*kappa_n/12) times the level-three scalar, and the same-sign brackets vanish. Every lattice-root mode commutes with both Heisenberg halves. The degree operator preserves the positive-mode kernel, so the full concrete Z algebra preserves that kernel and its cyclic span from a vacuum seed is contained there.

The full triple-Fock Heisenberg vacuum now has an explicit polynomial model. The substitution x_(i,n) -> x_(i,n)-x_(0,n) is an idempotent projection onto the common positive-mode kernel. A triangular coordinate change converts the diagonal derivative into an ordinary partial derivative; a characteristic-zero coefficient argument proves that zero partial derivative means the reference variable is absent. The remaining differences x_(1,n)-x_(0,n) and x_(2,n)-x_(0,n) are independent, as proved by an explicit extraction map. This describes the full triple-Fock vacuum. The next cyclicity result describes the vacuum inside the cyclic space generated by a chosen seed.

Vacuum cyclicity is now proved for the combined concrete oscillator--Z action. The centered substitution x_(i,n) -> x_(i,n)-(x_(0,n)+x_(1,n)+x_(2,n))/3 kills every diagonal creation variable and fixes every vacuum vector. For any vacuum subspace S, its finite negative-Heisenberg-word span intersects the vacuum exactly in S. Moving a positive Heisenberg mode through those words uses the proved level-three commutator, and root-mode and degree stability follow from their proved commutators. Consequently the combined cyclic space from any vacuum seed has exactly the Z-cyclic space as its vacuum. For the triple-vacuum seed this transfers the minimum-two degree bound to the actual vacuum intersection of the combined cyclic action.

The tensor root fields X are now constructed from the source's basic-representation formula with trivial lattice character. In tensor position j, their creation logarithm has coefficient 12*rootWeight(w^(-n),beta)*x_(j,n)/n, and their annihilation shifts only that tensor factor by -kappa_n*rootWeight(w^n,beta). The creation logarithm is the sum of the diagonal logarithm and the existing Z creation logarithm. The two annihilation substitutions agree on every vacuum polynomial because they agree on all relative coordinate differences. This proves both X=DZ and Z=D^(-1)X as full Laurent-field identities on vacuum inputs. The tensor root modes also satisfy the negative Heisenberg commutator with shift i-n. Every coefficient of both dressing factors lies in the algebra generated by the diagonal creation variables. The Laurent convolutions are finite on each input. This proves that, from any vacuum seed, the source tensor cyclic space is exactly the negative-Heisenberg span of the Z-cyclic space. Its vacuum intersection is therefore precisely the Z-cyclic space, and the minimum-two degree bound applies to this actual tensor cyclic vacuum. The Serre-presentation action is proved below; the subsequent representation and character arguments are assembled in `KanadeRussell/Theorems.lean`.

The positive tensor Heisenberg bracket is now derived from the coefficientwise exponential chain rule. The creation derivative is a single formal monomial, while the annihilation substitution commutes with the diagonal derivative. Coefficient extraction gives the shift i+n, complementing the already proved negative shift i-n. An exact Fourier calculation of the actual D4 Cartan pairing identifies both scalar coefficients with the source projected-root pairings for every lattice vector. The tensor modes preserve the principal grading, positive modes annihilate the triple vacuum, and d has the prescribed brackets with tensor root modes and both Heisenberg halves. These are checked parts of the affine relations. All three brackets between the two root families are proved below; the subsequent Representation modules establish the actual module structure.

The tensor first-root commutator now has an exact finite Fourier-contraction formula. Wick normal ordering gives G1 cubed for equal tensor positions and scalar one for distinct positions. A finite polynomial in the two inverse variables represents all annihilation substitutions, proving separate lower bounds and exchange symmetry. Modes in distinct positions therefore commute, leaving three equal-position terms with normalization 1/144. The existing complete G1-cubed Fourier identity supplies the four noncentral delta poles and central Euler-delta kernel. All these tensor residues are now evaluated. The four noncentral poles give the first- and second-root modes. The central derivative gives -12 times the Heisenberg mode in the corresponding degree, and the Euler-delta contribution also supplies the level-three central scalar in total mode zero. This proves the full first-root self bracket on every polynomial input. The mixed first/second-root bracket is now also proved. Its four simple poles fuse to two first-root and two second-root modes, with the exact phases and normalization. For arbitrary lattice pairs, the Wick factor and its finite rational commutator kernel are proved. The second-root self bracket is now proved as well: its scalar is G1 cubed with w replaced by -w, its four noncentral poles give the two root families, and its central Euler residue supplies the second-root projected Heisenberg weight. This completes all three brackets between the two root families on arbitrary polynomial inputs.

The concrete tensor operators now give a representation of the Serre presentation for the matrix `[2,-1,0; -1,2,-3; 0,-1,2]`. Each Chevalley E is an explicit linear combination of the two root modes and the Heisenberg mode in degree +1; each F uses degree -1; each H combines the two root zero modes and the identity. The proved coordinate evaluation identifies all six Serre families with identities of actual polynomial operators. The universal property then constructs `affineTensorRepresentation`, with proved evaluations on each generator. Its dual-mark central element acts by three, the polynomial vacuum has weight (3,0,0), and the principal derivation has brackets +E, -F, and zero with H. This is an affine highest-weight action. The subsequent Representation modules identify its Chevalley cyclic subspace with the tensor cyclic space, prove the required highest-weight structure and evaluate the actual characters. These results are assembled in `KanadeRussell/Theorems.lean`.

The polynomial generator produces certificates, which Lean verifies as `ring` and `linear_combination` proofs. The finite twelve-case calculation exhausts the residue classes of `A-B`. `Phases.lean` extends these identities to arbitrary integer indices.

## Final assembly and verification

The three concrete character applications and `LowerBounds` are proved in
[Theorems.lean](../Theorems.lean), which then proves the original series
equalities and `HasSum` statements.

The main targets of the active [Comparator challenge](../../Comparator/README.md)
are the three original KR identities in `HasSum` form. Three auxiliary checks
verify the degree 0–2 product coefficients. These statements are in
[Challenge.lean](../../Challenge.lean),
with proofs in [Solution.lean](../../Solution.lean). The local checker compiles
those proofs and audits their transitive axioms; the Linux workflow is configured to run
`leanprover/comparator` with the independent statement file.

## Reproduce

Run these commands from the repository root:

```sh
python scripts/check-comparator.py
python scripts/test_check_comparator.py
python scripts/audit-axioms.py
```

The comparator checker builds the library and verifies the six challenge
statements and their transitive axioms. The test suite checks the verifier's
failure cases and dependency rebuilds. The public axiom audit includes the
Tsuchioka declarations listed in [AxiomAudit.lean](../AxiomAudit.lean), allowing
only `propext`, `Classical.choice`, and `Quot.sound`.
