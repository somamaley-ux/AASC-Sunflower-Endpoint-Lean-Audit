import SunflowerAASC.V2.FixedIdentityPopulation
import SunflowerAASC.V2.HighRankPopulationInheritance
import SunflowerAASC.V2.MechanizedKernelImport

namespace SunflowerAASC
namespace V2
namespace ManuscriptKernelTransfer

open ConstraintMapPopulation
open FixedIdentityPopulation
open HighRankPopulationInheritance
open InternalTensorProfiles
open PopulationInheritance
open MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction

/--
The source-neutral antecedent used by the manuscript's kernel import.  Its four
fields are exactly target determinacy, step evaluability, act-time finality, and
same-regime fidelity; they are not new sunflower-specific assumptions.
-/
structure NeutralEndpointAdequacy
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch) : Prop where
  targetDeterminacy : endpointUse.targetFixed /\ endpointUse.carrierFixed
  stepEvaluability : endpointUse.branchRoleFixed /\ endpointUse.reportable
  actTimeFinality : endpointUse.lawfulActTimeBoundary
  sameRegimeFidelity : endpointUse.downstreamReusable

/-- Every live local endpoint use supplies the neutral adequacy antecedent. -/
theorem NeutralEndpointAdequacy.ofLocalEndpointUse
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch) :
    NeutralEndpointAdequacy endpointUse where
  targetDeterminacy :=
    And.intro endpointUse.targetFixed_holds endpointUse.carrierFixed_holds
  stepEvaluability :=
    And.intro endpointUse.branchRoleFixed_holds endpointUse.reportable_holds
  actTimeFinality := endpointUse.lawfulActTimeBoundary_holds
  sameRegimeFidelity := endpointUse.downstreamReusable_holds

/-- The four neutral clauses and the existing six-field adequacy surface agree. -/
theorem neutralEndpointAdequacy_iff_targetAdequate
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch) :
    NeutralEndpointAdequacy endpointUse <-> endpointUse.targetAdequate := by
  constructor
  · intro adequate
    exact
      And.intro adequate.targetDeterminacy.1
        (And.intro adequate.targetDeterminacy.2
          (And.intro adequate.stepEvaluability.1
            (And.intro adequate.stepEvaluability.2
              (And.intro adequate.sameRegimeFidelity
                adequate.actTimeFinality))))
  · intro adequate
    rcases adequate with
      ⟨targetFixed, carrierFixed, branchRoleFixed, reportable,
        downstreamReusable, lawfulActTimeBoundary⟩
    exact
      { targetDeterminacy := And.intro targetFixed carrierFixed
        stepEvaluability := And.intro branchRoleFixed reportable
        actTimeFinality := lawfulActTimeBoundary
        sameRegimeFidelity := downstreamReusable }

/--
The typed kernel-import route.  Neutral endpoint adequacy is checked first;
kernel necessity and fixed-domain closure then enter through the corpus source.
-/
structure KernelImportRoute
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (endpointUse : LocalEndpointUse S branch) where
  neutralAdequacy : NeutralEndpointAdequacy endpointUse
  corpus : KernelFirstCorpusMachinery S

def KernelImportRoute.kernelPackage
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (route : KernelImportRoute endpointUse) :
    KernelPackage S :=
  route.corpus.kernelAtEndpointUse endpointUse

/--
The kernel route is linked to the separately mechanized fixed-domain kernel
theorems.  This certificate concerns necessity and denial; population remains
the target-specific theorem stated later in this module.
-/
def KernelImportRoute.mechanizedKernelDependency
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (route : KernelImportRoute endpointUse) :
    MechanizedKernelImport.MechanizedKernelDependencyCertificate
      endpointUse route.corpus :=
  MechanizedKernelImport.mechanizedKernelDependencyCertificate
    endpointUse route.corpus

/-- No governance-equivalent same-domain construction lies below the kernel. -/
theorem KernelImportRoute.noSameDomainDerivationBelowKernel
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (route : KernelImportRoute endpointUse) :
    NoDerivationBelowKernel
      (MechanizedKernelImport.endpointConstructionRegime
        endpointUse route.corpus) :=
  route.mechanizedKernelDependency.noDerivationBelow

/-- A same-domain governance-equivalent replacement cannot shed the kernel. -/
theorem KernelImportRoute.governanceEquivalentReplacement_hasKernel
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (route : KernelImportRoute endpointUse)
    (alternative : ConstructionRegime S.Family S.Family)
    (equivalent : GovernanceEquivalent
      (MechanizedKernelImport.endpointConstructionRegime
        endpointUse route.corpus)
      alternative) :
    MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.KernelPackage
      alternative :=
  MechanizedKernelImport.governanceEquivalentReplacement_hasKernel
    route.mechanizedKernelDependency alternative equivalent

/-- The manuscript dependency order, exposed as one checked activation theorem. -/
theorem KernelImportRoute.activation
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (route : KernelImportRoute endpointUse) :
    endpointUse.targetAdequate /\
      S.nondegenerate /\
      route.kernelPackage.allRolesHold := by
  exact
    And.intro
      ((neutralEndpointAdequacy_iff_targetAdequate endpointUse).mp
        route.neutralAdequacy)
      (And.intro route.corpus.kernelNecessity.carrierNondegenerate
        route.kernelPackage.allRolesHold_holds)

/-- The five manuscript outcomes for denial or same-domain weakening. -/
inductive DenialOrWeakeningDisposition where
  | endpointUseLoss
  | domainOrPolicyChange
  | supportSkinOrBookkeepingCollapse
  | governanceEquivalentReplacement
  | independentSecondAuthority
deriving DecidableEq, Repr

/-- Translate the corpus factor ledger into the manuscript's denial ledger. -/
def denialOrWeakeningDisposition :
    SameScopeFactorDisposition -> DenialOrWeakeningDisposition
  | .bookkeeping => .supportSkinOrBookkeepingCollapse
  | .gateEquivalent => .governanceEquivalentReplacement
  | .sameSideRefinement => .supportSkinOrBookkeepingCollapse
  | .scopeChange => .domainOrPolicyChange
  | .independentAuthorizer => .independentSecondAuthority

theorem denialOrWeakeningDisposition_eq_independent_iff
    (disposition : SameScopeFactorDisposition) :
    denialOrWeakeningDisposition disposition =
        DenialOrWeakeningDisposition.independentSecondAuthority <->
      disposition = SameScopeFactorDisposition.independentAuthorizer := by
  cases disposition <;> simp [denialOrWeakeningDisposition]

/-- Strict same-domain weakening cannot create a second standing authority. -/
theorem KernelImportRoute.strictWeakening_ne_independentSecondAuthority
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (route : KernelImportRoute endpointUse)
    (factor : S.StandingFactor) :
    denialOrWeakeningDisposition
        (route.corpus.fixedDomainClosure.disposition factor) ≠
      DenialOrWeakeningDisposition.independentSecondAuthority := by
  intro independent
  exact route.corpus.fixedDomainClosure.noIndependentAuthorizer factor <|
    (denialOrWeakeningDisposition_eq_independent_iff _).mp independent

/--
Direct denial has a real endpoint cost, while strict fixed-domain weakening has
no independent-authority branch.  This is the local denial theorem used by the
hybrid route; it does not infer a fibre bound from four kernel labels alone.
-/
theorem KernelImportRoute.denialAndStrictWeakeningExhausted
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    {endpointUse : LocalEndpointUse S branch}
    (route : KernelImportRoute endpointUse)
    (denial : KernelDenialCost S)
    (factor : S.StandingFactor) :
    denial.isRealCost /\
      denialOrWeakeningDisposition
          (route.corpus.fixedDomainClosure.disposition factor) ≠
        DenialOrWeakeningDisposition.independentSecondAuthority :=
  And.intro denial.isRealCost_holds
    (route.strictWeakening_ne_independentSecondAuthority factor)

private theorem threePetalRankNondegenerate (r : Nat) :
    0 < r + 1 /\ 3 <= 3 := by
  omega

/-- The concrete no-sunflower endpoint use at rank `r + 1`. -/
def threePetalNoSunflowerEndpointUse
    (alpha : Type)
    [DecidableEq alpha]
    (r : Nat) :
    LocalEndpointUse
      (Concrete.concreteSunflowerCarrier alpha (r + 1) 3)
      (fun F => Not (Concrete.HasSunflower 3 F)) :=
  CorpusMachinery.concreteNoSunflowerEndpointUse
    alpha (r + 1) 3 (threePetalRankNondegenerate r)

/-- Concrete activation of the manuscript's neutral-antecedent kernel import. -/
def threePetalKernelImportRoute
    (alpha : Type)
    [DecidableEq alpha]
    (r : Nat) :
    KernelImportRoute (threePetalNoSunflowerEndpointUse alpha r) where
  neutralAdequacy :=
    NeutralEndpointAdequacy.ofLocalEndpointUse
      (threePetalNoSunflowerEndpointUse alpha r)
  corpus := CorpusMachinery.concreteKernelFirstCorpusMachinery
    alpha (r + 1) 3 (threePetalRankNondegenerate r)

/--
The local imported AASC packet at one dense high-rank countercase.  Kernel
activation and fixed-domain factor exhaustion are constructed above.  The two
genuine corpus obligations are kept visible: a denial-cost ledger and the
same-side identity exhaustion that rules out a fifth live blocker role.
-/
structure ThreePetalLocalKernelCloseout
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F)) where
  denialCost :
    KernelRole ->
      KernelDenialCost
        (Concrete.concreteSunflowerCarrier alpha (r + 1) 3)
  sameSideExhaustionOfKernelCloseout :
    (threePetalKernelImportRoute alpha r).kernelPackage.allRolesHold ->
    (forall role : KernelRole,
      forall factor :
        (Concrete.concreteSunflowerCarrier alpha (r + 1) 3).StandingFactor,
      (denialCost role).isRealCost /\
        denialOrWeakeningDisposition
            ((threePetalKernelImportRoute alpha r).corpus.fixedDomainClosure.disposition
              factor) ≠
          DenialOrWeakeningDisposition.independentSecondAuthority) ->
      AASCSameSideIdentityExhaustion
        (tensorProfileBound :=
          traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)
        F noSunflower

theorem ThreePetalLocalKernelCloseout.kernelActivated
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (_closeout : ThreePetalLocalKernelCloseout F noSunflower) :
    (threePetalNoSunflowerEndpointUse alpha r).targetAdequate /\
      (Concrete.concreteSunflowerCarrier alpha (r + 1) 3).nondegenerate /\
      (threePetalKernelImportRoute alpha r).kernelPackage.allRolesHold :=
  (threePetalKernelImportRoute alpha r).activation

theorem ThreePetalLocalKernelCloseout.denialAndStrictWeakeningExhausted
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (closeout : ThreePetalLocalKernelCloseout F noSunflower)
    (role : KernelRole)
    (factor :
      (Concrete.concreteSunflowerCarrier alpha (r + 1) 3).StandingFactor) :
    (closeout.denialCost role).isRealCost /\
      denialOrWeakeningDisposition
          ((threePetalKernelImportRoute alpha r).corpus.fixedDomainClosure.disposition
            factor) ≠
        DenialOrWeakeningDisposition.independentSecondAuthority :=
  (threePetalKernelImportRoute alpha r).denialAndStrictWeakeningExhausted
    (closeout.denialCost role) factor

/-- The local AASC exhaustion is downstream of activation and denial closeout. -/
def ThreePetalLocalKernelCloseout.sameSideExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (closeout : ThreePetalLocalKernelCloseout F noSunflower) :
    AASCSameSideIdentityExhaustion
      (tensorProfileBound :=
        traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)
      F noSunflower :=
  closeout.sameSideExhaustionOfKernelCloseout
    closeout.kernelActivated.2.2
    closeout.denialAndStrictWeakeningExhausted

/-- AASC same-side exhaustion mechanically populates the combinatorial load. -/
noncomputable def ThreePetalLocalKernelCloseout.toBoundedLoadExhaustion
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (closeout : ThreePetalLocalKernelCloseout F noSunflower) :
    BoundedPrivateWitnessLoadExhaustion
      (tensorProfileBound :=
        traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)
      noSunflower
      (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
        alpha 3 (by decide) r) :=
  closeout.sameSideExhaustion.toFixedIdentityRealization.toBoundedLoadExhaustion

/-- The imported local packet supplies exactly the inherited support-fibre bound. -/
theorem ThreePetalLocalKernelCloseout.canonicalSupportFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (closeout : ThreePetalLocalKernelCloseout F noSunflower) :
    CanonicalSupportFiberBound
      (tensorProfileBound :=
        traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)
      F noSunflower :=
  canonicalSupportFiberBoundOfBoundedLoadExhaustion
    closeout.toBoundedLoadExhaustion

/--
Rank-uniform corpus source for the one open high-rank regime.  Lower-rank
population and the dense countercase are explicit inputs to the local packet,
so the import cannot silently assume the final endpoint.
-/
structure ThreePetalKernelGovernedFiberClosureSource
    (alpha : Type)
    [DecidableEq alpha] where
  closeout :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower 3 F),
      threePetalSeedReflectedCutoff < r + 1 ->
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ (r + 1) <
        F.edges.card ->
      (forall s : Nat,
        s < r ->
        forall G : Concrete.UniformSetFamily alpha (s + 1),
        forall noSunflowerG : Not (Concrete.HasSunflower 3 G),
        internalTensorConstraintBase 3
            (traditionalSeedTensorProfileBound
              3 threePetalTraditionalCutoff) ^ (s + 1) <
          G.edges.card ->
        BoundedPrivateWitnessLoadExhaustion
          (tensorProfileBound := traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff)
          noSunflowerG
          (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
            alpha 3 (by decide) s)) ->
      ThreePetalLocalKernelCloseout F noSunflower

/--
The AASC packet is transferred into the exact finite support-fibre source used
by the already verified combinatorial recurrence.
-/
noncomputable def
    ThreePetalKernelGovernedFiberClosureSource.toSupportFiberInheritanceSource
    {alpha : Type}
    [DecidableEq alpha]
    (source : ThreePetalKernelGovernedFiberClosureSource alpha) :
    ThreePetalDenseHighRankSupportFiberInheritanceSource alpha where
  inheritSupportFiberBound := by
    intro r F noSunflower aboveCutoff sizeExcess lowerPopulation
    exact (source.closeout r F noSunflower aboveCutoff sizeExcess
      lowerPopulation).canonicalSupportFiberBound

/--
The manuscript transfer theorem: neutral adequacy activates the kernel, the
imported local AASC packet closes the support fibre, and the combinatorial
high-rank pipeline produces a genuine three-petal sunflower.
-/
theorem sunflower_of_threePetalKernelGovernedTransfer
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (source : ThreePetalKernelGovernedFiberClosureSource alpha)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ n < F.edges.card) :
    Concrete.HasSunflower 3 F :=
  sunflower_of_threePetalDenseHighRankSupportFiberInheritance
    source.toSupportFiberInheritanceSource F sizeExcess

/-- The same transfer route stated as the complete checked endpoint bound. -/
theorem ThreePetalKernelGovernedFiberClosureSource.provesEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    (source : ThreePetalKernelGovernedFiberClosureSource alpha) :
    ThreePetalSeedBaseEndpointBound alpha := by
  intro n F noSunflower
  exact Nat.le_of_not_gt fun sizeExcess =>
    noSunflower <|
      sunflower_of_threePetalKernelGovernedTransfer source F sizeExcess

/--
The preceding high-rank hypotheses of the manuscript's population theorem.
This bundles only generated combinatorial data: the dense countercase and all
strictly lower-rank populated countercases.
-/
structure ThreePetalDenseHighRankManuscriptContext
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F)) where
  aboveReflectedCutoff : threePetalSeedReflectedCutoff < r + 1
  sizeExcess :
    internalTensorConstraintBase 3
        (traditionalSeedTensorProfileBound
          3 threePetalTraditionalCutoff) ^ (r + 1) <
      F.edges.card
  lowerRankPopulation :
    forall s : Nat,
      s < r ->
      forall G : Concrete.UniformSetFamily alpha (s + 1),
      forall noSunflowerG : Not (Concrete.HasSunflower 3 G),
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ (s + 1) <
        G.edges.card ->
      BoundedPrivateWitnessLoadExhaustion
        (tensorProfileBound := traditionalSeedTensorProfileBound
          3 threePetalTraditionalCutoff)
        noSunflowerG
        (BlockerSupportLayers.rankUniformConcreteCorpusMachinery
          alpha 3 (by decide) s)

/--
The exact local output of manuscript Theorem 6.2.  It produces the populated
finite profile/role/slot identity after kernel activation and denial exhaustion;
it does not assume the support-fibre inequality or the sunflower endpoint.
-/
structure ThreePetalLocalManuscriptPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower 3 F)) where
  denialCost :
    KernelRole ->
      KernelDenialCost
        (Concrete.concreteSunflowerCarrier alpha (r + 1) 3)
  populateOfKernelCloseout :
    (threePetalKernelImportRoute alpha r).kernelPackage.allRolesHold ->
    (forall role : KernelRole,
      forall factor :
        (Concrete.concreteSunflowerCarrier alpha (r + 1) 3).StandingFactor,
      (denialCost role).isRealCost /\
        denialOrWeakeningDisposition
            ((threePetalKernelImportRoute alpha r).corpus.fixedDomainClosure.disposition
              factor) ≠
          DenialOrWeakeningDisposition.independentSecondAuthority) ->
      KernelFaithfulFixedIdentityRealization
        (tensorProfileBound :=
          traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)
        F noSunflower

theorem ThreePetalLocalManuscriptPopulation.denialAndStrictWeakeningExhausted
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (population : ThreePetalLocalManuscriptPopulation F noSunflower)
    (role : KernelRole)
    (factor :
      (Concrete.concreteSunflowerCarrier alpha (r + 1) 3).StandingFactor) :
    (population.denialCost role).isRealCost /\
      denialOrWeakeningDisposition
          ((threePetalKernelImportRoute alpha r).corpus.fixedDomainClosure.disposition
            factor) ≠
        DenialOrWeakeningDisposition.independentSecondAuthority :=
  (threePetalKernelImportRoute alpha r).denialAndStrictWeakeningExhausted
    (population.denialCost role) factor

/-- Apply manuscript Theorem 6.2 in the same dependency order as its proof. -/
def ThreePetalLocalManuscriptPopulation.fixedIdentityPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (population : ThreePetalLocalManuscriptPopulation F noSunflower) :
    KernelFaithfulFixedIdentityRealization
      (tensorProfileBound :=
        traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)
      F noSunflower :=
  population.populateOfKernelCloseout
    (threePetalKernelImportRoute alpha r).activation.2.2
    population.denialAndStrictWeakeningExhausted

/-- The manuscript population theorem supplies the existing local closeout. -/
noncomputable def
    ThreePetalLocalManuscriptPopulation.toLocalKernelCloseout
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (population : ThreePetalLocalManuscriptPopulation F noSunflower) :
    ThreePetalLocalKernelCloseout F noSunflower where
  denialCost := population.denialCost
  sameSideExhaustionOfKernelCloseout := by
    intro kernelRoles denialCloseout
    exact (population.populateOfKernelCloseout
      kernelRoles denialCloseout).toAASCSameSideIdentityExhaustion

/-- Manuscript Theorem 6.2 implies Theorem 6.3's canonical fibre bound. -/
theorem ThreePetalLocalManuscriptPopulation.canonicalSupportFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower 3 F)}
    (population : ThreePetalLocalManuscriptPopulation F noSunflower) :
    CanonicalSupportFiberBound
      (tensorProfileBound :=
        traditionalSeedTensorProfileBound 3 threePetalTraditionalCutoff)
      F noSunflower :=
  population.toLocalKernelCloseout.canonicalSupportFiberBound

/--
The named corpus theorem imported by the manuscript: under its generated
high-rank hypotheses, kernel-governed population inheritance produces the
profile/role/slot realization of Theorem 6.2.
-/
structure ImportedManuscriptKernelGovernedPopulationTheorem
    (alpha : Type)
    [DecidableEq alpha] where
  population :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower 3 F),
      ThreePetalDenseHighRankManuscriptContext F noSunflower ->
        ThreePetalLocalManuscriptPopulation F noSunflower

/-- The manuscript's imported population theorem constructs the fibre source. -/
noncomputable def
    ImportedManuscriptKernelGovernedPopulationTheorem.toKernelGovernedFiberClosureSource
    {alpha : Type}
    [DecidableEq alpha]
    (imported : ImportedManuscriptKernelGovernedPopulationTheorem alpha) :
    ThreePetalKernelGovernedFiberClosureSource alpha where
  closeout := by
    intro r F noSunflower aboveCutoff sizeExcess lowerPopulation
    let context : ThreePetalDenseHighRankManuscriptContext F noSunflower :=
      { aboveReflectedCutoff := aboveCutoff
        sizeExcess := sizeExcess
        lowerRankPopulation := lowerPopulation }
    exact (imported.population r F noSunflower context).toLocalKernelCloseout

/--
The Lean closure matching the manuscript closure: import its kernel-governed
population theorem, derive the support-fibre bound, and transfer to a genuine
three-petal sunflower.
-/
theorem sunflower_of_importedManuscriptKernelGovernedClosure
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    (imported : ImportedManuscriptKernelGovernedPopulationTheorem alpha)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      internalTensorConstraintBase 3
          (traditionalSeedTensorProfileBound
            3 threePetalTraditionalCutoff) ^ n < F.edges.card) :
    Concrete.HasSunflower 3 F :=
  sunflower_of_threePetalKernelGovernedTransfer
    imported.toKernelGovernedFiberClosureSource F sizeExcess

/-- The manuscript-matched closure stated as its complete endpoint theorem. -/
theorem ImportedManuscriptKernelGovernedPopulationTheorem.provesEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    (imported : ImportedManuscriptKernelGovernedPopulationTheorem alpha) :
    ThreePetalSeedBaseEndpointBound alpha := by
  intro n F noSunflower
  exact Nat.le_of_not_gt fun sizeExcess =>
    noSunflower <|
      sunflower_of_importedManuscriptKernelGovernedClosure
        imported F sizeExcess

/-- Endpoint closure can inhabit the imported theorem only by removing its case. -/
noncomputable def importedManuscriptPopulationTheoremOfEndpointBound
    {alpha : Type}
    [DecidableEq alpha]
    (bound : ThreePetalSeedBaseEndpointBound alpha) :
    ImportedManuscriptKernelGovernedPopulationTheorem alpha where
  population := by
    intro r F noSunflower context
    exact False.elim <|
      Nat.not_lt_of_ge (bound (r + 1) F noSunflower) context.sizeExcess

/--
No laundering: the imported manuscript population theorem is endpoint-strength,
although its conclusion is the local profile/role/slot population rather than
the endpoint itself.
-/
theorem nonempty_importedManuscriptPopulationTheorem_iff_endpointBound
    {alpha : Type}
    [DecidableEq alpha] :
    Nonempty (ImportedManuscriptKernelGovernedPopulationTheorem alpha) <->
      ThreePetalSeedBaseEndpointBound alpha := by
  constructor
  · intro imported
    exact imported.some.provesEndpointBound
  · intro bound
    exact ⟨importedManuscriptPopulationTheoremOfEndpointBound bound⟩

end ManuscriptKernelTransfer
end V2
end SunflowerAASC
