namespace SunflowerAASC

/-- The four kernel roles used by the AASC endpoint proof class. -/
inductive KernelRole where
  | admissibility
  | standing
  | reference
  | irreversibility
deriving DecidableEq, Repr

def kernelRoles : List KernelRole :=
  [ .admissibility
  , .standing
  , .reference
  , .irreversibility
  ]

theorem kernelRoles_length_eq : kernelRoles.length = 4 := by
  rfl

def kernelRoleTitle : KernelRole -> String
  | .admissibility => "Admissibility"
  | .standing => "Standing"
  | .reference => "Reference"
  | .irreversibility => "Irreversibility"

def kernelRoleTitles : List String :=
  kernelRoles.map kernelRoleTitle

def kernelRoleTitlesPopulated : Bool :=
  kernelRoleTitles.all (fun title => !title.isEmpty)

theorem kernelRoleTitlesPopulated_eq_true :
    kernelRoleTitlesPopulated = true := by
  rfl

/--
Abstract sunflower carrier for the fixed core-petal residual matching carrier.
The field `corePetalEquivalence` is the paper's equivalence between the usual
sunflower endpoint and the residual-petal witness on the same carrier.
-/
structure SunflowerCarrier where
  Family : Type
  Core : Type
  Petal : Type
  k : Nat
  rank : Nat
  nondegenerate : Prop
  sunflower : Family -> Prop
  residualWitness : Family -> Core -> Prop
  corePetalEndpoint : Family -> Prop :=
    fun F => Exists (fun C => residualWitness F C)
  corePetalEquivalence : forall F, sunflower F <-> corePetalEndpoint F

def SunflowerCarrier.noSunflower (S : SunflowerCarrier) (F : S.Family) : Prop :=
  Not (S.sunflower F)

def SunflowerCarrier.positiveEndpoint (S : SunflowerCarrier) (F : S.Family) : Prop :=
  S.sunflower F

def SunflowerCarrier.negativeEndpoint (S : SunflowerCarrier) (F : S.Family) : Prop :=
  S.noSunflower F

theorem corePetal_endpoint_equivalence
    (S : SunflowerCarrier)
    (F : S.Family) :
    S.sunflower F <-> S.corePetalEndpoint F := by
  exact S.corePetalEquivalence F

theorem noSunflower_iff_not_corePetalEndpoint
    (S : SunflowerCarrier)
    (F : S.Family) :
    S.noSunflower F <-> Not (S.corePetalEndpoint F) := by
  constructor
  · intro h
    change Not (S.sunflower F) at h
    intro hcore
    exact h ((S.corePetalEquivalence F).mpr hcore)
  · intro h
    change Not (S.sunflower F)
    intro hs
    exact h ((S.corePetalEquivalence F).mp hs)

/--
Manuscript anchor for the sunflower threshold `f(n,k)`.  The current audit
does not optimize or compute the threshold; it records the two threshold
properties used by the hardened manuscript.
-/
structure SunflowerThreshold (S : SunflowerCarrier) where
  value : Nat
  thresholdProperty : Prop
  supremumProperty : Prop
  thresholdProperty_holds : thresholdProperty
  supremumProperty_holds : supremumProperty

def SunflowerThreshold.thresholdSurfaceComplete
    {S : SunflowerCarrier}
    (T : SunflowerThreshold S) : Prop :=
  T.thresholdProperty /\ T.supremumProperty

theorem SunflowerThreshold.thresholdSurfaceComplete_holds
    {S : SunflowerCarrier}
    (T : SunflowerThreshold S) :
    T.thresholdSurfaceComplete := by
  exact And.intro T.thresholdProperty_holds T.supremumProperty_holds

/-- The local endpoint proof act in which a branch is used as live endpoint work. -/
structure LocalEndpointUse (S : SunflowerCarrier) (branch : S.Family -> Prop) where
  targetFixed : Prop
  carrierFixed : Prop
  branchRoleFixed : Prop
  reportable : Prop
  downstreamReusable : Prop
  lawfulActTimeBoundary : Prop
  targetFixed_holds : targetFixed
  carrierFixed_holds : carrierFixed
  branchRoleFixed_holds : branchRoleFixed
  reportable_holds : reportable
  downstreamReusable_holds : downstreamReusable
  lawfulActTimeBoundary_holds : lawfulActTimeBoundary

def LocalEndpointUse.targetAdequate
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) : Prop :=
  U.targetFixed /\
  U.carrierFixed /\
  U.branchRoleFixed /\
  U.reportable /\
  U.downstreamReusable /\
  U.lawfulActTimeBoundary

theorem LocalEndpointUse.targetAdequate_holds
    {S : SunflowerCarrier}
    {branch : S.Family -> Prop}
    (U : LocalEndpointUse S branch) :
    U.targetAdequate := by
  exact
    And.intro U.targetFixed_holds
      (And.intro U.carrierFixed_holds
        (And.intro U.branchRoleFixed_holds
          (And.intro U.reportable_holds
            (And.intro U.downstreamReusable_holds
              U.lawfulActTimeBoundary_holds))))

/-- Same-domain endpoint-status discriminator, represented as a typed status act. -/
structure IndependentDiscriminator
    (S : SunflowerCarrier)
    (branch positive : S.Family -> Prop) where
  sameCarrier : Prop
  sameDomain : Prop
  discriminatesEndpointStatus : Prop
  independentOfKernel : Prop
  sameCarrier_holds : sameCarrier
  sameDomain_holds : sameDomain
  discriminatesEndpointStatus_holds : discriminatesEndpointStatus
  independentOfKernel_holds : independentOfKernel

end SunflowerAASC
