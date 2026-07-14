import SunflowerAASC.V2.EffectiveBlocker
import SunflowerAASC.V2.MinimalBlocker
import SunflowerAASC.V2.WitnessCompression
import SunflowerAASC.V2.CorpusMachinery

namespace SunflowerAASC
namespace V2
namespace BlockerSupportLayers

/-- Matching petals whose residual part contains one raw blocker coordinate. -/
def supportingPetals
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : Concrete.FiniteCoreLinkMatching F core)
    (x : {x // x ∈ M.rawBlocker}) :
    Finset {edge // edge ∈ M.petals} :=
  Finset.univ.filter (fun edge => x.val ∈ edge.val \ core)

theorem supportingPetals_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : Concrete.FiniteCoreLinkMatching F core)
    (x : {x // x ∈ M.rawBlocker}) :
    (supportingPetals M x).Nonempty := by
  rcases Finset.mem_biUnion.mp x.property with ⟨edge, edge_mem, x_mem⟩
  exact ⟨⟨edge, edge_mem⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, x_mem⟩⟩

theorem supportingPetals_card_le_one
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : Concrete.FiniteCoreLinkMatching F core)
    (x : {x // x ∈ M.rawBlocker}) :
    (supportingPetals M x).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro left left_mem right right_mem
  apply Subtype.ext
  apply Classical.byContradiction
  intro petals_ne
  have left_hit : x.val ∈ left.val \ core :=
    (Finset.mem_filter.mp left_mem).2
  have right_hit : x.val ∈ right.val \ core :=
    (Finset.mem_filter.mp right_mem).2
  exact Finset.disjoint_left.mp
    (M.residuals_disjoint
      left.val right.val left.property right.property petals_ne)
    left_hit
    right_hit

theorem supportingPetals_card_eq_one
    {alpha : Type}
    [DecidableEq alpha]
    {n : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    (M : Concrete.FiniteCoreLinkMatching F core)
    (x : {x // x ∈ M.rawBlocker}) :
    (supportingPetals M x).card = 1 := by
  exact Nat.le_antisymm
    (supportingPetals_card_le_one M x)
    (Finset.one_le_card.mpr (supportingPetals_nonempty M x))

/-- Encode the mandatory matching-incidence layer inside `Fin k`. -/
noncomputable def supportLayerCell
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    {M : Concrete.FiniteCoreLinkMatching F core}
    (matchingSize_le : M.petals.card <= k)
    (x : {x // x ∈ M.rawBlocker}) : Finset (Fin k) :=
  (supportingPetals M x).map
    (WitnessCompression.matchingPetalEmbedding M matchingSize_le)

theorem supportLayerCell_card_eq_one
    {alpha : Type}
    [DecidableEq alpha]
    {n k : Nat}
    {F : Concrete.UniformSetFamily alpha n}
    {core : Finset alpha}
    {M : Concrete.FiniteCoreLinkMatching F core}
    (matchingSize_le : M.petals.card <= k)
    (x : {x // x ∈ M.rawBlocker}) :
    (supportLayerCell matchingSize_le x).card = 1 := by
  rw [supportLayerCell, Finset.card_map]
  exact supportingPetals_card_eq_one M x

noncomputable def canonicalSupportLayerCell
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (x : {x // x ∈ EffectiveBlocker.canonicalRawBlocker F}) :
    Finset (Fin k) :=
  supportLayerCell
    (Nat.le_of_lt <| Concrete.finiteCoreLinkMatching_card_lt_of_noSunflower
      noSunflower
      (EffectiveBlocker.emptyCoreMaximalMatching F).matching)
    x

theorem canonicalSupportLayerCell_card_eq_one
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (x : {x // x ∈ EffectiveBlocker.canonicalRawBlocker F}) :
    (canonicalSupportLayerCell F noSunflower x).card = 1 := by
  exact supportLayerCell_card_eq_one
    (Nat.le_of_lt <| Concrete.finiteCoreLinkMatching_card_lt_of_noSunflower
      noSunflower
      (EffectiveBlocker.emptyCoreMaximalMatching F).matching)
    x

/--
The remaining within-cell AASC population over the mandatory matching-support
layers.  Effective representatives stay inside the raw blocker and preserve
all hits needed by the recurrence.
-/
structure SupportFiberCompression
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (fiberBound : Nat)
    (F : Concrete.UniformSetFamily alpha (r + 1))
    (noSunflower : Not (Concrete.HasSunflower k F)) where
  effectiveBlocker : Finset alpha
  effective_subset_raw :
    effectiveBlocker ⊆ EffectiveBlocker.canonicalRawBlocker F
  fiberSlot : {x // x ∈ effectiveBlocker} -> Fin fiberBound
  skinOutcome :
    {x // x ∈ effectiveBlocker} -> {x // x ∈ effectiveBlocker} -> Prop
  tensorSplitOutcome :
    {x // x ∈ effectiveBlocker} -> {x // x ∈ effectiveBlocker} -> Prop
  sunflowerOutcome :
    {x // x ∈ effectiveBlocker} -> {x // x ∈ effectiveBlocker} -> Prop
  collisionExhaustive :
    forall left right : {x // x ∈ effectiveBlocker},
      canonicalSupportLayerCell F noSunflower
          ⟨left.val, effective_subset_raw left.property⟩ =
        canonicalSupportLayerCell F noSunflower
          ⟨right.val, effective_subset_raw right.property⟩ ->
      fiberSlot left = fiberSlot right ->
      left = right \/
      skinOutcome left right \/
      tensorSplitOutcome left right \/
      sunflowerOutcome left right
  skinFinality :
    forall left right, skinOutcome left right -> left = right
  tensorSplitExcluded :
    forall left right, tensorSplitOutcome left right -> False
  sunflowerExcluded :
    forall left right, sunflowerOutcome left right -> False
  preservesRawHits :
    forall edge : Finset alpha, edge ∈ F.edges ->
      Not (Disjoint edge (EffectiveBlocker.canonicalRawBlocker F)) ->
      Not (Disjoint edge effectiveBlocker)

theorem SupportFiberCompression.collision
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Compression : SupportFiberCompression fiberBound F noSunflower)
    (left right : {x // x ∈ Compression.effectiveBlocker})
    (sameCell :
      canonicalSupportLayerCell F noSunflower
          ⟨left.val, Compression.effective_subset_raw left.property⟩ =
        canonicalSupportLayerCell F noSunflower
          ⟨right.val, Compression.effective_subset_raw right.property⟩)
    (sameSlot : Compression.fiberSlot left = Compression.fiberSlot right) :
    left = right := by
  rcases Compression.collisionExhaustive left right sameCell sameSlot with
    equal | skinOrTensorOrSun
  · exact equal
  · rcases skinOrTensorOrSun with skin | tensorOrSun
    · exact Compression.skinFinality left right skin
    · rcases tensorOrSun with tensor | sunflower
      · exact False.elim (Compression.tensorSplitExcluded left right tensor)
      · exact False.elim (Compression.sunflowerExcluded left right sunflower)

noncomputable def SupportFiberCompression.toVennCompressedBlocker
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    (Compression : SupportFiberCompression fiberBound F noSunflower) :
    EffectiveBlocker.VennCompressedBlocker k fiberBound F where
  effectiveBlocker := Compression.effectiveBlocker
  effective_subset_raw := Compression.effective_subset_raw
  code := fun x =>
    (canonicalSupportLayerCell F noSunflower
      ⟨x.val, Compression.effective_subset_raw x.property⟩,
      Compression.fiberSlot x)
  code_injective := by
    intro left right sameCode
    exact Compression.collision left right
      (congrArg Prod.fst sameCode)
      (congrArg Prod.snd sameCode)
  preservesRawHits := Compression.preservesRawHits

/-- Rank-uniform support-layer and within-cell fiber population. -/
structure RankUniformSupportFiberSource
    (alpha : Type)
    [DecidableEq alpha]
    (k fiberBound : Nat) where
  fiberBound_positive : 0 < fiberBound
  compress :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      SupportFiberCompression fiberBound F noSunflower

noncomputable def RankUniformSupportFiberSource.toVennCompressionSource
    {alpha : Type}
    [DecidableEq alpha]
    {k fiberBound : Nat}
    (Src : RankUniformSupportFiberSource alpha k fiberBound) :
    EffectiveBlocker.RankUniformVennCompressionSource
      alpha k k fiberBound where
  fiberBound_positive := Src.fiberBound_positive
  compress := fun r F noSunflower =>
    (Src.compress r F noSunflower).toVennCompressedBlocker

theorem sunflower_of_supportFiberCompression
    {alpha : Type}
    [DecidableEq alpha]
    {n k fiberBound : Nat}
    (Src : RankUniformSupportFiberSource alpha k fiberBound)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      VennSeparation.vennAlphabetSize k fiberBound ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact EffectiveBlocker.sunflower_of_uniformVennBlockerCompression
    Src.toVennCompressionSource
    F
    sizeExcess

def rankUniformConcreteCorpusMachinery
    (alpha : Type)
    [DecidableEq alpha]
    (k : Nat)
    (k_nondegenerate : 3 <= k)
    (r : Nat) :
    KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k) :=
  CorpusMachinery.concreteKernelFirstCorpusMachinery
    alpha
    (r + 1)
    k
    ⟨Nat.zero_lt_succ r, k_nondegenerate⟩

/--
Kernel-first AASC population inside one mandatory support cell.  A surviving
same-cell, same-slot non-skin distinction would be an independent authorizer.
-/
structure CorpusSupportFiberAssignment
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)) where
  effectiveBlocker : Finset alpha
  effective_subset_raw :
    effectiveBlocker ⊆ EffectiveBlocker.canonicalRawBlocker F
  fiberSlot : {x // x ∈ effectiveBlocker} -> Fin fiberBound
  skinEquivalent :
    {x // x ∈ effectiveBlocker} -> {x // x ∈ effectiveBlocker} -> Prop
  nonSkinSameCellSlotCreatesIndependentAuthorizer :
    forall left right : {x // x ∈ effectiveBlocker},
      canonicalSupportLayerCell F noSunflower
          ⟨left.val, effective_subset_raw left.property⟩ =
        canonicalSupportLayerCell F noSunflower
          ⟨right.val, effective_subset_raw right.property⟩ ->
      fiberSlot left = fiberSlot right ->
      Not (skinEquivalent left right) ->
      Exists (fun factor :
        (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
        corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)
  skinFinality :
    forall left right, skinEquivalent left right -> left = right
  preservesRawHits :
    forall edge : Finset alpha, edge ∈ F.edges ->
      Not (Disjoint edge (EffectiveBlocker.canonicalRawBlocker F)) ->
      Not (Disjoint edge effectiveBlocker)

theorem CorpusSupportFiberAssignment.sameCellSlotImpliesSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Assignment : CorpusSupportFiberAssignment
      (fiberBound := fiberBound) noSunflower corpus)
    (left right : {x // x ∈ Assignment.effectiveBlocker})
    (sameCell :
      canonicalSupportLayerCell F noSunflower
          ⟨left.val, Assignment.effective_subset_raw left.property⟩ =
        canonicalSupportLayerCell F noSunflower
          ⟨right.val, Assignment.effective_subset_raw right.property⟩)
    (sameSlot : Assignment.fiberSlot left = Assignment.fiberSlot right) :
    Assignment.skinEquivalent left right := by
  apply Classical.byContradiction
  intro nonSkin
  rcases Assignment.nonSkinSameCellSlotCreatesIndependentAuthorizer
      left right sameCell sameSlot nonSkin with ⟨factor, independent⟩
  exact corpus.fixedDomainClosure.excludesIndependentAuthorizer
    factor
    independent

noncomputable def CorpusSupportFiberAssignment.toSupportFiberCompression
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Assignment : CorpusSupportFiberAssignment
      (fiberBound := fiberBound) noSunflower corpus) :
    SupportFiberCompression fiberBound F noSunflower where
  effectiveBlocker := Assignment.effectiveBlocker
  effective_subset_raw := Assignment.effective_subset_raw
  fiberSlot := Assignment.fiberSlot
  skinOutcome := Assignment.skinEquivalent
  tensorSplitOutcome := fun _ _ => False
  sunflowerOutcome := fun _ _ => False
  collisionExhaustive := by
    intro left right sameCell sameSlot
    exact Or.inr (Or.inl <|
      Assignment.sameCellSlotImpliesSkin left right sameCell sameSlot)
  skinFinality := Assignment.skinFinality
  tensorSplitExcluded := fun _ _ impossible => impossible
  sunflowerExcluded := fun _ _ impossible => impossible
  preservesRawHits := Assignment.preservesRawHits

/--
The irreducible source obligation after finite minimalization.  Its carrier is
the canonical cardinality-minimal blocker, so subset selection, preservation
of every family hit, and private witness edges are already theorems.
-/
structure MinimalCorpusSupportFiberPopulation
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    (noSunflower : Not (Concrete.HasSunflower k F))
    (corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)) where
  fiberSlot :
    {x // x ∈ MinimalBlocker.minimalBlocker F} -> Fin fiberBound
  skinEquivalent :
    {x // x ∈ MinimalBlocker.minimalBlocker F} ->
      {x // x ∈ MinimalBlocker.minimalBlocker F} -> Prop
  nonSkinSameCellSlotCreatesIndependentAuthorizer :
    forall left right : {x // x ∈ MinimalBlocker.minimalBlocker F},
      canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩ ->
      fiberSlot left = fiberSlot right ->
      Not (skinEquivalent left right) ->
      Exists (fun factor :
        (Concrete.concreteSunflowerCarrier alpha (r + 1) k).StandingFactor =>
        corpus.fixedDomainClosure.disposition factor =
          SameScopeFactorDisposition.independentAuthorizer)
  skinFinality :
    forall left right, skinEquivalent left right -> left = right

theorem MinimalCorpusSupportFiberPopulation.sameCellSlotImpliesSkin
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : MinimalCorpusSupportFiberPopulation
      (fiberBound := fiberBound) noSunflower corpus)
    (left right : {x // x ∈ MinimalBlocker.minimalBlocker F})
    (sameCell :
      canonicalSupportLayerCell F noSunflower
          ⟨left.val, MinimalBlocker.minimalBlocker_subset_raw F left.property⟩ =
        canonicalSupportLayerCell F noSunflower
          ⟨right.val, MinimalBlocker.minimalBlocker_subset_raw F right.property⟩)
    (sameSlot : Population.fiberSlot left = Population.fiberSlot right) :
    Population.skinEquivalent left right := by
  apply Classical.byContradiction
  intro nonSkin
  rcases Population.nonSkinSameCellSlotCreatesIndependentAuthorizer
      left right sameCell sameSlot nonSkin with ⟨factor, independent⟩
  exact corpus.fixedDomainClosure.excludesIndependentAuthorizer
    factor
    independent

noncomputable def MinimalCorpusSupportFiberPopulation.toAssignment
    {alpha : Type}
    [DecidableEq alpha]
    {r k fiberBound : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 1)}
    {noSunflower : Not (Concrete.HasSunflower k F)}
    {corpus : KernelFirstCorpusMachinery
      (Concrete.concreteSunflowerCarrier alpha (r + 1) k)}
    (Population : MinimalCorpusSupportFiberPopulation
      (fiberBound := fiberBound) noSunflower corpus) :
    CorpusSupportFiberAssignment
      (fiberBound := fiberBound) noSunflower corpus where
  effectiveBlocker := MinimalBlocker.minimalBlocker F
  effective_subset_raw := MinimalBlocker.minimalBlocker_subset_raw F
  fiberSlot := Population.fiberSlot
  skinEquivalent := Population.skinEquivalent
  nonSkinSameCellSlotCreatesIndependentAuthorizer :=
    Population.nonSkinSameCellSlotCreatesIndependentAuthorizer
  skinFinality := Population.skinFinality
  preservesRawHits := by
    intro edge edge_mem _
    exact MinimalBlocker.minimalBlocker_hitsEveryEdge F edge edge_mem

/-- Uniform corpus-controlled minimal-blocker fiber population at every rank. -/
structure RankUniformCorpusSupportFiberSource
    (alpha : Type)
    [DecidableEq alpha]
    (k fiberBound : Nat)
    (k_nondegenerate : 3 <= k) where
  fiberBound_positive : 0 < fiberBound
  assign :
    forall r : Nat,
      forall F : Concrete.UniformSetFamily alpha (r + 1),
      forall noSunflower : Not (Concrete.HasSunflower k F),
      MinimalCorpusSupportFiberPopulation
        (fiberBound := fiberBound)
        noSunflower
        (rankUniformConcreteCorpusMachinery alpha k k_nondegenerate r)

noncomputable def RankUniformCorpusSupportFiberSource.toSupportFiberSource
    {alpha : Type}
    [DecidableEq alpha]
    {k fiberBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : RankUniformCorpusSupportFiberSource
      alpha k fiberBound k_nondegenerate) :
    RankUniformSupportFiberSource alpha k fiberBound where
  fiberBound_positive := Src.fiberBound_positive
  compress := fun r F noSunflower =>
    (Src.assign r F noSunflower).toAssignment.toSupportFiberCompression

theorem sunflower_of_corpusSupportFiberCompression
    {alpha : Type}
    [DecidableEq alpha]
    {n k fiberBound : Nat}
    {k_nondegenerate : 3 <= k}
    (Src : RankUniformCorpusSupportFiberSource
      alpha k fiberBound k_nondegenerate)
    (F : Concrete.UniformSetFamily alpha n)
    (sizeExcess :
      VennSeparation.vennAlphabetSize k fiberBound ^ n < F.edges.card) :
    Concrete.HasSunflower k F := by
  exact sunflower_of_supportFiberCompression
    Src.toSupportFiberSource
    F
    sizeExcess

end BlockerSupportLayers
end V2
end SunflowerAASC
