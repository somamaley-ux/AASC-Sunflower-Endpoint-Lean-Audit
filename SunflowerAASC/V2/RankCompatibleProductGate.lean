import SunflowerAASC.V2.ResidualGateContextQuotient

namespace SunflowerAASC
namespace V2
namespace RankCompatibleProductGate

open ResidualVennPincer
open ResidualGateContextQuotient

/-- A component tuple belongs to the graded product layer at the residual rank. -/
def ProductRankCompatible
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F) : Prop :=
  (componentCodeOfProduct F product).rank = r + 1

/-- The finite product layer whose component ranks add to the residual rank. -/
abbrev RankCompatibleProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :=
  {product : ResidualComponentProduct F // ProductRankCompatible F product}

noncomputable instance rankCompatibleProductFintype
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Fintype (RankCompatibleProduct F) :=
  Fintype.ofFinite (RankCompatibleProduct F)

/-- Every realized residual product lies in the rank-compatible layer. -/
noncomputable def residualRankCompatibleProductCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} →
      RankCompatibleProduct F :=
  fun edge => ⟨residualProductCode F edge, by
    rw [ProductRankCompatible, componentCodeOfProduct_residualProductCode,
      componentCodeOfEdge_rank]
    exact (PrivateWitnessReduction.residualFamily F).uniform edge.val edge.property⟩

theorem residualRankCompatibleProductCode_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Function.Injective (residualRankCompatibleProductCode F) := by
  intro left right sameCode
  apply residualProductCode_injective F
  exact congrArg Subtype.val sameCode

/-- The rank-compatible tuples actually realized by residual edges. -/
noncomputable def occupiedRankCompatibleProducts
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Finset (RankCompatibleProduct F) :=
  Finset.univ.image (residualRankCompatibleProductCode F)

/-- Graded fullness asks only for recombination at the required total rank. -/
def RankCompatibleProductFull
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) : Prop :=
  occupiedRankCompatibleProducts F = Finset.univ

/-- A missing tuple at the correct total rank, rather than a rank-incompatible artifact. -/
structure MissingRankCompatibleCombination
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) where
  code : RankCompatibleProduct F
  notOccupied : code ∉ occupiedRankCompatibleProducts F

theorem residualRankCompatibleProductCode_mem_occupied
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    residualRankCompatibleProductCode F edge ∈
      occupiedRankCompatibleProducts F := by
  classical
  exact Finset.mem_image.mpr ⟨edge, Finset.mem_univ edge, rfl⟩

/-- A missing rank-compatible tuple is also a literal missing product tuple. -/
noncomputable def MissingRankCompatibleCombination.toMissingCombination
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    {F : Concrete.UniformSetFamily alpha (r + 2)}
    (missing : MissingRankCompatibleCombination F) :
    MissingComponentCombination F where
  code := missing.code.val
  notOccupied := by
    intro occupied
    apply missing.notOccupied
    rcases Finset.mem_image.mp occupied with ⟨edge, _, sameCode⟩
    exact Finset.mem_image.mpr
      ⟨edge, Finset.mem_univ edge, Subtype.ext sameCode⟩

/-- The graded component image is either full or has a genuine same-rank omission. -/
theorem rankCompatibleProductFull_or_missing
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    RankCompatibleProductFull F ∨
      Nonempty (MissingRankCompatibleCombination F) := by
  classical
  by_cases full : RankCompatibleProductFull F
  · exact Or.inl full
  · apply Or.inr
    change occupiedRankCompatibleProducts F ≠
      (Finset.univ : Finset (RankCompatibleProduct F)) at full
    have notEqual : occupiedRankCompatibleProducts F ≠
        (Finset.univ : Finset (RankCompatibleProduct F)) := full
    have strict : occupiedRankCompatibleProducts F ⊂
        (Finset.univ : Finset (RankCompatibleProduct F)) :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, notEqual⟩
    rcases (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mp strict with
      ⟨code, _, codeNotOccupied⟩
    exact ⟨⟨code, codeNotOccupied⟩⟩

theorem residualRankCompatibleProductCode_surjective_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : RankCompatibleProductFull F) :
    Function.Surjective (residualRankCompatibleProductCode F) := by
  classical
  change occupiedRankCompatibleProducts F =
    (Finset.univ : Finset (RankCompatibleProduct F)) at full
  intro code
  have codeMem : code ∈ occupiedRankCompatibleProducts F := by
    rw [full]
    exact Finset.mem_univ code
  rcases Finset.mem_image.mp codeMem with ⟨edge, _, sameCode⟩
  exact ⟨edge, sameCode⟩

/-- Graded fullness identifies residual edges with exactly the compatible layer. -/
theorem residualFamily_card_eq_rankCompatibleProducts_of_full
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : RankCompatibleProductFull F) :
    (PrivateWitnessReduction.residualFamily F).edges.card =
      Fintype.card (RankCompatibleProduct F) := by
  classical
  let equivalence :
      {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} ≃
        RankCompatibleProduct F :=
    Equiv.ofBijective (residualRankCompatibleProductCode F)
      ⟨residualRankCompatibleProductCode_injective F,
        residualRankCompatibleProductCode_surjective_of_full F full⟩
  simpa using Fintype.card_congr equivalence

/-- Every compatible tuple assembles to a residual edge under graded fullness. -/
theorem assembledProduct_mem_residualFamily_of_rankCompatibleFull
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : RankCompatibleProductFull F)
    (product : ResidualComponentProduct F)
    (compatible : ProductRankCompatible F product) :
    assembleComponentCode F (componentCodeOfProduct F product) ∈
      (PrivateWitnessReduction.residualFamily F).edges := by
  let compatibleProduct : RankCompatibleProduct F := ⟨product, compatible⟩
  rcases residualRankCompatibleProductCode_surjective_of_full
      F full compatibleProduct with ⟨edge, sameProduct⟩
  have sameCode := congrArg (componentCodeOfProduct F)
    (congrArg Subtype.val sameProduct)
  change componentCodeOfProduct F (residualProductCode F edge) =
    componentCodeOfProduct F product at sameCode
  rw [componentCodeOfProduct_residualProductCode] at sameCode
  rw [← sameCode, assemble_componentCodeOfEdge]
  exact edge.property

/-- Replacing one petal component by another of the same size preserves total rank. -/
theorem replacePetalProduct_rankCompatible_of_same_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (compatible : ProductRankCompatible F product)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalComponentFamily F petal})
    (sameCard : part.val.card = (product.1 petal).val.card) :
    ProductRankCompatible F (replacePetalProduct F product petal part) := by
  classical
  have updatedSum :
      (∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        ((Function.update product.1 petal part slot).val).card) =
      ∑ slot : {edge // edge ∈ (residualMatching F).matching.petals},
        (product.1 slot).val.card := by
    calc
      _ = part.val.card +
          ∑ slot ∈ (Finset.univ.erase petal),
            ((Function.update product.1 petal part slot).val).card :=
        (Finset.add_sum_erase Finset.univ
          (fun slot => ((Function.update product.1 petal part slot).val).card)
          (Finset.mem_univ petal)).symm.trans <| by simp
      _ = (product.1 petal).val.card +
          ∑ slot ∈ (Finset.univ.erase petal),
            (product.1 slot).val.card := by
        apply congrArg₂ (· + ·) sameCard
        apply Finset.sum_congr rfl
        intro slot slotMem
        have slotNe : slot ≠ petal := Finset.ne_of_mem_erase slotMem
        simp [Function.update, slotNe]
      _ = _ := Finset.add_sum_erase Finset.univ
        (fun slot => (product.1 slot).val.card) (Finset.mem_univ petal)
  rw [ProductRankCompatible, componentCodeOfProduct,
    ResidualComponentCode.rank, replacePetalProduct]
  rw [updatedSum]
  exact compatible

/-- Replacing the outside component by another of the same size preserves total rank. -/
theorem replaceOutsideProduct_rankCompatible_of_same_card
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (compatible : ProductRankCompatible F product)
    (outside : {outside // outside ∈ outsideComponentFamily F})
    (sameCard : outside.val.card = product.2.val.card) :
    ProductRankCompatible F (replaceOutsideProduct F product outside) := by
  rw [ProductRankCompatible, componentCodeOfProduct,
    ResidualComponentCode.rank, replaceOutsideProduct]
  simpa [sameCard] using compatible

/-- One fixed-cardinality slice of a petal component language. -/
noncomputable def petalRankGradeFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (s : Nat) : Concrete.UniformSetFamily alpha s where
  edges := (petalComponentFamily F petal).filter fun part => part.card = s
  uniform := by
    intro part partMem
    exact (Finset.mem_filter.mp partMem).2

theorem mem_petalRankGradeFamily_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : Finset alpha) :
    part ∈ (petalRankGradeFamily F petal s).edges ↔
      part ∈ petalComponentFamily F petal ∧ part.card = s := by
  simp [petalRankGradeFamily]

/-- A nonempty petal grade has a realized compatible context at that grade. -/
theorem exists_product_with_petal_rank_of_grade_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (gradeNonempty : (petalRankGradeFamily F petal s).edges.Nonempty) :
    ∃ product : ResidualComponentProduct F,
      ProductRankCompatible F product ∧ (product.1 petal).val.card = s := by
  rcases gradeNonempty with ⟨part, partMem⟩
  have componentMem := (mem_petalRankGradeFamily_iff F petal part).mp partMem |>.1
  have partCard := (petalRankGradeFamily F petal s).uniform part partMem
  rcases Finset.mem_image.mp componentMem with ⟨edge, edgeMem, samePart⟩
  let residualEdge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} := ⟨edge, edgeMem⟩
  refine ⟨residualProductCode F residualEdge,
    (residualRankCompatibleProductCode F residualEdge).property, ?_⟩
  change (edge ∩ petal.val).card = s
  rw [samePart]
  exact partCard

/-- A sunflower in one fixed-rank petal slice lifts through graded fullness. -/
theorem hasResidualSunflower_of_petalRankGrade
    {alpha : Type}
    [DecidableEq alpha]
    {r k s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : RankCompatibleProductFull F)
    (product : ResidualComponentProduct F)
    (compatible : ProductRankCompatible F product)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (productRank : (product.1 petal).val.card = s)
    (factorSunflower : Concrete.HasSunflower k
      (petalRankGradeFamily F petal s)) :
    Concrete.HasSunflower k (PrivateWitnessReduction.residualFamily F) := by
  classical
  rcases factorSunflower with ⟨core, ⟨W⟩⟩
  let part : Fin k → {part // part ∈ petalComponentFamily F petal} :=
    fun i => ⟨W.petals i,
      (mem_petalRankGradeFamily_iff F petal (W.petals i)).mp
        (W.petals_mem i) |>.1⟩
  let productAt : Fin k → ResidualComponentProduct F :=
    fun i => replacePetalProduct F product petal (part i)
  let liftedEdge : Fin k → Finset alpha :=
    fun i => assembleComponentCode F (componentCodeOfProduct F (productAt i))
  let fixed := fixedPetalContext F product petal
  refine ⟨core ∪ fixed, ⟨{
    petals := liftedEdge
    petals_mem := ?_
    petals_injective := ?_
    pairwise_intersection := ?_ }⟩⟩
  · intro i
    apply assembledProduct_mem_residualFamily_of_rankCompatibleFull F full
    apply replacePetalProduct_rankCompatible_of_same_card
      F product compatible petal (part i)
    have rankAtI := (petalRankGradeFamily F petal s).uniform
      (W.petals i) (W.petals_mem i)
    simpa [part, productRank] using rankAtI
  · intro i j sameEdge
    apply W.petals_injective
    have sameIntersection :=
      congrArg (fun edge : Finset alpha => edge ∩ petal.val) sameEdge
    simp only [liftedEdge, productAt] at sameIntersection
    rw [assemble_replacePetalProduct_inter_petal F product petal (part i),
      assemble_replacePetalProduct_inter_petal F product petal (part j)] at sameIntersection
    exact sameIntersection
  · intro i j distinct
    have leftSubset : W.petals i ⊆ petal.val :=
      petalComponent_subset_petal F petal (part i)
    have rightSubset : W.petals j ⊆ petal.val :=
      petalComponent_subset_petal F petal (part j)
    have contextDisjoint := fixedPetalContext_disjoint F product petal
    have leftDisjoint : Disjoint (W.petals i) fixed :=
      contextDisjoint.mono_left leftSubset
    have rightDisjoint : Disjoint (W.petals j) fixed :=
      contextDisjoint.mono_left rightSubset
    rw [show liftedEdge i = W.petals i ∪ fixed by
          exact assemble_replacePetalProduct F product petal (part i),
      show liftedEdge j = W.petals j ∪ fixed by
          exact assemble_replacePetalProduct F product petal (part j),
      union_fixed_inter_union_fixed
        (W.petals i) (W.petals j) fixed leftDisjoint rightDisjoint,
      W.pairwise_intersection i j distinct]

theorem petalRankGrade_noSunflower_of_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r k s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (gradeNonempty : (petalRankGradeFamily F petal s).edges.Nonempty) :
    Not (Concrete.HasSunflower k (petalRankGradeFamily F petal s)) := by
  rcases exists_product_with_petal_rank_of_grade_nonempty
      F petal gradeNonempty with ⟨product, compatible, productRank⟩
  intro factorSunflower
  exact PrivateWitnessReduction.residualFamily_noSunflower noSunflower
    (hasResidualSunflower_of_petalRankGrade
      F full product compatible petal productRank factorSunflower)

/-- Every strict lower-rank petal grade inherits the ordinary induction bound. -/
theorem petalRankGrade_card_le_of_lowerRankBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k s base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (rankLower : s < r + 1)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    (petalRankGradeFamily F petal s).edges.card ≤ base ^ s := by
  by_cases gradeNonempty : (petalRankGradeFamily F petal s).edges.Nonempty
  · exact lowerRankBound s rankLower (petalRankGradeFamily F petal s)
      (petalRankGrade_noSunflower_of_nonempty
        F noSunflower full petal gradeNonempty)
  · have gradeEmpty : (petalRankGradeFamily F petal s).edges = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp gradeNonempty
    simp [gradeEmpty]

/-- A full-rank petal grade contains only the matching petal itself. -/
theorem petalRankGrade_fullRank_card_le_one
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    (petalRankGradeFamily F petal (r + 1)).edges.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro left leftMem right rightMem
  have leftComponent :=
    (mem_petalRankGradeFamily_iff F petal left).mp leftMem |>.1
  have rightComponent :=
    (mem_petalRankGradeFamily_iff F petal right).mp rightMem |>.1
  have petalMem : petal.val ∈
      (PrivateWitnessReduction.residualFamily F).edges :=
    (residualMatching F).matching.petals_subset petal.property
  have petalCard : petal.val.card = r + 1 :=
    (PrivateWitnessReduction.residualFamily F).uniform petal.val petalMem
  have leftCard := (petalRankGradeFamily F petal (r + 1)).uniform left leftMem
  have rightCard := (petalRankGradeFamily F petal (r + 1)).uniform right rightMem
  have leftEq : left = petal.val := by
    apply Finset.eq_of_subset_of_card_le
      (petalComponent_subset_petal F petal ⟨left, leftComponent⟩)
    rw [petalCard, leftCard]
  have rightEq : right = petal.val := by
    apply Finset.eq_of_subset_of_card_le
      (petalComponent_subset_petal F petal ⟨right, rightComponent⟩)
    rw [petalCard, rightCard]
  exact leftEq.trans rightEq.symm

/-- Every petal grade through the parent rank has the expected power bound. -/
theorem petalRankGrade_card_le_pow
    {alpha : Type}
    [DecidableEq alpha]
    {r k s base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (rankAtMost : s ≤ r + 1)
    (basePositive : 0 < base)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    (petalRankGradeFamily F petal s).edges.card ≤ base ^ s := by
  by_cases rankLower : s < r + 1
  · exact petalRankGrade_card_le_of_lowerRankBound
      F noSunflower full petal rankLower lowerRankBound
  · have rankEq : s = r + 1 := by omega
    subst s
    exact (petalRankGrade_fullRank_card_le_one F petal).trans <| by
      have powerPositive : 0 < base ^ (r + 1) := pow_pos basePositive _
      omega

/-- One fixed-cardinality slice of the outside component language. -/
noncomputable def outsideRankGradeFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (s : Nat) : Concrete.UniformSetFamily alpha s where
  edges := (outsideComponentFamily F).filter fun part => part.card = s
  uniform := by
    intro part partMem
    exact (Finset.mem_filter.mp partMem).2

theorem mem_outsideRankGradeFamily_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (part : Finset alpha) :
    part ∈ (outsideRankGradeFamily F s).edges ↔
      part ∈ outsideComponentFamily F ∧ part.card = s := by
  simp [outsideRankGradeFamily]

theorem exists_product_with_outside_rank_of_grade_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (gradeNonempty : (outsideRankGradeFamily F s).edges.Nonempty) :
    ∃ product : ResidualComponentProduct F,
      ProductRankCompatible F product ∧ product.2.val.card = s := by
  rcases gradeNonempty with ⟨part, partMem⟩
  have componentMem := (mem_outsideRankGradeFamily_iff F part).mp partMem |>.1
  have partCard := (outsideRankGradeFamily F s).uniform part partMem
  rcases Finset.mem_image.mp componentMem with ⟨edge, edgeMem, samePart⟩
  let residualEdge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} := ⟨edge, edgeMem⟩
  refine ⟨residualProductCode F residualEdge,
    (residualRankCompatibleProductCode F residualEdge).property, ?_⟩
  change (edge \ residualSupport F).card = s
  rw [samePart]
  exact partCard

/-- A sunflower in one fixed-rank outside slice lifts through graded fullness. -/
theorem hasResidualSunflower_of_outsideRankGrade
    {alpha : Type}
    [DecidableEq alpha]
    {r k s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : RankCompatibleProductFull F)
    (product : ResidualComponentProduct F)
    (compatible : ProductRankCompatible F product)
    (productRank : product.2.val.card = s)
    (factorSunflower : Concrete.HasSunflower k
      (outsideRankGradeFamily F s)) :
    Concrete.HasSunflower k (PrivateWitnessReduction.residualFamily F) := by
  classical
  rcases factorSunflower with ⟨core, ⟨W⟩⟩
  let outside : Fin k → {outside // outside ∈ outsideComponentFamily F} :=
    fun i => ⟨W.petals i,
      (mem_outsideRankGradeFamily_iff F (W.petals i)).mp
        (W.petals_mem i) |>.1⟩
  let productAt : Fin k → ResidualComponentProduct F :=
    fun i => replaceOutsideProduct F product (outside i)
  let liftedEdge : Fin k → Finset alpha :=
    fun i => assembleComponentCode F (componentCodeOfProduct F (productAt i))
  let fixed := fixedOutsideContext F product
  refine ⟨core ∪ fixed, ⟨{
    petals := liftedEdge
    petals_mem := ?_
    petals_injective := ?_
    pairwise_intersection := ?_ }⟩⟩
  · intro i
    apply assembledProduct_mem_residualFamily_of_rankCompatibleFull F full
    apply replaceOutsideProduct_rankCompatible_of_same_card
      F product compatible (outside i)
    have rankAtI := (outsideRankGradeFamily F s).uniform
      (W.petals i) (W.petals_mem i)
    simpa [outside, productRank] using rankAtI
  · intro i j sameEdge
    apply W.petals_injective
    have sameOutside := congrArg
      (fun edge : Finset alpha => edge \ residualSupport F) sameEdge
    simp only [liftedEdge, productAt] at sameOutside
    rw [assemble_replaceOutsideProduct_sdiff_support F product (outside i),
      assemble_replaceOutsideProduct_sdiff_support F product (outside j)] at sameOutside
    exact sameOutside
  · intro i j distinct
    have leftDisjoint : Disjoint (W.petals i) fixed :=
      outside_disjoint_fixedOutsideContext F product (outside i)
    have rightDisjoint : Disjoint (W.petals j) fixed :=
      outside_disjoint_fixedOutsideContext F product (outside j)
    rw [show liftedEdge i = W.petals i ∪ fixed by
          exact assemble_replaceOutsideProduct F product (outside i),
      show liftedEdge j = W.petals j ∪ fixed by
          exact assemble_replaceOutsideProduct F product (outside j),
      union_fixed_inter_union_fixed
        (W.petals i) (W.petals j) fixed leftDisjoint rightDisjoint,
      W.pairwise_intersection i j distinct]

theorem outsideRankGrade_noSunflower_of_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r k s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (gradeNonempty : (outsideRankGradeFamily F s).edges.Nonempty) :
    Not (Concrete.HasSunflower k (outsideRankGradeFamily F s)) := by
  rcases exists_product_with_outside_rank_of_grade_nonempty
      F gradeNonempty with ⟨product, compatible, productRank⟩
  intro factorSunflower
  exact PrivateWitnessReduction.residualFamily_noSunflower noSunflower
    (hasResidualSunflower_of_outsideRankGrade
      F full product compatible productRank factorSunflower)

/-- Every occupied outside grade is strictly below the residual rank. -/
theorem outsideRankGrade_rank_lt_of_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r s : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (gradeNonempty : (outsideRankGradeFamily F s).edges.Nonempty) :
    s < r + 1 := by
  rcases gradeNonempty with ⟨part, partMem⟩
  have componentMem := (mem_outsideRankGradeFamily_iff F part).mp partMem |>.1
  have partCard := (outsideRankGradeFamily F s).uniform part partMem
  rcases Finset.mem_image.mp componentMem with ⟨edge, edgeMem, samePart⟩
  let residualEdge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} := ⟨edge, edgeMem⟩
  have lower := realizedOutsideComponent_card_lt F residualEdge
  change (edge \ residualSupport F).card < r + 1 at lower
  rw [samePart, partCard] at lower
  exact lower

theorem outsideRankGrade_card_le_of_lowerRankBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k s base : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (full : RankCompatibleProductFull F)
    (lowerRankBound : ∀ t : Nat, t < r + 1 →
      ∀ G : Concrete.UniformSetFamily alpha t,
        Not (Concrete.HasSunflower k G) → G.edges.card ≤ base ^ t) :
    (outsideRankGradeFamily F s).edges.card ≤ base ^ s := by
  by_cases gradeNonempty : (outsideRankGradeFamily F s).edges.Nonempty
  · exact lowerRankBound s
      (outsideRankGrade_rank_lt_of_nonempty F gradeNonempty)
      (outsideRankGradeFamily F s)
      (outsideRankGrade_noSunflower_of_nonempty
        F noSunflower full gradeNonempty)
  · have gradeEmpty : (outsideRankGradeFamily F s).edges = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp gradeNonempty
    simp [gradeEmpty]

/-- Literal product fullness implies fullness of the required rank layer. -/
theorem rankCompatibleProductFull_of_componentProductFull
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (full : ComponentProductFull F) :
    RankCompatibleProductFull F := by
  classical
  change occupiedRankCompatibleProducts F =
    (Finset.univ : Finset (RankCompatibleProduct F))
  apply Finset.eq_univ_iff_forall.mpr
  intro code
  rcases residualProductCode_surjective_of_full F full code.val with
    ⟨edge, sameCode⟩
  exact Finset.mem_image.mpr
    ⟨edge, Finset.mem_univ edge, Subtype.ext sameCode⟩

/--
Raw fullness is exactly graded fullness plus the assertion that every available
tuple already has the required total rank.
-/
theorem componentProductFull_iff_rankCompatibleFull_and_allCompatible
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    ComponentProductFull F ↔
      RankCompatibleProductFull F ∧
        ∀ product : ResidualComponentProduct F,
          ProductRankCompatible F product := by
  classical
  constructor
  · intro full
    exact ⟨rankCompatibleProductFull_of_componentProductFull F full,
      componentProduct_rank_eq_of_full F full⟩
  · rintro ⟨gradedFull, allCompatible⟩
    change occupiedResidualProducts F =
      (Finset.univ : Finset (ResidualComponentProduct F))
    apply Finset.eq_univ_iff_forall.mpr
    intro product
    let compatibleCode : RankCompatibleProduct F :=
      ⟨product, allCompatible product⟩
    have compatibleMem : compatibleCode ∈
        occupiedRankCompatibleProducts F := by
      change occupiedRankCompatibleProducts F =
        (Finset.univ : Finset (RankCompatibleProduct F)) at gradedFull
      rw [gradedFull]
      exact Finset.mem_univ compatibleCode
    rcases Finset.mem_image.mp compatibleMem with
      ⟨edge, _, sameCode⟩
    exact Finset.mem_image.mpr
      ⟨edge, Finset.mem_univ edge, congrArg Subtype.val sameCode⟩

/-- Under graded fullness, every literal missing tuple is missing only by rank. -/
theorem missingCombination_not_rankCompatible_of_gradedFull
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (gradedFull : RankCompatibleProductFull F)
    (missing : MissingComponentCombination F) :
    ¬ ProductRankCompatible F missing.code := by
  classical
  intro compatible
  let compatibleCode : RankCompatibleProduct F := ⟨missing.code, compatible⟩
  have compatibleMem : compatibleCode ∈ occupiedRankCompatibleProducts F := by
    change occupiedRankCompatibleProducts F =
      (Finset.univ : Finset (RankCompatibleProduct F)) at gradedFull
    rw [gradedFull]
    exact Finset.mem_univ compatibleCode
  rcases Finset.mem_image.mp compatibleMem with ⟨edge, _, sameCode⟩
  apply missing.notOccupied
  exact Finset.mem_image.mpr
    ⟨edge, Finset.mem_univ edge, congrArg Subtype.val sameCode⟩

/--
The honest product ledger has three branches: unrestricted tensor fullness,
graded fullness with only wrong-rank omissions, or a genuine same-rank omission.
-/
inductive ProductRankDisposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) : Type
  | full (proof : ComponentProductFull F) : ProductRankDisposition F
  | gradedFullOnly
      (gradedFull : RankCompatibleProductFull F)
      (notFull : ¬ ComponentProductFull F) : ProductRankDisposition F
  | rankCompatibleMissing
      (missing : MissingRankCompatibleCombination F) : ProductRankDisposition F

theorem productRank_disposition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2)) :
    Nonempty (ProductRankDisposition F) := by
  by_cases full : ComponentProductFull F
  · exact ⟨ProductRankDisposition.full full⟩
  · rcases rankCompatibleProductFull_or_missing F with gradedFull | missing
    · exact ⟨ProductRankDisposition.gradedFullOnly gradedFull full⟩
    · rcases missing with ⟨missing⟩
      exact ⟨ProductRankDisposition.rankCompatibleMissing missing⟩

/-- Take the whole component in every matching petal and the empty outside component. -/
noncomputable def matchingDiagonalProduct
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (matchingNonempty : (residualMatching F).matching.petals.Nonempty) :
    ResidualComponentProduct F := by
  classical
  let basePetal : {edge // edge ∈ (residualMatching F).matching.petals} :=
    ⟨Classical.choose matchingNonempty,
      Classical.choose_spec matchingNonempty⟩
  refine
    (fun petal => ⟨petal.val, ?_⟩,
      ⟨∅, ?_⟩)
  · exact Finset.mem_image.mpr
      ⟨petal.val,
        (residualMatching F).matching.petals_subset petal.property, by simp⟩
  · apply Finset.mem_image.mpr
    refine ⟨basePetal.val,
      (residualMatching F).matching.petals_subset basePetal.property, ?_⟩
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    intro y yMem
    exact Finset.mem_biUnion.mpr
      ⟨basePetal.val, basePetal.property, yMem⟩

/-- With two matching petals, the diagonal tuple has rank strictly above the residual rank. -/
theorem matchingDiagonalProduct_not_rankCompatible
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (matchingNonempty : (residualMatching F).matching.petals.Nonempty)
    (twoPetals : 2 ≤ (residualMatching F).matching.petals.card) :
    ¬ ProductRankCompatible F (matchingDiagonalProduct F matchingNonempty) := by
  classical
  have petalCard : ∀ petal :
      {edge // edge ∈ (residualMatching F).matching.petals},
      petal.val.card = r + 1 := by
    intro petal
    exact (PrivateWitnessReduction.residualFamily F).uniform petal.val
      ((residualMatching F).matching.petals_subset petal.property)
  have diagonalRank :
      (componentCodeOfProduct F
        (matchingDiagonalProduct F matchingNonempty)).rank =
        (residualMatching F).matching.petals.card * (r + 1) := by
    rw [ResidualComponentCode.rank, componentCodeOfProduct]
    change (∑ petal : {edge // edge ∈
      (residualMatching F).matching.petals}, petal.val.card) + 0 = _
    simp_rw [petalCard]
    simp
  have twice_le : 2 * (r + 1) ≤
      (residualMatching F).matching.petals.card * (r + 1) :=
    Nat.mul_le_mul_right (r + 1) twoPetals
  have rankLt : r + 1 <
      (residualMatching F).matching.petals.card * (r + 1) := by
    exact lt_of_lt_of_le (by omega) twice_le
  intro compatible
  rw [ProductRankCompatible, diagonalRank] at compatible
  omega

/-- Literal product fullness is impossible once the second matching has two petals. -/
theorem componentProduct_not_full_of_two_matchingPetals
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (matchingNonempty : (residualMatching F).matching.petals.Nonempty)
    (twoPetals : 2 ≤ (residualMatching F).matching.petals.card) :
    ¬ ComponentProductFull F := by
  intro full
  exact matchingDiagonalProduct_not_rankCompatible F matchingNonempty twoPetals
    (componentProduct_rank_eq_of_full F full
      (matchingDiagonalProduct F matchingNonempty))

/-- The slot-cardinality sum is exactly the component-code rank. -/
theorem productComponentCardSum_eq_rank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F) :
    (∑ slot : GateSlot F,
      (productComponentAt F product slot).card) =
      (componentCodeOfProduct F product).rank := by
  classical
  simp [GateSlot, Fintype.sum_option, productComponentAt,
    componentCodeOfProduct, ResidualComponentCode.rank, Nat.add_comm]

/-- Equal total card-sums and unequal component functions force a nonempty left disagreement. -/
theorem exists_nonempty_disagreement_of_sum_card_eq
    {ι beta : Type}
    [Fintype ι]
    [DecidableEq ι]
    [DecidableEq beta]
    (left right : ι → Finset beta)
    (sameTotal : (∑ i : ι, (left i).card) =
      ∑ i : ι, (right i).card)
    (distinct : left ≠ right) :
    ∃ i : ι, left i ≠ right i ∧ (left i).Nonempty := by
  classical
  have someDisagreement : ∃ i : ι, left i ≠ right i := by
    by_contra noDisagreement
    push_neg at noDisagreement
    exact distinct (funext noDisagreement)
  by_contra noWitness
  push_neg at noWitness
  have leftSubsetRight : ∀ i : ι, left i ⊆ right i := by
    intro i y yMem
    by_cases same : left i = right i
    · simpa [same] using yMem
    · rw [noWitness i same] at yMem
      simp at yMem
  rcases someDisagreement with ⟨i, differs⟩
  have leftEmpty : left i = ∅ := by
    exact noWitness i differs
  have rightNonempty : (right i).Nonempty := by
    by_contra rightNotNonempty
    have rightEmpty : right i = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp rightNotNonempty
    exact differs (leftEmpty.trans rightEmpty.symm)
  have strictAt : (left i).card < (right i).card := by
    simpa [leftEmpty] using Finset.card_pos.mpr rightNonempty
  have strictTotal : (∑ j : ι, (left j).card) <
      ∑ j : ι, (right j).card := by
    apply Finset.sum_lt_sum
    · intro j _
      exact Finset.card_le_card (leftSubsetRight j)
    · exact ⟨i, Finset.mem_univ i, strictAt⟩
  exact (Nat.ne_of_lt strictTotal) sameTotal

/-- Every realized code differs from a missing compatible tuple at a rank-spending slot. -/
theorem realizedCode_has_rankSpendingDisagreement
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    ∃ slot : GateSlot F,
      productComponentAt F (residualProductCode F edge) slot ≠
          productComponentAt F missing.code.val slot ∧
        (productComponentAt F (residualProductCode F edge) slot).Nonempty := by
  classical
  let realized : GateSlot F → Finset alpha :=
    productComponentAt F (residualProductCode F edge)
  let absent : GateSlot F → Finset alpha :=
    productComponentAt F missing.code.val
  have sameTotal : (∑ slot : GateSlot F, (realized slot).card) =
      ∑ slot : GateSlot F, (absent slot).card := by
    calc
      (∑ slot : GateSlot F, (realized slot).card) =
          (componentCodeOfProduct F (residualProductCode F edge)).rank := by
        simpa [realized] using
          productComponentCardSum_eq_rank F (residualProductCode F edge)
      _ = r + 1 := (residualRankCompatibleProductCode F edge).property
      _ = (componentCodeOfProduct F missing.code.val).rank :=
        missing.code.property.symm
      _ = ∑ slot : GateSlot F, (absent slot).card := by
        symm
        simpa [absent] using productComponentCardSum_eq_rank F missing.code.val
  have distinct : realized ≠ absent := by
    intro sameFunctions
    rcases realizedCode_has_gateDisagreement F
        missing.toMissingCombination edge with ⟨slot, differs⟩
    exact differs (congrFun sameFunctions slot)
  simpa [realized, absent] using
    exists_nonempty_disagreement_of_sum_card_eq
      realized absent sameTotal distinct

/-- Choose a disagreement that spends at least one realized rank unit. -/
noncomputable def rankSpendingGateSlot
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) : GateSlot F :=
  Classical.choose (realizedCode_has_rankSpendingDisagreement F missing edge)

theorem rankSpendingGateSlot_spec
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    productComponentAt F (residualProductCode F edge)
          (rankSpendingGateSlot F missing edge) ≠
        productComponentAt F missing.code.val
          (rankSpendingGateSlot F missing edge) ∧
      (productComponentAt F (residualProductCode F edge)
        (rankSpendingGateSlot F missing edge)).Nonempty :=
  Classical.choose_spec
    (realizedCode_has_rankSpendingDisagreement F missing edge)

/-- The rank stored in all component slots except one selected gate. -/
noncomputable def productSiblingRank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (slot : GateSlot F) : Nat :=
  ∑ sibling ∈ (Finset.univ.erase slot),
    (productComponentAt F product sibling).card

theorem selectedCard_add_siblingRank_eq_rank
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (product : ResidualComponentProduct F)
    (slot : GateSlot F) :
    (productComponentAt F product slot).card +
        productSiblingRank F product slot =
      (componentCodeOfProduct F product).rank := by
  classical
  calc
    (productComponentAt F product slot).card +
        productSiblingRank F product slot =
      ∑ sibling : GateSlot F,
        (productComponentAt F product sibling).card := by
      exact Finset.add_sum_erase Finset.univ
        (fun sibling => (productComponentAt F product sibling).card)
        (Finset.mem_univ slot)
    _ = (componentCodeOfProduct F product).rank :=
      productComponentCardSum_eq_rank F product

/-- The complementary context of the selected rank-spending gate is strictly lower rank. -/
theorem rankSpendingGateSlot_siblingRank_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    productSiblingRank F (residualProductCode F edge)
      (rankSpendingGateSlot F missing edge) < r + 1 := by
  have positive : 0 <
      (productComponentAt F (residualProductCode F edge)
        (rankSpendingGateSlot F missing edge)).card :=
    Finset.card_pos.mpr (rankSpendingGateSlot_spec F missing edge).2
  have rankSplit := selectedCard_add_siblingRank_eq_rank F
    (residualProductCode F edge) (rankSpendingGateSlot F missing edge)
  have realizedRank :
      (componentCodeOfProduct F (residualProductCode F edge)).rank = r + 1 :=
    (residualRankCompatibleProductCode F edge).property
  omega

/-- The residuals assigned to one selected rank-spending disagreement slot. -/
noncomputable def rankSpendingGateFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  Finset.univ.filter fun edge => rankSpendingGateSlot F missing edge = slot

theorem mem_rankSpendingGateFiber_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    edge ∈ rankSpendingGateFiber F missing slot ↔
      rankSpendingGateSlot F missing edge = slot := by
  simp [rankSpendingGateFiber]

theorem rankSpendingGateFiber_selected_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (edgeMem : edge ∈ rankSpendingGateFiber F missing slot) :
    (productComponentAt F (residualProductCode F edge) slot).Nonempty := by
  have sameSlot := (mem_rankSpendingGateFiber_iff F missing slot edge).mp edgeMem
  simpa [sameSlot] using (rankSpendingGateSlot_spec F missing edge).2

theorem rankSpendingGateFiber_siblingRank_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (edgeMem : edge ∈ rankSpendingGateFiber F missing slot) :
    productSiblingRank F (residualProductCode F edge) slot < r + 1 := by
  have sameSlot := (mem_rankSpendingGateFiber_iff F missing slot edge).mp edgeMem
  simpa [sameSlot] using rankSpendingGateSlot_siblingRank_lt F missing edge

/-- A same-rank missing tuple still has only the boundedly many matching/outside gates. -/
theorem exists_large_rankSpendingGateFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r k t : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingRankCompatibleCombination F)
    (oversized : k * t <
      (PrivateWitnessReduction.residualFamily F).edges.card) :
    ∃ slot : GateSlot F,
      t < (rankSpendingGateFiber F missing slot).card := by
  classical
  have slotBound : Fintype.card (GateSlot F) ≤ k :=
    gateSlot_card_le F noSunflower
  have productLt : Fintype.card (GateSlot F) * t <
      Fintype.card {edge // edge ∈
        (PrivateWitnessReduction.residualFamily F).edges} := by
    rw [Fintype.card_coe]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right t slotBound) oversized
  rcases Fintype.exists_lt_card_fiber_of_mul_lt_card
      (rankSpendingGateSlot F missing) productLt with ⟨slot, large⟩
  refine ⟨slot, ?_⟩
  simpa [rankSpendingGateFiber] using large

/-- The strict selected-rank part of a rank-spending gate fibre. -/
noncomputable def lowerRankSpendingGateFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  (rankSpendingGateFiber F missing slot).filter fun edge =>
    (productComponentAt F (residualProductCode F edge) slot).card < r + 1

/-- The complementary full-selected-rank exception set. -/
noncomputable def fullRankSpendingGateFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    Finset {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges} :=
  (rankSpendingGateFiber F missing slot).filter fun edge =>
    ¬ (productComponentAt F (residualProductCode F edge) slot).card < r + 1

theorem rankSpendingGateFiber_rank_partition
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    (lowerRankSpendingGateFiber F missing slot).card +
        (fullRankSpendingGateFiber F missing slot).card =
      (rankSpendingGateFiber F missing slot).card := by
  classical
  simpa [lowerRankSpendingGateFiber, fullRankSpendingGateFiber] using
    (Finset.card_filter_add_card_filter_not
      (s := rankSpendingGateFiber F missing slot)
      (fun edge =>
        (productComponentAt F (residualProductCode F edge) slot).card < r + 1))

theorem fullRankSpendingGateFiber_subset_fullRankGateEdges
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    fullRankSpendingGateFiber F missing slot ⊆ fullRankGateEdges F slot := by
  intro edge edgeMem
  have notLower := (Finset.mem_filter.mp edgeMem).2
  apply (mem_fullRankGateEdges_iff F slot edge).mpr
  have atMost := realizedComponent_card_le F edge slot
  omega

/-- At most one edge at a rank-spending gate can consume the whole rank. -/
theorem fullRankSpendingGateFiber_card_le_one
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    (fullRankSpendingGateFiber F missing slot).card ≤ 1 :=
  (Finset.card_le_card
    (fullRankSpendingGateFiber_subset_fullRankGateEdges F missing slot)).trans
      (fullRankGateEdges_card_le_one F slot)

theorem rankSpendingGateFiber_card_le_lowerRank_succ
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    (rankSpendingGateFiber F missing slot).card ≤
      (lowerRankSpendingGateFiber F missing slot).card + 1 := by
  have partition := rankSpendingGateFiber_rank_partition F missing slot
  have exceptional := fullRankSpendingGateFiber_card_le_one F missing slot
  omega

/-- Oversize in a same-rank missing branch reaches a strict binary-rank gate fibre. -/
theorem exists_large_lowerRankSpendingGateFiber
    {alpha : Type}
    [DecidableEq alpha]
    {r k t : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingRankCompatibleCombination F)
    (oversized : k * (t + 1) <
      (PrivateWitnessReduction.residualFamily F).edges.card) :
    ∃ slot : GateSlot F,
      t < (lowerRankSpendingGateFiber F missing slot).card := by
  rcases exists_large_rankSpendingGateFiber F noSunflower missing oversized with
    ⟨slot, large⟩
  refine ⟨slot, ?_⟩
  have branchBound :=
    rankSpendingGateFiber_card_le_lowerRank_succ F missing slot
  omega

/-- A bound on every strict binary-rank gate fibre bounds the whole same-rank omission. -/
theorem residualFamily_card_le_of_lowerRankSpendingGateFiberBound
    {alpha : Type}
    [DecidableEq alpha]
    {r k M : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingRankCompatibleCombination F)
    (fiberBound : ∀ slot : GateSlot F,
      (lowerRankSpendingGateFiber F missing slot).card ≤ M) :
    (PrivateWitnessReduction.residualFamily F).edges.card ≤ k * (M + 1) := by
  by_contra notBounded
  have oversized : k * (M + 1) <
      (PrivateWitnessReduction.residualFamily F).edges.card :=
    Nat.lt_of_not_ge notBounded
  rcases exists_large_lowerRankSpendingGateFiber
      F noSunflower missing oversized with ⟨slot, large⟩
  exact (Nat.not_lt_of_ge (fiberBound slot)) large

/-- Every nonexceptional assigned edge splits into two positive strict lower ranks. -/
theorem lowerRankSpendingGateFiber_strict_binary_rank_split
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (edgeMem : edge ∈ lowerRankSpendingGateFiber F missing slot) :
    0 < (productComponentAt F (residualProductCode F edge) slot).card ∧
      (productComponentAt F (residualProductCode F edge) slot).card < r + 1 ∧
      0 < productSiblingRank F (residualProductCode F edge) slot ∧
      productSiblingRank F (residualProductCode F edge) slot < r + 1 ∧
      (productComponentAt F (residualProductCode F edge) slot).card +
          productSiblingRank F (residualProductCode F edge) slot = r + 1 := by
  have fiberMem := (Finset.mem_filter.mp edgeMem).1
  have selectedLower := (Finset.mem_filter.mp edgeMem).2
  have selectedPositive := Finset.card_pos.mpr
    (rankSpendingGateFiber_selected_nonempty F missing slot edge fiberMem)
  have siblingLower :=
    rankSpendingGateFiber_siblingRank_lt F missing slot edge fiberMem
  have rankSplit := selectedCard_add_siblingRank_eq_rank F
    (residualProductCode F edge) slot
  have realizedRank :
      (componentCodeOfProduct F (residualProductCode F edge)).rank = r + 1 :=
    (residualRankCompatibleProductCode F edge).property
  have siblingPositive :
      0 < productSiblingRank F (residualProductCode F edge) slot := by
    omega
  exact ⟨selectedPositive, selectedLower, siblingPositive, siblingLower, by omega⟩

/-- The selected component and normalized sibling context reconstruct an edge. -/
noncomputable def rankSpendingSplitCode
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} →
      Finset alpha × ResidualComponentProduct F :=
  fun edge =>
    (productComponentAt F (residualProductCode F edge) slot,
      normalizeProductAtSlot F missing.code.val slot
        (residualProductCode F edge))

theorem rankSpendingSplitCode_injective
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (missing : MissingRankCompatibleCombination F)
    (slot : GateSlot F) :
    Function.Injective (rankSpendingSplitCode F missing slot) := by
  intro left right sameCode
  apply residualProductCode_injective F
  apply product_eq_of_normalize_eq_of_component_eq
    F missing.code.val (residualProductCode F left)
      (residualProductCode F right) slot
  · exact congrArg Prod.snd sameCode
  · exact congrArg Prod.fst sameCode

end RankCompatibleProductGate
end V2
end SunflowerAASC
