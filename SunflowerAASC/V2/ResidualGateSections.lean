import SunflowerAASC.V2.ResidualVennPincer

namespace SunflowerAASC
namespace V2
namespace ResidualGateSections

open ResidualVennPincer

/-- Two realized residual products agree on every matching-petal component. -/
def OutsideContextAgrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) : Prop :=
  ∀ petal : {edge // edge ∈ (residualMatching F).matching.petals},
    (residualProductCode F edge).1 petal =
      (residualProductCode F base).1 petal

/-- Outside components realized while every matching-petal component is fixed. -/
noncomputable def outsideSectionComponents
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    Finset (Finset alpha) := by
  classical
  exact
    ((Finset.univ : Finset {edge // edge ∈
        (PrivateWitnessReduction.residualFamily F).edges}).filter
          (OutsideContextAgrees F base)).image
      (fun edge => (residualProductCode F edge).2.val)

theorem mem_outsideSectionComponents_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (part : Finset alpha) :
    part ∈ outsideSectionComponents F base ↔
      ∃ edge : {edge // edge ∈
          (PrivateWitnessReduction.residualFamily F).edges},
        OutsideContextAgrees F base edge ∧
          (residualProductCode F edge).2.val = part := by
  classical
  rw [outsideSectionComponents]
  constructor
  · intro part_mem
    rcases Finset.mem_image.mp part_mem with ⟨edge, edge_mem, samePart⟩
    exact ⟨edge, (Finset.mem_filter.mp edge_mem).2, samePart⟩
  · rintro ⟨edge, agrees, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ edge, agrees⟩, rfl⟩

theorem outsideSectionComponents_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    (outsideSectionComponents F base).Nonempty := by
  refine ⟨(residualProductCode F base).2.val, ?_⟩
  apply (mem_outsideSectionComponents_iff F base _).mpr
  exact ⟨base, fun _ => rfl, rfl⟩

/-- Choose a realized residual representing one outside-section component. -/
noncomputable def outsideSectionRepresentative
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (part : {part // part ∈ outsideSectionComponents F base}) :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} :=
  Classical.choose ((mem_outsideSectionComponents_iff F base part.val).mp part.property)

theorem outsideSectionRepresentative_agrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (part : {part // part ∈ outsideSectionComponents F base}) :
    OutsideContextAgrees F base (outsideSectionRepresentative F base part) :=
  (Classical.choose_spec
    ((mem_outsideSectionComponents_iff F base part.val).mp part.property)).1

theorem outsideSectionRepresentative_outside
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (part : {part // part ∈ outsideSectionComponents F base}) :
    (residualProductCode F (outsideSectionRepresentative F base part)).2.val =
      part.val :=
  (Classical.choose_spec
    ((mem_outsideSectionComponents_iff F base part.val).mp part.property)).2

theorem outsideSectionComponent_mem_outsideFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (part : {part // part ∈ outsideSectionComponents F base}) :
    part.val ∈ outsideComponentFamily F := by
  let edge := outsideSectionRepresentative F base part
  have sameOutside := outsideSectionRepresentative_outside F base part
  apply Finset.mem_image.mpr
  refine ⟨edge.val, edge.property, ?_⟩
  simpa [residualProductCode] using sameOutside

theorem residualProductCode_eq_replaceOutside_of_agrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (agrees : OutsideContextAgrees F base edge) :
    residualProductCode F edge =
      replaceOutsideProduct F (residualProductCode F base)
        ⟨(residualProductCode F edge).2.val,
          (residualProductCode F edge).2.property⟩ := by
  apply Prod.ext
  · funext petal
    exact agrees petal
  · apply Subtype.ext
    rfl

theorem edge_eq_outside_union_fixedContext_of_agrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (agrees : OutsideContextAgrees F base edge) :
    edge.val = (residualProductCode F edge).2.val ∪
      fixedOutsideContext F (residualProductCode F base) := by
  let outside : {outside // outside ∈ outsideComponentFamily F} :=
    ⟨(residualProductCode F edge).2.val,
      (residualProductCode F edge).2.property⟩
  have sameProduct := residualProductCode_eq_replaceOutside_of_agrees
    F base edge agrees
  calc
    edge.val = assembleComponentCode F
        (componentCodeOfProduct F (residualProductCode F edge)) := by
      rw [componentCodeOfProduct_residualProductCode,
        assemble_componentCodeOfEdge]
    _ = assembleComponentCode F
        (componentCodeOfProduct F
          (replaceOutsideProduct F (residualProductCode F base) outside)) := by
      exact congrArg (fun product =>
        assembleComponentCode F (componentCodeOfProduct F product)) sameProduct
    _ = outside.val ∪ fixedOutsideContext F (residualProductCode F base) :=
      assemble_replaceOutsideProduct F (residualProductCode F base) outside

/-- A context-fixed outside section is an honest uniform family. -/
noncomputable def outsideSectionFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    Concrete.UniformSetFamily alpha (residualProductCode F base).2.val.card where
  edges := outsideSectionComponents F base
  uniform := by
    intro part part_mem
    let selected : {part // part ∈ outsideSectionComponents F base} :=
      ⟨part, part_mem⟩
    let edge := outsideSectionRepresentative F base selected
    let fixed := fixedOutsideContext F (residualProductCode F base)
    let selectedOutside : {outside // outside ∈ outsideComponentFamily F} :=
      ⟨part, outsideSectionComponent_mem_outsideFamily F base selected⟩
    let baseOutside : {outside // outside ∈ outsideComponentFamily F} :=
      (residualProductCode F base).2
    have edgeEq : edge.val = part ∪ fixed := by
      have eq := edge_eq_outside_union_fixedContext_of_agrees
        F base edge (outsideSectionRepresentative_agrees F base selected)
      rw [outsideSectionRepresentative_outside F base selected] at eq
      exact eq
    have baseEq : base.val = baseOutside.val ∪ fixed := by
      simpa [baseOutside, fixed] using
        edge_eq_outside_union_fixedContext_of_agrees F base base (fun _ => rfl)
    have selectedDisjoint : Disjoint part fixed := by
      simpa [selectedOutside, fixed] using
        outside_disjoint_fixedOutsideContext
          F (residualProductCode F base) selectedOutside
    have baseDisjoint : Disjoint baseOutside.val fixed := by
      simpa [baseOutside, fixed] using
        outside_disjoint_fixedOutsideContext
          F (residualProductCode F base) baseOutside
    have selectedTotal : part.card + fixed.card = r + 1 := by
      rw [← Finset.card_union_of_disjoint selectedDisjoint, ← edgeEq]
      exact (PrivateWitnessReduction.residualFamily F).uniform edge.val edge.property
    have baseTotal : baseOutside.val.card + fixed.card = r + 1 := by
      rw [← Finset.card_union_of_disjoint baseDisjoint, ← baseEq]
      exact (PrivateWitnessReduction.residualFamily F).uniform base.val base.property
    have baseTotal' :
        (residualProductCode F base).2.val.card + fixed.card = r + 1 := by
      simpa [baseOutside] using baseTotal
    omega

/-- Every context-fixed outside section has strictly lower rank. -/
theorem outsideSectionFactor_rank_lt
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    (residualProductCode F base).2.val.card < r + 1 :=
  realizedOutsideComponent_card_lt F base

/-- A sunflower in a realized outside section lifts to the residual family. -/
theorem hasResidualSunflower_of_outsideSection
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (sectionSunflower : Concrete.HasSunflower k (outsideSectionFactor F base)) :
    Concrete.HasSunflower k (PrivateWitnessReduction.residualFamily F) := by
  classical
  rcases sectionSunflower with ⟨core, ⟨W⟩⟩
  let part : Fin k -> {part // part ∈ outsideSectionComponents F base} :=
    fun i => ⟨W.petals i, W.petals_mem i⟩
  let lifted : Fin k ->
      {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} :=
    fun i => outsideSectionRepresentative F base (part i)
  let fixed := fixedOutsideContext F (residualProductCode F base)
  refine ⟨core ∪ fixed, ⟨{
    petals := fun i => (lifted i).val
    petals_mem := fun i => (lifted i).property
    petals_injective := ?_
    pairwise_intersection := ?_ }⟩⟩
  · intro i j sameEdge
    apply W.petals_injective
    have sameOutside := congrArg
      (fun edge : Finset alpha => edge \ residualSupport F) sameEdge
    change (lifted i).val \ residualSupport F =
      (lifted j).val \ residualSupport F at sameOutside
    rw [show (lifted i).val \ residualSupport F = W.petals i by
          simpa [lifted, part, residualProductCode] using
            outsideSectionRepresentative_outside F base (part i),
        show (lifted j).val \ residualSupport F = W.petals j by
          simpa [lifted, part, residualProductCode] using
            outsideSectionRepresentative_outside F base (part j)] at sameOutside
    exact sameOutside
  · intro i j distinct
    let leftOutside : {outside // outside ∈ outsideComponentFamily F} :=
      ⟨W.petals i, outsideSectionComponent_mem_outsideFamily F base (part i)⟩
    let rightOutside : {outside // outside ∈ outsideComponentFamily F} :=
      ⟨W.petals j, outsideSectionComponent_mem_outsideFamily F base (part j)⟩
    have leftEq : (lifted i).val = W.petals i ∪ fixed := by
      have eq := edge_eq_outside_union_fixedContext_of_agrees
        F base (lifted i) (outsideSectionRepresentative_agrees F base (part i))
      rw [outsideSectionRepresentative_outside F base (part i)] at eq
      exact eq
    have rightEq : (lifted j).val = W.petals j ∪ fixed := by
      have eq := edge_eq_outside_union_fixedContext_of_agrees
        F base (lifted j) (outsideSectionRepresentative_agrees F base (part j))
      rw [outsideSectionRepresentative_outside F base (part j)] at eq
      exact eq
    have leftDisjoint : Disjoint (W.petals i) fixed := by
      simpa [leftOutside, fixed] using
        outside_disjoint_fixedOutsideContext
          F (residualProductCode F base) leftOutside
    have rightDisjoint : Disjoint (W.petals j) fixed := by
      simpa [rightOutside, fixed] using
        outside_disjoint_fixedOutsideContext
          F (residualProductCode F base) rightOutside
    rw [leftEq, rightEq,
      union_fixed_inter_union_fixed
        (W.petals i) (W.petals j) fixed leftDisjoint rightDisjoint,
      W.pairwise_intersection i j distinct]

theorem outsideSectionFactor_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    Not (Concrete.HasSunflower k (outsideSectionFactor F base)) :=
  fun sectionSunflower =>
    PrivateWitnessReduction.residualFamily_noSunflower noSunflower <|
      hasResidualSunflower_of_outsideSection F base sectionSunflower

theorem baseOutside_mem_outsideSectionFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) :
    (residualProductCode F base).2.val ∈
      (outsideSectionFactor F base).edges := by
  apply (mem_outsideSectionComponents_iff F base _).mpr
  exact ⟨base, fun _ => rfl, rfl⟩

/-- Two realized residual products agree away from one selected petal slot. -/
def PetalContextAgrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges}) : Prop :=
  (∀ sibling : {edge // edge ∈ (residualMatching F).matching.petals},
      sibling ≠ petal →
        (residualProductCode F edge).1 sibling =
          (residualProductCode F base).1 sibling) ∧
    (residualProductCode F edge).2 = (residualProductCode F base).2

/-- Petal components realized while every other component is fixed. -/
noncomputable def petalSectionComponents
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Finset (Finset alpha) := by
  classical
  exact
    ((Finset.univ : Finset {edge // edge ∈
        (PrivateWitnessReduction.residualFamily F).edges}).filter
          (PetalContextAgrees F base petal)).image
      (fun edge => ((residualProductCode F edge).1 petal).val)

theorem mem_petalSectionComponents_iff
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : Finset alpha) :
    part ∈ petalSectionComponents F base petal ↔
      ∃ edge : {edge // edge ∈
          (PrivateWitnessReduction.residualFamily F).edges},
        PetalContextAgrees F base petal edge ∧
          ((residualProductCode F edge).1 petal).val = part := by
  classical
  rw [petalSectionComponents]
  constructor
  · intro part_mem
    rcases Finset.mem_image.mp part_mem with ⟨edge, edge_mem, samePart⟩
    exact ⟨edge, (Finset.mem_filter.mp edge_mem).2, samePart⟩
  · rintro ⟨edge, agrees, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ edge, agrees⟩, rfl⟩

theorem petalSectionComponents_nonempty
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    (petalSectionComponents F base petal).Nonempty := by
  refine ⟨((residualProductCode F base).1 petal).val, ?_⟩
  apply (mem_petalSectionComponents_iff F base petal _).mpr
  exact ⟨base, ⟨fun _ _ => rfl, rfl⟩, rfl⟩

/-- Choose a realized residual representing one petal-section component. -/
noncomputable def petalSectionRepresentative
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalSectionComponents F base petal}) :
    {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} :=
  Classical.choose
    ((mem_petalSectionComponents_iff F base petal part.val).mp part.property)

theorem petalSectionRepresentative_agrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalSectionComponents F base petal}) :
    PetalContextAgrees F base petal
      (petalSectionRepresentative F base petal part) :=
  (Classical.choose_spec
    ((mem_petalSectionComponents_iff F base petal part.val).mp part.property)).1

theorem petalSectionRepresentative_selected
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalSectionComponents F base petal}) :
    ((residualProductCode F
      (petalSectionRepresentative F base petal part)).1 petal).val = part.val :=
  (Classical.choose_spec
    ((mem_petalSectionComponents_iff F base petal part.val).mp part.property)).2

theorem petalSectionComponent_mem_petalFamily
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (part : {part // part ∈ petalSectionComponents F base petal}) :
    part.val ∈ petalComponentFamily F petal := by
  let edge := petalSectionRepresentative F base petal part
  have selected := petalSectionRepresentative_selected F base petal part
  apply Finset.mem_image.mpr
  refine ⟨edge.val, edge.property, ?_⟩
  simpa [residualProductCode] using selected

theorem residualProductCode_eq_replacePetal_of_agrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (agrees : PetalContextAgrees F base petal edge) :
    residualProductCode F edge =
      replacePetalProduct F (residualProductCode F base) petal
        ⟨((residualProductCode F edge).1 petal).val,
          ((residualProductCode F edge).1 petal).property⟩ := by
  apply Prod.ext
  · funext sibling
    by_cases same : sibling = petal
    · subst sibling
      simp [replacePetalProduct]
    · simpa [replacePetalProduct, Function.update, same] using agrees.1 sibling same
  · simpa [replacePetalProduct] using agrees.2

theorem edge_eq_petal_union_fixedContext_of_agrees
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (agrees : PetalContextAgrees F base petal edge) :
    edge.val = ((residualProductCode F edge).1 petal).val ∪
      fixedPetalContext F (residualProductCode F base) petal := by
  let part : {part // part ∈ petalComponentFamily F petal} :=
    ⟨((residualProductCode F edge).1 petal).val,
      ((residualProductCode F edge).1 petal).property⟩
  have sameProduct := residualProductCode_eq_replacePetal_of_agrees
    F base edge petal agrees
  calc
    edge.val = assembleComponentCode F
        (componentCodeOfProduct F (residualProductCode F edge)) := by
      rw [componentCodeOfProduct_residualProductCode,
        assemble_componentCodeOfEdge]
    _ = assembleComponentCode F
        (componentCodeOfProduct F
          (replacePetalProduct F (residualProductCode F base) petal part)) := by
      exact congrArg (fun product =>
        assembleComponentCode F (componentCodeOfProduct F product)) sameProduct
    _ = part.val ∪
        fixedPetalContext F (residualProductCode F base) petal :=
      assemble_replacePetalProduct F (residualProductCode F base) petal part

/-- A context-fixed petal section is an honest uniform family. -/
noncomputable def petalSectionFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Concrete.UniformSetFamily alpha
      ((residualProductCode F base).1 petal).val.card where
  edges := petalSectionComponents F base petal
  uniform := by
    intro selectedPart selectedMem
    let selected : {part // part ∈ petalSectionComponents F base petal} :=
      ⟨selectedPart, selectedMem⟩
    let edge := petalSectionRepresentative F base petal selected
    let fixed := fixedPetalContext F (residualProductCode F base) petal
    let selectedComponent : {part // part ∈ petalComponentFamily F petal} :=
      ⟨selectedPart, petalSectionComponent_mem_petalFamily F base petal selected⟩
    let baseComponent : {part // part ∈ petalComponentFamily F petal} :=
      (residualProductCode F base).1 petal
    have edgeEq : edge.val = selectedPart ∪ fixed := by
      have eq := edge_eq_petal_union_fixedContext_of_agrees
        F base edge petal (petalSectionRepresentative_agrees F base petal selected)
      rw [petalSectionRepresentative_selected F base petal selected] at eq
      exact eq
    have baseEq : base.val = baseComponent.val ∪ fixed := by
      simpa [baseComponent, fixed] using
        edge_eq_petal_union_fixedContext_of_agrees
          F base base petal ⟨fun _ _ => rfl, rfl⟩
    have contextDisjoint :=
      fixedPetalContext_disjoint F (residualProductCode F base) petal
    have selectedDisjoint : Disjoint selectedPart fixed := by
      exact contextDisjoint.mono_left
        (petalComponent_subset_petal F petal selectedComponent)
    have baseDisjoint : Disjoint baseComponent.val fixed := by
      exact contextDisjoint.mono_left
        (petalComponent_subset_petal F petal baseComponent)
    have selectedTotal : selectedPart.card + fixed.card = r + 1 := by
      rw [← Finset.card_union_of_disjoint selectedDisjoint, ← edgeEq]
      exact (PrivateWitnessReduction.residualFamily F).uniform edge.val edge.property
    have baseTotal : baseComponent.val.card + fixed.card = r + 1 := by
      rw [← Finset.card_union_of_disjoint baseDisjoint, ← baseEq]
      exact (PrivateWitnessReduction.residualFamily F).uniform base.val base.property
    have baseTotal' :
        ((residualProductCode F base).1 petal).val.card + fixed.card = r + 1 := by
      simpa [baseComponent] using baseTotal
    omega

theorem hasResidualSunflower_of_petalSection
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals})
    (sectionSunflower : Concrete.HasSunflower k
      (petalSectionFactor F base petal)) :
    Concrete.HasSunflower k (PrivateWitnessReduction.residualFamily F) := by
  classical
  rcases sectionSunflower with ⟨core, ⟨W⟩⟩
  let part : Fin k -> {part // part ∈ petalSectionComponents F base petal} :=
    fun i => ⟨W.petals i, W.petals_mem i⟩
  let lifted : Fin k ->
      {edge // edge ∈ (PrivateWitnessReduction.residualFamily F).edges} :=
    fun i => petalSectionRepresentative F base petal (part i)
  let fixed := fixedPetalContext F (residualProductCode F base) petal
  refine ⟨core ∪ fixed, ⟨{
    petals := fun i => (lifted i).val
    petals_mem := fun i => (lifted i).property
    petals_injective := ?_
    pairwise_intersection := ?_ }⟩⟩
  · intro i j sameEdge
    apply W.petals_injective
    have sameIntersection := congrArg
      (fun edge : Finset alpha => edge ∩ petal.val) sameEdge
    change (lifted i).val ∩ petal.val =
      (lifted j).val ∩ petal.val at sameIntersection
    rw [show (lifted i).val ∩ petal.val = W.petals i by
          simpa [lifted, part, residualProductCode] using
            petalSectionRepresentative_selected F base petal (part i),
        show (lifted j).val ∩ petal.val = W.petals j by
          simpa [lifted, part, residualProductCode] using
            petalSectionRepresentative_selected F base petal (part j)] at sameIntersection
    exact sameIntersection
  · intro i j distinct
    let leftComponent : {part // part ∈ petalComponentFamily F petal} :=
      ⟨W.petals i, petalSectionComponent_mem_petalFamily F base petal (part i)⟩
    let rightComponent : {part // part ∈ petalComponentFamily F petal} :=
      ⟨W.petals j, petalSectionComponent_mem_petalFamily F base petal (part j)⟩
    have leftEq : (lifted i).val = W.petals i ∪ fixed := by
      have eq := edge_eq_petal_union_fixedContext_of_agrees
        F base (lifted i) petal
          (petalSectionRepresentative_agrees F base petal (part i))
      rw [petalSectionRepresentative_selected F base petal (part i)] at eq
      exact eq
    have rightEq : (lifted j).val = W.petals j ∪ fixed := by
      have eq := edge_eq_petal_union_fixedContext_of_agrees
        F base (lifted j) petal
          (petalSectionRepresentative_agrees F base petal (part j))
      rw [petalSectionRepresentative_selected F base petal (part j)] at eq
      exact eq
    have contextDisjoint :=
      fixedPetalContext_disjoint F (residualProductCode F base) petal
    have leftDisjoint : Disjoint (W.petals i) fixed := by
      exact contextDisjoint.mono_left
        (petalComponent_subset_petal F petal leftComponent)
    have rightDisjoint : Disjoint (W.petals j) fixed := by
      exact contextDisjoint.mono_left
        (petalComponent_subset_petal F petal rightComponent)
    rw [leftEq, rightEq,
      union_fixed_inter_union_fixed
        (W.petals i) (W.petals j) fixed leftDisjoint rightDisjoint,
      W.pairwise_intersection i j distinct]

theorem petalSectionFactor_noSunflower
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    Not (Concrete.HasSunflower k (petalSectionFactor F base petal)) :=
  fun sectionSunflower =>
    PrivateWitnessReduction.residualFamily_noSunflower noSunflower <|
      hasResidualSunflower_of_petalSection F base petal sectionSunflower

theorem basePetal_mem_petalSectionFactor
    {alpha : Type}
    [DecidableEq alpha]
    {r : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (base : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (petal : {edge // edge ∈ (residualMatching F).matching.petals}) :
    ((residualProductCode F base).1 petal).val ∈
      (petalSectionFactor F base petal).edges := by
  apply (mem_petalSectionComponents_iff F base petal _).mpr
  exact ⟨base, ⟨fun _ _ => rfl, rfl⟩, rfl⟩

/--
Every realized lower-rank gate component lies in an honest lower-rank,
sunflower-free uniform section through the residual that realizes it.
-/
theorem exists_lowerRank_noSunflower_section_at_slot
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (slot : GateSlot F)
    (lowerRank :
      (productComponentAt F (residualProductCode F edge) slot).card < r + 1) :
    ∃ n : Nat, n < r + 1 ∧
      ∃ S : Concrete.UniformSetFamily alpha n,
        Not (Concrete.HasSunflower k S) ∧
          productComponentAt F (residualProductCode F edge) slot ∈
            S.edges := by
  cases slot with
  | none =>
      refine ⟨(residualProductCode F edge).2.val.card, ?_,
        outsideSectionFactor F edge, ?_, ?_⟩
      · simpa [productComponentAt] using lowerRank
      · exact outsideSectionFactor_noSunflower F noSunflower edge
      · simpa [productComponentAt] using baseOutside_mem_outsideSectionFactor F edge
  | some petal =>
      refine ⟨((residualProductCode F edge).1 petal).val.card, ?_,
        petalSectionFactor F edge petal, ?_, ?_⟩
      · simpa [productComponentAt] using lowerRank
      · exact petalSectionFactor_noSunflower F noSunflower edge petal
      · simpa [productComponentAt] using
          basePetal_mem_petalSectionFactor F edge petal

theorem lowerRankGateFiber_member_has_recursive_section
    {alpha : Type}
    [DecidableEq alpha]
    {r k : Nat}
    (F : Concrete.UniformSetFamily alpha (r + 2))
    (noSunflower : Not (Concrete.HasSunflower k F))
    (missing : MissingComponentCombination F)
    (slot : GateSlot F)
    (edge : {edge // edge ∈
      (PrivateWitnessReduction.residualFamily F).edges})
    (edge_mem : edge ∈ lowerRankGateDisagreementFiber F missing slot) :
    ∃ n : Nat, n < r + 1 ∧
      ∃ S : Concrete.UniformSetFamily alpha n,
        Not (Concrete.HasSunflower k S) ∧
          productComponentAt F (residualProductCode F edge) slot ∈
            S.edges := by
  exact exists_lowerRank_noSunflower_section_at_slot F noSunflower edge slot
    (Finset.mem_filter.mp edge_mem).2

end ResidualGateSections
end V2
end SunflowerAASC
