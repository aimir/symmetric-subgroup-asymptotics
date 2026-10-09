import SymmetricSubgroupAsymptotics.BinaryPairFrameSignFiberCyclic
import SymmetricSubgroupAsymptotics.BinaryPairFrameTernarySelfDual
import SymmetricSubgroupAsymptotics.DiagonalIsotypeProjection

/-!
# Uniform cyclicity from cyclic literal sign fibres

The binary pair kernel acts diagonally on the full ternary signed module.
Its exact character projections split every invariant submodule into the
literal sign fibres.  The source group is transitive on those fibres.  A
single stabilizer generator in one fibre therefore transports to generators
of all fibres and generates the complete submodule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

open OddMarkerTernaryChart

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- Projection onto the coordinates carrying one realized literal sign. -/
def coordinateSignProjection (chi : CoordinateSign F) :
    (I → ZMod 3) →ₗ[ZMod 3] (I → ZMod 3) where
  toFun v i := if coordinateSign F i = chi then v i else 0
  map_add' v w := by
    funext i
    by_cases hi : coordinateSign F i = chi <;> simp [hi]
  map_smul' c v := by
    funext i
    by_cases hi : coordinateSign F i = chi <;> simp [hi]

@[simp] theorem coordinateSignProjection_apply
    (chi : CoordinateSign F) (v : I → ZMod 3) (i : I) :
    coordinateSignProjection F chi v i =
      if coordinateSign F i = chi then v i else 0 := rfl

/-- Scalar characters of the pair kernel on the ternary coordinate module. -/
def ternaryKernelScalar (i : I) (k : F.top.ker) : ZMod 3 :=
  signScalar (Multiplicative.ofAdd (F.bits k i))

/-- A binary sign label gives the corresponding ternary scalar label. -/
def coordinateSignScalarLabel (chi : CoordinateSign F) :
    DiagonalIsotypeProjection.CharacterLabel (ternaryKernelScalar F) :=
  ⟨fun k ↦ signScalar (Multiplicative.ofAdd (chi.1 k)), by
    obtain ⟨i, hi⟩ := chi.2
    refine ⟨i, ?_⟩
    funext k
    exact congrArg (fun f : F.top.ker → ZMod 2 ↦
      signScalar (Multiplicative.ofAdd (f k))) hi⟩

/-- The generic diagonal isotype projector is the literal sign-fibre
projector. -/
theorem isotypeProjection_coordinateSignScalarLabel
    (chi : CoordinateSign F) (v : I → ZMod 3) :
    DiagonalIsotypeProjection.isotypeProjection
        (ternaryKernelScalar F) (coordinateSignScalarLabel F chi) v =
      coordinateSignProjection F chi v := by
  funext i
  rw [DiagonalIsotypeProjection.isotypeProjection_apply,
    coordinateSignProjection_apply]
  congr 1
  constructor
  · intro h
    apply Subtype.ext
    funext k
    apply Multiplicative.ofAdd.injective
    exact signScalar_injective (congrFun h k)
  · intro h
    have hfun := congrArg Subtype.val h
    funext k
    exact congrArg (fun z : ZMod 2 ↦
      signScalar (Multiplicative.ofAdd z)) (congrFun hfun k)

/-- Every sign-fibre projection of an invariant submodule remains in that
same submodule. -/
theorem coordinateSignProjection_mem [Finite I]
    (M : Subrepresentation (ternarySignedRepresentation F))
    (chi : CoordinateSign F) (v : I → ZMod 3)
    (hv : v ∈ M.toSubmodule) :
    coordinateSignProjection F chi v ∈ M.toSubmodule := by
  rw [← isotypeProjection_coordinateSignScalarLabel F chi v]
  apply DiagonalIsotypeProjection.isotypeProjection_mem
    (ternaryKernelScalar F) M.toSubmodule
  intro k x hx
  have hrep :
      DiagonalIsotypeProjection.diagonalOperator
          (ternaryKernelScalar F) k x =
        ternarySignedRepresentation F k.1 x := by
    funext i
    exact (ternarySignedRepresentation_kernel_apply F k x i).symm
  rw [hrep]
  exact M.apply_mem_toSubmodule k.1 hx

/-- Reconstruction is the sum of the literal sign-fibre projections. -/
theorem sum_coordinateSignProjection [Finite I]
    (v : I → ZMod 3) :
    (∑ chi : CoordinateSign F, coordinateSignProjection F chi v) = v := by
  funext i
  rw [Finset.sum_apply]
  let chi := coordinateSign F i
  apply Finset.sum_eq_single chi
  · intro psi _hpsi hne
    simp only [coordinateSignProjection_apply]
    exact if_neg (fun h ↦ hne h.symm)
  · simp [chi]

/-- Extend a vector on one literal sign fibre by zero. -/
def signFiberExtension (chi : CoordinateSign F) :
    ({i : I // coordinateSign F i = chi} → ZMod 3) →ₗ[ZMod 3]
      (I → ZMod 3) where
  toFun v i := if hi : coordinateSign F i = chi then v ⟨i, hi⟩ else 0
  map_add' v w := by
    funext i
    by_cases hi : coordinateSign F i = chi <;> simp [hi]
  map_smul' c v := by
    funext i
    by_cases hi : coordinateSign F i = chi <;> simp [hi]

/-- Restrict a full vector to one literal sign fibre. -/
def signFiberRestriction (chi : CoordinateSign F) :
    (I → ZMod 3) →ₗ[ZMod 3]
      ({i : I // coordinateSign F i = chi} → ZMod 3) where
  toFun v i := v i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem signFiberRestriction_extension
    (chi : CoordinateSign F)
    (v : {i : I // coordinateSign F i = chi} → ZMod 3) :
    signFiberRestriction F chi (signFiberExtension F chi v) = v := by
  funext i
  simp [signFiberRestriction, signFiberExtension, i.2]

theorem signFiberExtension_restriction_of_supported
    (chi : CoordinateSign F) (v : I → ZMod 3)
    (hv : ∀ i, coordinateSign F i ≠ chi → v i = 0) :
    signFiberExtension F chi (signFiberRestriction F chi v) = v := by
  funext i
  by_cases hi : coordinateSign F i = chi
  · simp [signFiberExtension, signFiberRestriction, hi]
  · simp [signFiberExtension, hi, hv i hi]

/-- Extension by zero intertwines the sign stabilizer action. -/
theorem signFiberExtension_equivariant
    (chi : CoordinateSign F)
    (u : MulAction.stabilizer G chi)
    (v : {i : I // coordinateSign F i = chi} → ZMod 3) :
    signFiberExtension F chi (signFiberRepresentation F chi u v) =
      ternarySignedRepresentation F u.1 (signFiberExtension F chi v) := by
  funext i
  by_cases hi : coordinateSign F i = chi
  · let ii : {i : I // coordinateSign F i = chi} := ⟨i, hi⟩
    change
      signScalar (Multiplicative.ofAdd (F.affineTranslation u.1 i)) *
          v (u⁻¹ • ii) =
        signScalar (Multiplicative.ofAdd (F.affineTranslation u.1 i)) *
          (signFiberExtension F chi v) ((F.top u.1)⁻¹ i)
    congr 1
    simp [signFiberExtension, ii]
  · have hpre : coordinateSign F ((F.top u.1)⁻¹ i) ≠ chi := by
      intro hpre
      apply hi
      calc
        coordinateSign F i =
            coordinateSign F (F.top u.1 ((F.top u.1)⁻¹ i)) := by simp
        _ = u.1 • coordinateSign F ((F.top u.1)⁻¹ i) :=
          (smul_coordinateSign F u.1 _).symm
        _ = chi := by
          rw [hpre]
          exact MulAction.mem_stabilizer_iff.mp u.2
    simp [signFiberExtension, hi, hpre,
      ternarySignedRepresentation_apply]

/-- The piece of an invariant submodule supported on one sign fibre. -/
def signFiberSubrepresentation
    (M : Subrepresentation (ternarySignedRepresentation F))
    (chi : CoordinateSign F) :
    Subrepresentation (signFiberRepresentation F chi) where
  toSubmodule := M.toSubmodule.comap (signFiberExtension F chi)
  apply_mem_toSubmodule := by
    intro u v hv
    change signFiberExtension F chi (signFiberRepresentation F chi u v) ∈ M
    rw [signFiberExtension_equivariant F chi u v]
    exact M.apply_mem_toSubmodule u.1 hv

/-- Extension embeds the fibre piece into the original invariant module. -/
def signFiberSubrepresentationInclusion
    (M : Subrepresentation (ternarySignedRepresentation F))
    (chi : CoordinateSign F) :
    (signFiberSubrepresentation F M chi).toRepresentation.IntertwiningMap
      ((M.toRepresentation).comp (MulAction.stabilizer G chi).subtype) where
  toLinearMap :=
    { toFun := fun v ↦ ⟨signFiberExtension F chi v.1, v.2⟩
      map_add' _ _ := Subtype.ext (map_add (signFiberExtension F chi) _ _)
      map_smul' _ _ := Subtype.ext (map_smul (signFiberExtension F chi) _ _) }
  isIntertwining' u := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact signFiberExtension_equivariant F chi u v.1

/-- The original source is transitive on its realized sign labels. -/
theorem coordinateSign_pretransitive
    [Finite I] (htrans : MulAction.IsPretransitive G X) :
    MulAction.IsPretransitive G (CoordinateSign F) := by
  constructor
  intro chi psi
  obtain ⟨i, rfl⟩ := coordinateSign_surjective F chi
  obtain ⟨j, rfl⟩ := coordinateSign_surjective F psi
  letI : MulAction.IsPretransitive G X := htrans
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
  obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
  refine ⟨u, ?_⟩
  rw [smul_coordinateSign]
  apply congrArg (coordinateSign F)
  simpa using ht

/-- If every literal sign-fibre stabilizer module has cyclic invariant
submodules, then so does the complete signed coordinate module. -/
theorem ternarySignedRepresentation_uniformSubrepresentationGeneratorBound_one
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (hfiber : ∀ chi : CoordinateSign F,
      UniformSubrepresentationGeneratorBound
        (signFiberRepresentation F chi) 1) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F) 1 := by
  letI : MulAction.IsPretransitive G (CoordinateSign F) :=
    coordinateSign_pretransitive F htrans
  intro M
  let chi : CoordinateSign F :=
    coordinateSign F (Classical.choice (inferInstance : Nonempty I))
  obtain ⟨a, ha⟩ := hfiber chi (signFiberSubrepresentation F M chi)
  let inclusion := signFiberSubrepresentationInclusion F M chi
  let generator : Fin 1 → M.toRepresentation.asModule := fun _ ↦
    M.toRepresentation.asModuleEquiv.symm
      (inclusion (a 0)).1
  let W : Submodule (ZMod 3)[G] M.toRepresentation.asModule :=
    Submodule.span (ZMod 3)[G] (Set.range generator)
  let N : Subrepresentation M.toRepresentation :=
    Subrepresentation.ofSubmodule' W
  have hfiber_le : ∀ y : signFiberSubrepresentation F M chi,
      inclusion y ∈ N.toSubmodule := by
    let Q : Subrepresentation
        (signFiberSubrepresentation F M chi).toRepresentation :=
      { toSubmodule := N.toSubmodule.comap inclusion.toLinearMap
        apply_mem_toSubmodule := by
          intro u y hy
          change inclusion
              ((signFiberSubrepresentation F M chi).toRepresentation u y) ∈ N
          rw [Representation.IntertwiningMap.isIntertwining]
          exact N.apply_mem_toSubmodule u.1 hy }
    have haQ : ∀ i, a i ∈ Q.asSubmodule := by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change generator 0 ∈ W
      exact Submodule.subset_span (Set.mem_range_self 0)
    have hspan : Submodule.span (ZMod 3)[MulAction.stabilizer G chi]
        (Set.range a) ≤ Q.asSubmodule :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact haQ i)
    rw [ha] at hspan
    intro y
    exact hspan Submodule.mem_top
  refine ⟨generator, top_unique ?_⟩
  intro x _hx
  change x ∈ W
  have hcomponent : ∀ psi : CoordinateSign F,
      ⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩ ∈ N.toSubmodule := by
    intro psi
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq G chi psi
    let z : M.toSubmodule :=
      ⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩
    let y : M.toSubmodule := M.toRepresentation u⁻¹ z
    have hysupport : ∀ i, coordinateSign F i ≠ chi → y.1 i = 0 := by
      intro i hi
      have hnotpsi : coordinateSign F (F.top u i) ≠ psi := by
        intro heq
        apply hi
        apply (coordinateSignTopPerm F u).injective
        simpa only [coordinateSignTopPerm_apply,
          coordinateSignTopMap_apply_coordinate, hu] using heq
      simp [y, z, ternarySignedRepresentation_apply,
        coordinateSignProjection_apply, hnotpsi]
    have hyext : signFiberExtension F chi
        (signFiberRestriction F chi y.1) = y.1 :=
      signFiberExtension_restriction_of_supported F chi y.1 hysupport
    let yF : signFiberSubrepresentation F M chi :=
      ⟨signFiberRestriction F chi y.1, by
        change signFiberExtension F chi
          (signFiberRestriction F chi y.1) ∈ M
        rw [hyext]
        exact y.2⟩
    have hyN : y ∈ N.toSubmodule := by
      have := hfiber_le yF
      simpa only [inclusion, signFiberSubrepresentationInclusion, yF,
        hyext] using this
    have huz : M.toRepresentation u y = z := by
      simp [y]
    rw [← huz]
    exact N.apply_mem_toSubmodule u hyN
  have hsum : (∑ psi : CoordinateSign F,
      (⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩ : M.toSubmodule)) ∈
      N.toSubmodule :=
    N.toSubmodule.sum_mem (fun psi _ ↦ hcomponent psi)
  have heq : (∑ psi : CoordinateSign F,
      (⟨coordinateSignProjection F psi x.1,
        coordinateSignProjection_mem F M psi x.1 x.2⟩ : M.toSubmodule)) = x := by
    apply Subtype.ext
    exact sum_coordinateSignProjection F x.1
  rw [heq] at hsum
  exact hsum

/-- The same one-generator theorem holds for the contragredient. -/
theorem ternarySignedRepresentation_dual_uniformSubrepresentationGeneratorBound_one
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (hfiber : ∀ chi : CoordinateSign F,
      UniformSubrepresentationGeneratorBound
        (signFiberRepresentation F chi) 1) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual 1 :=
  ternarySignedRepresentation_dual_uniform_of_primal F
    (ternarySignedRepresentation_uniformSubrepresentationGeneratorBound_one
      F htrans hfiber)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
