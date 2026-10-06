import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameSelectedRowAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameInducedTopNaturality
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameInducedCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28LiteralLocalRow
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28ModuleRegistry

/-!
# Selected eight-frame row 28: binding to the actual affine frame

This file transports the checked row-28 Schreier and matrix certificates to
an arbitrary literal degree-four, eight-block zero-core action whose top is
conjugate to the stored permutation group.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameRow28ActualBinding

open PrimitiveAffineEightFrameRow28InducedBinding

abbrev Source := PrimitiveAffineEightFrameRow28TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow28TopCertificate.group

abbrev ModelModule :=
  PrimitiveAffineEightFrameRow28ModuleRepresentation.ModelModule

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance row28ActualPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- The exact literal top match selected by row 28. -/
def literalTopMatch
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction) :
    DegreeFourZeroCoreEightLiteralTopMatch block Source where
  literalAction :=
    PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction
  actionModelEquiv :=
    PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.symm
  pointEquiv := pointEquiv
  conjugator := conjugator
  conjugated := hconjugated

/-- Select the generated order-three quotient against the actual local
affine complement. -/
noncomputable def pointedLocalMatch
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourZeroCoreEightPointedLocalMatch block P
      (literalTopMatch block pointEquiv conjugator hconjugated)
      hr hD (0 : Fin 8) :=
  DegreeEightLiteralLocalRowCatalogue.selectActualOrderOneSixtyEight
    block P (literalTopMatch block pointEquiv conjugator hconjugated)
    PrimitiveAffineEightFrameRow28LiteralLocalRow.literalLocalRow hr hD
    PrimitiveAffineEightFrameRow28TopCertificate.source_card
    (by
      change Nat.card PrimitiveAffineEightFrameRow28InducedBinding.CyclicThree = 3
      rw [Nat.card_eq_fintype_card]
      decide)

/-- Restrict a representation equivalence along a group homomorphism. -/
noncomputable def representationEquivComp
    {k G K V W : Type} [Semiring k] [Group G] [Group K]
    [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W]
    {rho : Representation k G V} {sigma : Representation k G W}
    (e : Representation.Equiv rho sigma) (f : K →* G) :
    Representation.Equiv (rho.comp f) (sigma.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun x ↦ e.isIntertwining' (f x))

/-- Transport one stored source-stabilizer element back to the actual
induced stabilizer. -/
noncomputable def sourceStabilizerToActual
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    sourceStabilizer ≃*
      fullFrameInducedStabilizer block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block)
          (literalTopMatch block pointEquiv conjugator hconjugated)
          (0 : Fin 8)) :=
  PrimitiveAffineEightFrameRow28LiteralLocalRow.sourceStabilizerEquivLiteral.trans
    (fullFrameInducedStabilizerEquivLiteral block P
      (literalTopMatch block pointEquiv conjugator hconjugated)
      hr hD (0 : Fin 8)).symm

theorem fullFrameInducedStabilizerEquivLiteral_sourceStabilizerToActual
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (h : sourceStabilizer) :
    fullFrameInducedStabilizerEquivLiteral block P
        (literalTopMatch block pointEquiv conjugator hconjugated)
        hr hD (0 : Fin 8)
        (sourceStabilizerToActual block P pointEquiv conjugator
          hconjugated hr hD h) =
      PrimitiveAffineEightFrameRow28LiteralLocalRow.sourceStabilizerEquivLiteral h := by
  change (fullFrameInducedStabilizerEquivLiteral block P
      (literalTopMatch block pointEquiv conjugator hconjugated)
      hr hD (0 : Fin 8))
      (((fullFrameInducedStabilizerEquivLiteral block P
        (literalTopMatch block pointEquiv conjugator hconjugated)
        hr hD (0 : Fin 8)).symm)
        (PrimitiveAffineEightFrameRow28LiteralLocalRow.sourceStabilizerEquivLiteral h)) = _
  exact (fullFrameInducedStabilizerEquivLiteral block P
    (literalTopMatch block pointEquiv conjugator hconjugated)
    hr hD (0 : Fin 8)).apply_symm_apply _

/-- The full top equivalence sends a transported source-stabilizer element
back to its original executable Cayley row. -/
theorem groupEquiv_sourceStabilizerToActual
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (h : sourceStabilizer) :
    DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
        (block := block) (P := P)
        (literalTopMatch block pointEquiv conjugator hconjugated) hr hD
        ((sourceStabilizerToActual block P pointEquiv conjugator
          hconjugated hr hD h).1) = h.1 := by
  have hrestrict := groupEquiv_stabilizer block P
    (literalTopMatch block pointEquiv conjugator hconjugated)
    hr hD (0 : Fin 8)
    (sourceStabilizerToActual block P pointEquiv conjugator
      hconjugated hr hD h)
  calc
    DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
        (block := block) (P := P)
        (literalTopMatch block pointEquiv conjugator hconjugated) hr hD
        ((sourceStabilizerToActual block P pointEquiv conjugator
          hconjugated hr hD h).1) =
      PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.symm
        ((fullFrameInducedStabilizerEquivLiteral block P
          (literalTopMatch block pointEquiv conjugator hconjugated)
          hr hD (0 : Fin 8)
          (sourceStabilizerToActual block P pointEquiv conjugator
            hconjugated hr hD h)).1) := hrestrict
    _ = PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.symm
        ((PrimitiveAffineEightFrameRow28LiteralLocalRow.sourceStabilizerEquivLiteral h).1) := by
      rw [fullFrameInducedStabilizerEquivLiteral_sourceStabilizerToActual
        block P pointEquiv conjugator hconjugated hr hD h]
    _ = h.1 := by
      exact PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.symm_apply_apply h.1

/-- The transported actual local component has exactly the stored exponent
on every source-stabilizer element. -/
theorem actualLocalMap_sourceStabilizerToActual
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (h : sourceStabilizer) :
    (pointedLocalMatch block P pointEquiv conjugator hconjugated hr hD).targetEquiv
      (binaryAffineStabilizerComponent block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block)
          (literalTopMatch block pointEquiv conjugator hconjugated)
          (0 : Fin 8))
        (sourceStabilizerToActual block P pointEquiv conjugator
          hconjugated hr hD h)) =
      sourceLocalMap h := by
  have hcomponent := pointedLocalMatch_actual_component block P
    (pointedLocalMatch block P pointEquiv conjugator hconjugated hr hD)
    (sourceStabilizerToActual block P pointEquiv conjugator
      hconjugated hr hD h)
  calc
    (pointedLocalMatch block P pointEquiv conjugator hconjugated hr hD).targetEquiv
        (binaryAffineStabilizerComponent block P
          (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
            (block := block)
            (literalTopMatch block pointEquiv conjugator hconjugated)
            (0 : Fin 8))
          (sourceStabilizerToActual block P pointEquiv conjugator
            hconjugated hr hD h)) =
      PrimitiveAffineEightFrameRow28LiteralLocalRow.literalLocalMap
        (fullFrameInducedStabilizerEquivLiteral block P
          (literalTopMatch block pointEquiv conjugator hconjugated)
          hr hD (0 : Fin 8)
          (sourceStabilizerToActual block P pointEquiv conjugator
            hconjugated hr hD h)) := hcomponent
    _ = PrimitiveAffineEightFrameRow28LiteralLocalRow.literalLocalMap
        (PrimitiveAffineEightFrameRow28LiteralLocalRow.sourceStabilizerEquivLiteral h) := by
      rw [fullFrameInducedStabilizerEquivLiteral_sourceStabilizerToActual
        block P pointEquiv conjugator hconjugated hr hD h]
    _ = sourceLocalMap h := by
      simp [PrimitiveAffineEightFrameRow28LiteralLocalRow.literalLocalMap]

noncomputable def actualRepresentative
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (a : Fin 8) : DegreeFourComplementQuotient block P :=
  (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
    (block := block) (P := P)
    (literalTopMatch block pointEquiv conjugator hconjugated) hr hD).symm
      (representative a)

noncomputable def actualGenerator
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (j : Fin 3) : DegreeFourComplementQuotient block P :=
  (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
    (block := block) (P := P)
    (literalTopMatch block pointEquiv conjugator hconjugated) hr hD).symm
      (PrimitiveAffineEightFrameRow28TopCertificate.ambient j)

noncomputable def actualTwist
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (j : Fin 3) (a : Fin 8) :=
  sourceStabilizerToActual block P pointEquiv conjugator hconjugated hr hD
    (twist j a)

theorem actualRepresentative_mul_generator
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (j : Fin 3) (a : Fin 8) :
    actualRepresentative block P pointEquiv conjugator hconjugated hr hD a *
        actualGenerator block P pointEquiv conjugator hconjugated hr hD j =
      (actualTwist block P pointEquiv conjugator hconjugated hr hD j a :
          DegreeFourComplementQuotient block P) *
        actualRepresentative block P pointEquiv conjugator hconjugated hr hD
          (next j a) := by
  let e := DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
    (block := block) (P := P)
    (literalTopMatch block pointEquiv conjugator hconjugated) hr hD
  have hrepresentative (c : Fin 8) :
      e (actualRepresentative block P pointEquiv conjugator hconjugated
        hr hD c) = representative c := by
    change e (e.symm (representative c)) = representative c
    exact e.apply_symm_apply _
  have hgenerator :
      e (actualGenerator block P pointEquiv conjugator hconjugated hr hD j) =
        PrimitiveAffineEightFrameRow28TopCertificate.ambient j := by
    change e (e.symm
      (PrimitiveAffineEightFrameRow28TopCertificate.ambient j)) = _
    exact e.apply_symm_apply _
  apply e.injective
  rw [map_mul, map_mul]
  rw [hrepresentative, hgenerator, hrepresentative]
  rw [actualTwist]
  rw [groupEquiv_sourceStabilizerToActual block P pointEquiv conjugator
    hconjugated hr hD (twist j a)]
  exact representative_mul_generator j a

theorem actualGenerator_full
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    Subgroup.closure (Set.range
      (actualGenerator block P pointEquiv conjugator hconjugated hr hD)) =
        ⊤ := by
  let e := DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
    (block := block) (P := P)
    (literalTopMatch block pointEquiv conjugator hconjugated) hr hD
  calc
    Subgroup.closure (Set.range
        (actualGenerator block P pointEquiv conjugator hconjugated hr hD)) =
      Subgroup.map e.symm.toMonoidHom
        (Subgroup.closure
          (Set.range PrimitiveAffineEightFrameRow28TopCertificate.ambient)) := by
        rw [MonoidHom.map_closure]
        congr 1
        ext x
        simp [actualGenerator, e]
    _ = Subgroup.map e.symm.toMonoidHom ⊤ := by
      rw [PrimitiveAffineEightFrameRow28TopCertificate.ambient_full]
    _ = ⊤ := Subgroup.map_top_of_surjective _ e.symm.surjective

@[simp] theorem groupEquiv_actualGenerator
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (j : Fin 3) :
    DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
        (block := block) (P := P)
        (literalTopMatch block pointEquiv conjugator hconjugated) hr hD
        (actualGenerator block P pointEquiv conjugator hconjugated hr hD j) =
      PrimitiveAffineEightFrameRow28TopCertificate.ambient j := by
  change (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
      (block := block) (P := P)
      (literalTopMatch block pointEquiv conjugator hconjugated) hr hD)
      ((DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
        (block := block) (P := P)
        (literalTopMatch block pointEquiv conjugator hconjugated) hr hD).symm
        (PrimitiveAffineEightFrameRow28TopCertificate.ambient j)) = _
  exact (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
    (block := block) (P := P)
    (literalTopMatch block pointEquiv conjugator hconjugated) hr hD).apply_symm_apply _

theorem actualRepresentative_factor
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    ∀ x : DegreeFourComplementQuotient block P,
      ∃ h : DegreeFourComplementQuotient block P,
        h ∈ fullFrameInducedStabilizer block P
          (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
            (block := block)
            (literalTopMatch block pointEquiv conjugator hconjugated)
            (0 : Fin 8)) ∧
        ∃ a : Fin 8,
          x = h * actualRepresentative block P pointEquiv conjugator
            hconjugated hr hD a := by
  intro x
  let e := DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
    (block := block) (P := P)
    (literalTopMatch block pointEquiv conjugator hconjugated) hr hD
  have hrepresentative (c : Fin 8) :
      e (actualRepresentative block P pointEquiv conjugator hconjugated
        hr hD c) = representative c := by
    change e (e.symm (representative c)) = representative c
    exact e.apply_symm_apply _
  obtain ⟨h, hh, a, ha⟩ := representative_factor (e x)
  let hActual := sourceStabilizerToActual block P pointEquiv conjugator
    hconjugated hr hD ⟨h, hh⟩
  refine ⟨hActual.1, hActual.2, a, ?_⟩
  apply e.injective
  rw [map_mul, groupEquiv_sourceStabilizerToActual block P pointEquiv
    conjugator hconjugated hr hD ⟨h, hh⟩]
  rw [hrepresentative]
  exact ha

/-- The actual point-stabilizer component, expressed in the retained
cyclic-three coordinate. -/
noncomputable def actualLocalMap
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    fullFrameInducedStabilizer block P
        (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
          (block := block)
          (literalTopMatch block pointEquiv conjugator hconjugated)
          (0 : Fin 8)) →*
      CyclicThree :=
  (pointedLocalMatch block P pointEquiv conjugator hconjugated hr hD).targetEquiv.toMonoidHom.comp
    (binaryAffineStabilizerComponent block P
      (DegreeFourZeroCoreEightLiteralTopMatch.pointOver
        (block := block)
        (literalTopMatch block pointEquiv conjugator hconjugated)
        (0 : Fin 8)))

@[simp] theorem actualLocalMap_apply_sourceStabilizerToActual
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (h : sourceStabilizer) :
    actualLocalMap block P pointEquiv conjugator hconjugated hr hD
        (sourceStabilizerToActual block P pointEquiv conjugator
          hconjugated hr hD h) =
      sourceLocalMap h := by
  exact actualLocalMap_sourceStabilizerToActual block P pointEquiv
    conjugator hconjugated hr hD h

/-- The emitted module, with its coefficient characteristic left explicit
so that an equality `p = 2` can be consumed without dependent elimination
on an affine profile containing `p` as a field. -/
abbrev ModelModuleAt (p : ℕ) := Fin 16 → ZMod p

abbrev LocalPlaneAt (p : ℕ) := Fin 2 → ZMod p

noncomputable def localRepresentationAt
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    Representation (ZMod p) CyclicThree (LocalPlaneAt p) := by
  subst p
  exact localRepresentation

theorem localRepresentationAt_injective
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    Function.Injective (localRepresentationAt hp) := by
  subst p
  exact localRepresentation_injective

noncomputable def modelRepresentationAt
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    Representation (ZMod p) Source (ModelModuleAt p) := by
  subst p
  exact PrimitiveAffineEightFrameRow28ModuleRepresentation.representation

theorem modelRepresentationAt_generator_formula
    {p : ℕ} [Fact p.Prime] (hp : p = 2)
    (j : Fin 3) (v : ModelModuleAt p) (a : Fin 8) (i : Fin 2) :
    modelRepresentationAt hp
        (PrimitiveAffineEightFrameRow28TopCertificate.ambient j) v
        (CoinducedLeadingCoordinates.label a i) =
      localRepresentationAt hp (Multiplicative.ofAdd (twistExponent j a))
        (fun q ↦ v (CoinducedLeadingCoordinates.label (next j a) q)) i := by
  subst p
  exact representation_generator_formula j v a i

theorem modelModuleAt_finrank_eq_sixteen
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    Module.finrank (ZMod p) (ModelModuleAt p) = 16 := by
  subst p
  exact PrimitiveAffineEightFrameRow28ModuleRepresentation.model_finrank_eq_sixteen

noncomputable def modelModuleRegistryAt
    {p : ℕ} [Fact p.Prime] (hp : p = 2) :
    FiniteFrameModuleCyclicOrbitDisplacementRegistry
      (modelRepresentationAt hp) 2 := by
  subst p
  exact PrimitiveAffineEightFrameRow28ModuleRegistry.registry

/-- Characteristic-transported form of uniqueness of the faithful binary
plane. -/
noncomputable def binaryPlaneRepresentationEquiv_of_card_three_at
    {p : ℕ} [Fact p.Prime]
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (hp : p = 2)
    (rho : Representation (ZMod p) G V)
    (sigma : Representation (ZMod p) G (LocalPlaneAt p))
    (hG : Nat.card G = 3)
    (hV : Module.finrank (ZMod p) V = 2)
    (hrho : Function.Injective rho)
    (hsigma : Function.Injective sigma) :
    rho.Equiv sigma := by
  subst p
  exact binaryPlaneRepresentationEquiv_of_card_three rho sigma hG hV
    (by simp [LocalPlaneAt]) hrho hsigma

/-- The checked order-168 row, now bound to the actual eight-block affine
frame.  All row data below are executable certificates; the only abstract
step is uniqueness of the faithful binary plane for a group of order
three. -/
noncomputable def selectedRow
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourZeroCoreEightOrderOneSixtyEightSelectedRow block P
      (literalTopMatch block pointEquiv conjugator hconjugated) hr hD := by
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  let topMatch := literalTopMatch block pointEquiv conjugator hconjugated
  let point := DegreeFourZeroCoreEightLiteralTopMatch.pointOver
    (block := block) topMatch (0 : Fin 8)
  let H := fullFrameInducedStabilizer block P point
  let rho := fullFrameInducedLocalRepresentation block P point
  let L := pointedLocalMatch block P pointEquiv conjugator hconjugated hr hD
  let sigma := (localRepresentationAt hp).comp
    (actualLocalMap block P pointEquiv conjugator hconjugated hr hD)
  let localEquiv : rho.Equiv sigma := by
    let quotientEquiv :
        (binaryAffineLocalLinearRepresentation block P).ρ.Equiv
          ((localRepresentationAt hp).comp L.targetEquiv.toMonoidHom) :=
      binaryPlaneRepresentationEquiv_of_card_three_at hp
        (binaryAffineLocalLinearRepresentation block P).ρ
        ((localRepresentationAt hp).comp L.targetEquiv.toMonoidHom)
        (by
          rw [Nat.card_congr L.targetEquiv.toEquiv]
          change Nat.card CyclicThree = 3
          rw [Nat.card_eq_fintype_card]
          decide)
        (by
          change (chart block P).d = 2
          exact (degreeFour_translationDimension block P hr).2)
        (binaryAffineLocalLinearRepresentation_injective block P)
        ((localRepresentationAt_injective hp).comp L.targetEquiv.injective)
    exact representationEquivComp quotientEquiv
      (binaryAffineStabilizerComponent block P point)
  let basis := Pi.basisFun (ZMod P.p) (Fin 2)
  let coordinateMap := EightFrameInducedCoordinates.coordinatesOfLocalEquiv
    H rho sigma localEquiv
      (actualRepresentative block P pointEquiv conjugator hconjugated hr hD)
      basis
  have coordinateMap_injective : Function.Injective coordinateMap :=
    EightFrameInducedCoordinates.coordinatesOfLocalEquiv_injective
      H rho sigma localEquiv
        (actualRepresentative block P pointEquiv conjugator hconjugated hr hD)
        basis
        (actualRepresentative_factor block P pointEquiv conjugator
          hconjugated hr hD)
  have generator_image (j : Fin 3) :
      (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
        (block := block) (P := P) topMatch hr hD)
        (actualGenerator block P pointEquiv conjugator hconjugated hr hD j) =
        PrimitiveAffineEightFrameRow28TopCertificate.ambient j := by
    exact groupEquiv_actualGenerator block P pointEquiv conjugator hconjugated hr hD j
  let inducedMatch := DegreeFourZeroCoreEightInducedRowMatch.ofGeneratorEquations
    block P (modelRepresentationAt hp)
    (DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
      (block := block) (P := P) topMatch hr hD)
    point
    (actualGenerator block P pointEquiv conjugator hconjugated hr hD)
    (actualGenerator_full block P pointEquiv conjugator hconjugated hr hD)
    coordinateMap coordinateMap_injective (by
      intro j v
      funext z
      obtain ⟨⟨a, i⟩, rfl⟩ :=
        (finProdFinEquiv (m := 8) (n := 2)).surjective z
      calc
        coordinateMap
            ((Representation.ind H.subtype rho)
              (actualGenerator block P pointEquiv conjugator hconjugated hr hD j) v)
            (CoinducedLeadingCoordinates.label a i) =
          basis.equivFun
            (sigma
              (actualTwist block P pointEquiv conjugator hconjugated hr hD j a)
              (((inducedToCoinducedEquiv H sigma)
                ((EightFrameInducedCoordinates.inducedEquivOfLocalEquiv
                  H rho sigma localEquiv) v)).1
                (actualRepresentative block P pointEquiv conjugator
                  hconjugated hr hD (next j a)))) i := by
            exact EightFrameInducedCoordinates.coordinatesOfLocalEquiv_action_label
              H rho sigma localEquiv
              (actualRepresentative block P pointEquiv conjugator
                hconjugated hr hD)
              basis v
              (actualGenerator block P pointEquiv conjugator hconjugated hr hD j)
              a (next j a)
              (actualTwist block P pointEquiv conjugator hconjugated hr hD j a)
              (actualRepresentative_mul_generator block P pointEquiv conjugator
                hconjugated hr hD j a) i
        _ = localRepresentationAt hp
              (Multiplicative.ofAdd (twistExponent j a))
              (fun q ↦ coordinateMap v
                (CoinducedLeadingCoordinates.label (next j a) q)) i := by
            rw [Pi.basisFun_equivFun]
            change localRepresentationAt hp
                (actualLocalMap block P pointEquiv conjugator hconjugated hr hD
                  (sourceStabilizerToActual block P pointEquiv conjugator
                    hconjugated hr hD (twist j a))) _ i = _
            apply congrArg (fun u : LocalPlaneAt P.p ↦ u i)
            apply congrArg₂ (fun g u ↦ localRepresentationAt hp g u)
            · exact (actualLocalMap_apply_sourceStabilizerToActual block P
                pointEquiv conjugator hconjugated hr hD (twist j a)).trans
                (sourceLocalMap_twist j a)
            · funext q
              have hcoordinate :=
                EightFrameInducedCoordinates.coordinatesOfLocalEquiv_label
                  H rho sigma localEquiv
                  (actualRepresentative block P pointEquiv conjugator
                    hconjugated hr hD)
                  basis v (next j a) q
              simpa only [Pi.basisFun_equivFun,
                LinearEquiv.refl_apply] using hcoordinate.symm
        _ = modelRepresentationAt hp
              (PrimitiveAffineEightFrameRow28TopCertificate.ambient j)
              (coordinateMap v)
              (CoinducedLeadingCoordinates.label a i) :=
            (modelRepresentationAt_generator_formula hp j
              (coordinateMap v) a i).symm
        _ = modelRepresentationAt hp
              ((DegreeFourZeroCoreEightLiteralTopMatch.groupEquiv
                (block := block) (P := P) topMatch hr hD)
                (actualGenerator block P pointEquiv conjugator hconjugated hr hD j))
              (coordinateMap v)
              (CoinducedLeadingCoordinates.label a i) := by
            specialize generator_image j
            rw [generator_image]
    )
  exact {
    modelGroup_card := PrimitiveAffineEightFrameRow28TopCertificate.source_card
    ModelModule := ModelModuleAt P.p
    representation := modelRepresentationAt hp
    inducedEmbedding := inducedMatch.inducedEmbedding
    inducedEmbedding_injective := inducedMatch.inducedEmbedding_injective
    model_finrank_eq_sixteen :=
      modelModuleAt_finrank_eq_sixteen hp
    classCount := 6
    representative := PrimitiveAffineEightFrameRow28TopCertificate.representative
    conjugacyCover := PrimitiveAffineEightFrameRow28TopCertificate.conjugacy.toCardinalCover
    TopIndex := Fin 2
    AmbientIndex := Fin 3
    GeneratorIndex := Fin 3
    ambient := PrimitiveAffineEightFrameRow28TopCertificate.ambient
    stateGenerators := PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators
    top := PrimitiveAffineEightFrameRow28TopRegistry.registry
    moduleRegistry := modelModuleRegistryAt hp }

/-- The public five-slot capacity row consumed by the degree-four
zero-core residue dispatcher. -/
noncomputable def bounds
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  let C := elementaryChart block P
  letI : Finite (elementaryChart block P).V := Finite.of_injective
    (fun v : C.V ↦ C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  exact (selectedRow block P pointEquiv conjugator hconjugated hr hD).toBounds
    block P hs

end PrimitiveAffineEightFrameRow28ActualBinding
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
