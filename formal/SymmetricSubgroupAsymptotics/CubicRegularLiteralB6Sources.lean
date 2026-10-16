import SymmetricSubgroupAsymptotics.CubicRegularSubgroupKernelCoordinates
import SymmetricSubgroupAsymptotics.CubicRegularLiteralFaithfulness
import SymmetricSubgroupAsymptotics.CubicActualRepresentativeSource

/-! One reusable B6 source constructor for literal correlated subgroups of
two regular binary C3 modules. Only original generator point bindings and
actual top/scalar witnesses are required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicRegularLiteralB6Sources
open BinaryThreeQuartetCubicImageSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

variable {n : ℕ} (e : Plane × CyclicThree ≃ Fin 12)
    (lifted : Fin n → Model) (target : Fin n → Equiv.Perm (Fin 12))
    (binding : ∀ i, literalAction e (lifted i) = target i)

abbrev K := Subgroup.closure (Set.range lifted)
abbrev Original := Subgroup.closure (Set.range target)
private def f : K lifted →* Equiv.Perm (Fin 12) :=
  (literalAction e).comp (K lifted).subtype

def toOriginal : K lifted →* Original target :=
  GeneratedLiteralImage.toTop (f e lifted) (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) binding

def originalEquiv : Original target ≃* K lifted :=
  (MulEquiv.ofBijective (toOriginal e lifted target binding) ⟨by
    intro x y he
    apply Subtype.ext
    apply regular_literalAction_injective e
    exact congrArg Subtype.val he,
    GeneratedLiteralImage.toTop_surjective (f e lifted) (closureGenerators lifted)
      target (Equiv.refl _) (closureGenerators_full lifted) binding⟩).symm

theorem projection_surjective (j : Fin n)
    (hj : (lifted j).right = Multiplicative.ofAdd (1 : ZMod 3)) :
    Function.Surjective (projection linear (K lifted)) := by
  intro c
  have hp : ∃ m : Fin 3, (Multiplicative.ofAdd (1 : ZMod 3))^m.val = c := by
    revert c
    decide +kernel
  obtain ⟨m,hm⟩ := hp
  refine ⟨closureGenerators lifted j ^ m.val,?_⟩
  rw [map_pow]
  change (lifted j).right ^ m.val = c
  rw [hj,hm]

variable (hs : Function.Surjective (projection linear (K lifted)))

include binding hs in
theorem original_nonbinary : ¬ IsPGroup 2 (Original target) := by
  intro h
  let pi := (projection linear (K lifted)).comp
    (originalEquiv e lifted target binding).toMonoidHom
  have hp : Function.Surjective pi := hs.comp (originalEquiv e lifted target binding).surjective
  have hc3 : IsPGroup 2 CyclicThree := h.of_surjective pi hp
  have hc : (Multiplicative.ofAdd (1 : ZMod 3))^3=1 := by decide +kernel
  have hn : (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by decide +kernel
  apply hn
  apply (hc3.powEquiv (by decide : Nat.Coprime 2 3)).injective
  simpa only [IsPGroup.powEquiv_apply,one_pow] using hc

variable (hscalar : ∃ j : Fin 2, ∃ p : (projection linear (K lifted)).ker,
    CubicElementaryKernelCoordinates.scalar (projection linear (K lifted))
      (CubicRegularSubgroupKernelCoordinates.moduleRep (K lifted) hs).ρ
      (CubicRegularSubgroupKernelCoordinates.originalKernelChart (K lifted) hs).equiv.symm
      (CubicRegularSubgroupKernelCoordinates.coordinates (K lifted) hs) j p ≠ 1)

def actionCertificate (F : BinaryPairFrame (Original target) (Fin 6))
    (hKP : KovacsPraegerAbelianizationBound) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate (Original target) :=
  CubicAllNormalB6Transport.originalActionCertificate
    (top := projection linear (K lifted))
    (A := CubicRegularSubgroupKernelCoordinates.moduleRep (K lifted) hs)
    (E := CubicRegularSubgroupKernelCoordinates.originalKernelChart (K lifted) hs)
    (originalEquiv e lifted target binding) hs
    (CubicRegularSubgroupKernelCoordinates.coordinates (K lifted) hs) hscalar hKP F

include binding hs hscalar in
theorem exists_actualSource
    (htrans : MulAction.IsPretransitive (Original target) (Fin 12))
    (F : BinaryPairFrame (Original target) (Fin 6))
    (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : Non2UnipotentPrefixFiniteMenu.PreE7PairActionClass 6,
      ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c (Original target) = Non2UnipotentPrefixFiniteMenu.preE7PairAction 6 p ∧
      Nonempty (Non2UnipotentPrefixFiniteMenu.PreE7B6SourceData 12
        (Non2UnipotentPrefixFiniteMenu.preE7SixPairNonPairAction p)) :=
  Non2UnipotentPrefixFiniteMenu.CubicActualRepresentativeSource.exists_actualRepresentativeSource
    (Original target) (original_nonbinary e lifted target binding hs) htrans F
    (originalEquiv e lifted target binding) (projection linear (K lifted)) hs
    (CubicRegularSubgroupKernelCoordinates.moduleRep (K lifted) hs)
    (CubicRegularSubgroupKernelCoordinates.originalKernelChart (K lifted) hs)
    (CubicRegularSubgroupKernelCoordinates.coordinates (K lifted) hs) hscalar hKP

end SymmetricSubgroupAsymptotics.CubicRegularLiteralB6Sources
end
