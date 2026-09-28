import SymmetricSubgroupAsymptotics.BinaryPairResidualTop
import SymmetricSubgroupAsymptotics.Non2OriginalFusionPayloadSelection

/-!
# Original nonbinary fusion on a literal pair-kernel axis

When an original normal axis lies inside the kernel of a physical pair top,
the quotient by that axis maps directly onto the unchanged top range.  Its
kernel is the exact retained pair section, with no quotient of the top and no
replacement action.  This file constructs the reversible kernel chart and
feeds the literal permutation section into the general nonbinary capacity
theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- On an axis contained in the pair kernel, the original normal quotient
maps onto the unchanged faithful top range. -/
def non2TopBase (hN : N ≤ F.top.ker) : (U ⧸ N) →* F.top.range :=
  QuotientGroup.lift N F.top.rangeRestrict (by
    intro n hn
    apply Subtype.ext
    exact hN hn)

@[simp] theorem non2TopBase_apply (hN : N ≤ F.top.ker) (u : U) :
    F.non2TopBase N hN (QuotientGroup.mk' N u) = F.top.rangeRestrict u := rfl

theorem non2TopBase_surjective (hN : N ≤ F.top.ker) :
    Function.Surjective (F.non2TopBase N hN) := by
  intro t
  obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
  exact ⟨QuotientGroup.mk' N u, rfl⟩

/-- The literal pair kernel maps onto the kernel of the unchanged-top base
map.  Every element is represented by the same original element of `U`. -/
def non2TopKernelMap (hN : N ≤ F.top.ker) :
    F.top.ker →* (F.non2TopBase N hN).ker where
  toFun l := ⟨QuotientGroup.mk' N (l : U), by
    rw [MonoidHom.mem_ker, F.non2TopBase_apply]
    apply Subtype.ext
    exact l.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul _ _ _

theorem non2TopKernelMap_surjective (hN : N ≤ F.top.ker) :
    Function.Surjective (F.non2TopKernelMap N hN) := by
  intro q
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective N q.1
  have htop : F.top.rangeRestrict u = 1 := by
    have hq := q.property
    rw [MonoidHom.mem_ker] at hq
    rw [← hu, F.non2TopBase_apply] at hq
    exact hq
  have huKer : u ∈ F.top.ker := by
    change F.top u = 1
    exact congrArg Subtype.val htop
  refine ⟨⟨u, huKer⟩, ?_⟩
  apply Subtype.ext
  exact hu.trans rfl

theorem non2TopKernelMap_ker (hN : N ≤ F.top.ker) :
    (F.non2TopKernelMap N hN).ker = N.subgroupOf F.top.ker := by
  ext l
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change QuotientGroup.mk' N (l : U) = 1 ↔ (l : U) ∈ N
  exact QuotientGroup.eq_one_iff _

/-- Reversible identification of the exact retained pair section with the
kernel of `U/N → range(top)`. -/
def non2TopKernelEquiv (hN : N ≤ F.top.ker) :
    Multiplicative (F.kernelSpace ⧸ F.normalSpace N) ≃*
      (F.non2TopBase N hN).ker :=
  binaryPair_sameKernelEquiv (F.sectionMap N) (F.non2TopKernelMap N hN)
    (F.sectionMap_surjective N) (F.non2TopKernelMap_surjective N hN)
    ((F.sectionMap_ker N).trans (F.non2TopKernelMap_ker N hN).symm)

@[simp] theorem non2TopKernelEquiv_apply (hN : N ≤ F.top.ker)
    (l : F.top.ker) :
    F.non2TopKernelEquiv N hN (F.sectionMap N l) =
      F.non2TopKernelMap N hN l :=
  binaryPair_sameKernelEquiv_apply _ _ _ _ _ l

/-- The original nonsplit extension over the unchanged top range.  The
module is the same literal section used by the permutation intertwiner. -/
def non2TopModuleChart (hN : N ≤ F.top.ker) :
    OriginalKernelModuleChart (F.non2TopBase N hN)
      (Rep.of (F.sectionTopRepresentation N)) where
  equiv := F.non2TopKernelEquiv N hN
  conjugate q a := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨l, hl⟩ := F.sectionMap_surjective N (Multiplicative.ofAdd a)
    have ha : (F.sectionMap N l).toAdd = a :=
      congrArg Multiplicative.toAdd hl
    rw [← ha, F.non2TopBase_apply]
    change (F.non2TopKernelEquiv N hN
        (Multiplicative.ofAdd
          (F.sectionTopRepresentation N (F.top.rangeRestrict u)
            (F.sectionMap N l).toAdd)) : U ⧸ N) = _
    change (F.non2TopKernelEquiv N hN
        (Multiplicative.ofAdd
          (F.sectionRepresentation N
            (F.sectionTopQuotient N (F.top.rangeRestrict u))
            (F.sectionMap N l).toAdd)) : U ⧸ N) = _
    rw [F.sectionTopQuotient_apply, F.sectionRepresentation_apply]
    have he (m : F.top.ker) :
        (F.non2TopKernelEquiv N hN (F.sectionMap N m) : U ⧸ N) =
          QuotientGroup.mk' N (m : U) :=
      congrArg Subtype.val (F.non2TopKernelEquiv_apply N hN m)
    calc
      _ = QuotientGroup.mk' N (MulAut.conjNormal u l : U) :=
        he (MulAut.conjNormal u l)
      _ = QuotientGroup.mk' N u * QuotientGroup.mk' N (l : U) *
          (QuotientGroup.mk' N u)⁻¹ := by
        change QuotientGroup.mk' N (u * (l : U) * u⁻¹) = _
        simp only [map_mul, map_inv]
      _ = _ := congrArg
        (fun z : U ⧸ N =>
          QuotientGroup.mk' N u * z * (QuotientGroup.mk' N u)⁻¹)
        (he l).symm

section Certificate

variable [Finite X] [Finite I]
variable [MulAction.IsPretransitive F.top.range I]

omit [Finite X] in
/-- The general retained-annihilator theorem applies to the exact retained
pair section whenever its unchanged top range is nonbinary.  The separate
kernel-containment hypothesis enters only when this section is identified
with the kernel of the original quotient extension below. -/
theorem exists_non2OriginalFusionCertificate_of_pairSection
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hTop : ¬ IsPGroup 2 F.top.range)
    (i : I) (hs : 24 ≤ Nat.card I) (heven : Even (Nat.card I)) :
    Nonempty (Non2OriginalFusionCertificate
      (Rep.of (F.sectionTopRepresentation N)) (Nat.card I)) := by
  exact exists_non2OriginalFusionCertificate
    hTracey hExceptional hTop i
    (Rep.of (F.sectionTopRepresentation N))
    F.kernelTopPermutationSubrepresentation
    (F.sectionTopIntertwiner N)
    (F.normalSpace N).mkQ_surjective hs heven

end Certificate

section Payload

variable {s : ℕ} {U : Subgroup (Equiv.Perm (Fin (2 * s)))}
variable (F : BinaryPairFrame U (Fin s))
variable (N : {N : Subgroup U // N.Normal})
variable [MulAction.IsPretransitive F.top.range (Fin s)]

/-- Complete usable payload on a literal pair-kernel axis.  Besides the
capacity certificate, this retains the unchanged top, reversible extension
chart, and the faithful top cover needed by the same-source moment. -/
theorem exists_non2OriginalFusionAxisPayload_of_pairKernelAxis
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hN : N.1 ≤ F.top.ker) (hTop : ¬ IsPGroup 2 F.top.range)
    (i : Fin s) (hs : 24 ≤ s) (heven : Even s) :
    Nonempty (Non2OriginalFusionAxisPayload s U N) := by
  letI : N.1.Normal := N.2
  have hcertificate : Nonempty
      (Non2OriginalFusionCertificate
        (Rep.of (F.sectionTopRepresentation N.1)) s) := by
    simpa using
      (F.exists_non2OriginalFusionCertificate_of_pairSection
        N.1 hTracey hExceptional hTop i
          (by simpa using hs) (by simpa using heven))
  obtain ⟨C⟩ := hcertificate
  exact ⟨{
    B := F.top.range
    M := Rep.of (F.sectionTopRepresentation N.1)
    certificate := C
    base := F.non2TopBase N.1 hN
    base_surjective := F.non2TopBase_surjective N.1 hN
    moduleChart := F.non2TopModuleChart N.1 hN
    T := F.top.range
    topAction := F.top.range.subtype
    topAction_injective := Subtype.val_injective
    topBase := MonoidHom.id F.top.range
    topBase_surjective := Function.surjective_id }⟩

end Payload

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
