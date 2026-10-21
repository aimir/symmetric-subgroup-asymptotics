import SymmetricSubgroupAsymptotics.BinaryPairActualKernelDualSections
import SymmetricSubgroupAsymptotics.PermutationTrivialQuotientOrbitBound
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction

/-! An actual odd subgroup of the physical pair-label top bounds the
surviving pair kernel in every binary original quotient by its point-orbit
count. The exact original correlated module and normal axis are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open OriginalKernelModuleChart
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance oddOrbitSectionBoundFactPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {X I : Type} [Finite X] [Fintype I]
  {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

omit [Finite X] in
 theorem binary_section_finrank_le_odd_orbits
    (P : Subgroup F.top.range) (hP : IsPGroup 3 P)
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N)) :
    Module.finrank (ZMod 2)
      ((F.actualOriginalKernelChart).sectionModule F.top.rangeRestrict F.actualKernelModule N) ≤
        Nat.card (MulAction.orbitRel.Quotient P I) := by
  let pi := F.top.rangeRestrict
  let A := F.actualKernelModule
  let E := F.actualOriginalKernelChart
  let R := U ⧸ (pi.ker ⊔ N)
  let sigma : Representation (ZMod 2) F.top.range (E.sectionModule pi A N) :=
    (E.sectionRepresentation pi A N).ρ.comp (sectionTop pi N F.top.rangeRestrict_surjective)
  let q0 := E.sectionProjectionOnBase pi A N F.top.rangeRestrict_surjective
  let M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) P I) :=
    { toSubmodule := F.kernelSpace
      apply_mem_toSubmodule := fun p _ hv =>
        F.kernelTopPermutationSubrepresentation.apply_mem_toSubmodule p.val hv }
  letI : NeZero (Nat.card P : ZMod 2) := ⟨by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hn,Nat.cast_pow]
    exact pow_ne_zero n (show ((3 : ℕ) : ZMod 2)≠0 by decide +kernel)⟩
  have hR : IsPGroup 2 R := hQ.of_surjective (base pi N) (base_surjective pi N)
  have hz (p : P) : sectionTop pi N F.top.rangeRestrict_surjective p.val=1 := by
    let top := sectionTop pi N F.top.rangeRestrict_surjective
    have hd := IsPGroup.disjoint_of_ne 3 2 (by decide)
      (P.map top) (⊤ : Subgroup R) (hP.map top) (hR.to_subgroup ⊤)
    exact Subgroup.disjoint_def.mp hd (show top p.val∈P.map top from ⟨p.val,p.property,rfl⟩)
      (Subgroup.mem_top (top p.val))
  apply permutation_trivial_quotient_finrank_le_orbits M q0.toLinearMap
    (E.sectionProjectionOnBase_surjective pi A N F.top.rangeRestrict_surjective)
  intro p v
  change q0 (A.ρ p.val v)=q0 v
  rw [Representation.IntertwiningMap.isIntertwining]
  change (E.sectionRepresentation pi A N).ρ
    (sectionTop pi N F.top.rangeRestrict_surjective p.val) (q0 v)=q0 v
  rw [hz p,map_one]
  rfl

 theorem binary_kernel_card_le_of_odd_orbits
    (P : Subgroup F.top.range) (hP : IsPGroup 3 P) (r : ℕ)
    (horbits : Nat.card (MulAction.orbitRel.Quotient P I)≤r)
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N)) :
    Nat.card (base F.top.rangeRestrict N).ker≤2^r := by
  let pi := F.top.rangeRestrict
  let A := F.actualKernelModule
  let E := F.actualOriginalKernelChart
  let V := E.sectionModule pi A N
  letI : Finite A := by
    change Finite F.kernelSpace
    infer_instance
  letI : Finite V := Finite.of_surjective
    (E.sectionProjectionOnBase pi A N F.top.rangeRestrict_surjective)
    (E.sectionProjectionOnBase_surjective pi A N F.top.rangeRestrict_surjective)
  letI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hc : Nat.card V=2^Module.finrank (ZMod 2) V := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V))
  have he : Nat.card (base pi N).ker=Nat.card V :=
    (Nat.card_congr (E.kernelEquiv pi A N).symm.toEquiv).trans
      (Nat.card_congr (Multiplicative.toAdd : Multiplicative V≃V))
  rw [he,hc]
  exact Nat.pow_le_pow_right (by decide : 0<2)
    ((F.binary_section_finrank_le_odd_orbits P hP N hQ).trans horbits)

 theorem binary_quotient_card_le_of_odd_orbits
    (P : Subgroup F.top.range) (hP : IsPGroup 3 P) (r m : ℕ)
    (horbits : Nat.card (MulAction.orbitRel.Quotient P I)≤r)
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N))
    (hresidual : Nat.card (U ⧸ (F.top.rangeRestrict.ker ⊔ N))≤2^m) :
    Nat.card (U ⧸ N)≤2^(r+m) := by
  let f := base F.top.rangeRestrict N
  have hk := F.binary_kernel_card_le_of_odd_orbits P hP r horbits N hQ
  have he := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective f
      (base_surjective F.top.rangeRestrict N)).toEquiv
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [he] at hc
  calc
    Nat.card (U ⧸ N)=Nat.card (U ⧸ (F.top.rangeRestrict.ker ⊔ N))*Nat.card f.ker := hc
    _≤2^m*2^r := Nat.mul_le_mul hresidual hk
    _=2^(r+m) := by rw [←pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
