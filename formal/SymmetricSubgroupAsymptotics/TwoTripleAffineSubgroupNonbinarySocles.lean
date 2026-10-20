import SymmetricSubgroupAsymptotics.TwoTripleSignedUpperFaithful
import SymmetricSubgroupAsymptotics.TernaryTwoBlockMonomialNonbinaryQuotientSocles

/-! Every actual affine subgroup exchanging the two ternary blocks has
one-generator socle on ALL nonbinary original normal quotients. The affine
subgroup need not contain a complement or the full translation plane. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTripleAffineSubgroupNonbinarySocles
open TwoTripleSignedUpperLinearAction TwoTripleSignedAffineCoordinates
open LinearSemidirectSubgroupKernelChart LinearSemidirectActualImageKernelChart

private def coordinates : Upper ≃ (Binary × Binary) × Binary where
  toFun g := (g.left,g.right)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance affineSocleUpperFintype : Fintype Upper :=
  Fintype.ofEquiv ((Binary × Binary) × Binary) coordinates.symm

local instance affineSocleModelFinite : Finite Affine :=
  Finite.of_injective (fun g : Affine => (g.left,g.right)) (by
    intro g h he
    exact SemidirectProduct.ext (congrArg Prod.fst he) (congrArg Prod.snd he))

private theorem swap_sends : ∀ u : Upper, u.right=C2Wreath.gen →
    ∀ i j : Fin 2, i≠j → blocks u i=j := by decide +kernel

variable (K : Subgroup Affine)

/-- The binary image is the actual upper projection of K. -/
theorem quotient_socle_one
    (hswap : ∃ u : Image linearAction K, (u : Upper).right=C2Wreath.gen)
    (N : Subgroup K) [N.Normal] (hQ : ¬IsPGroup 2 (K ⧸ N)) :
    SocleNormalGeneratorBound (K ⧸ N) 1 := by
  let U := Image linearAction K
  let b : U →* Equiv.Perm (Fin 2) := blocks.comp U.subtype
  let d : U → Fin 2 → ZMod 3 := fun u => coefficient u.val
  have hone : ∀ i, d 1 i=1 := coefficient_one
  have hmul : ∀ u v i, d (u*v) i=d u i*d v (b u⁻¹ i) := by
    intro u v i
    exact coefficient_mul u.val v.val i
  have htrans : ∀ i j : Fin 2, ∃ u : U, b u i=j := by
    obtain ⟨u,hu⟩ := hswap
    intro i j
    by_cases hij : i=j
    · exact ⟨1,by simpa only [map_one,Equiv.Perm.one_apply] using hij⟩
    · exact ⟨u,swap_sends u.val hu i j hij⟩
  have hfaithful : Function.Injective
      (TernaryTwoBlockMonomialNonbinaryQuotientSocles.ambient b d hone hmul) := by
    intro u v h
    apply Subtype.ext
    apply TwoTripleSignedUpperFaithful.faithful
    exact h
  let A := LinearSemidirectActualImageKernelChart.kernelModule linearAction K
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart linearAction K
  letI : FiniteDimensional (ZMod 3) A := by
    change FiniteDimensional (ZMod 3) (translationSpace linearAction K)
    infer_instance
  exact TernaryTwoBlockMonomialNonbinaryQuotientSocles.quotientSocle b d hone hmul
    (TwoTripleSignedUpperFaithful.binary U) htrans hfaithful
    (top linearAction K) (projection linearAction K).rangeRestrict_surjective
    A E (LinearSemidirectActualImageKernelChart.inclusion linearAction K)
    (LinearSemidirectActualImageKernelChart.inclusion_injective linearAction K) N hQ

end SymmetricSubgroupAsymptotics.TwoTripleAffineSubgroupNonbinarySocles
