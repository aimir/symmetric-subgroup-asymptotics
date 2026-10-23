import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarRootParameters

/-! Every ORIGINAL automorphism stabilizing the literal singular
two-plane acts additively on its actual Hermitian coefficients and
permutes exactly the fixed-scalar rank-one lines. The construction
uses the proved intrinsic-star equality and faithful coefficient map;
no fixed-field linearity is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists

private def coordinateConjugate {A G : Type*} [Group A] [Group G] (H : Subgroup G)
    (Phi : A ≃* H) (f : MulAut G) (hH : H.map f.toMonoidHom = H) : MulAut A :=
  (Phi.trans ((f.subgroupMap H).trans (MulEquiv.subgroupCongr hH))).trans Phi.symm

private theorem coordinateConjugate_apply {A G : Type*} [Group A] [Group G] (H : Subgroup G)
    (Phi : A ≃* H) (f : MulAut G) (hH : H.map f.toMonoidHom = H) (x : A) :
    (Phi (coordinateConjugate H Phi f hH x)).val = f (Phi x).val := by
  change (Phi (Phi.symm (((f.subgroupMap H).trans (MulEquiv.subgroupCongr hH)) (Phi x)))).val = _
  rw [Phi.apply_symm_apply]
  rfl

private def addEquivOfMultiplicative {A : Type*} [AddGroup A]
    (E : Multiplicative A ≃* Multiplicative A) : A ≃+ A where
  toFun x := (E (Multiplicative.ofAdd x)).toAdd
  invFun x := (E.symm (Multiplicative.ofAdd x)).toAdd
  left_inv x := congrArg Multiplicative.toAdd (E.symm_apply_apply (Multiplicative.ofAdd x))
  right_inv x := congrArg Multiplicative.toAdd (E.apply_symm_apply (Multiplicative.ofAdd x))
  map_add' x y := congrArg Multiplicative.toAdd (E.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

private theorem additive_line_transport {A G : Type*} [AddGroup A] [Group G]
    (phi : Multiplicative A →* G) (hphi : Function.Injective phi) (E : A ≃+ A) (f : MulAut G)
    (hcompat : ∀ x, phi (Multiplicative.ofAdd (E x)) = f (phi (Multiplicative.ofAdd x)))
    (L M : AddSubgroup A) (U V : Subgroup G)
    (hL : ∀ x, phi (Multiplicative.ofAdd x) ∈ U ↔ x ∈ L)
    (hM : ∀ x, phi (Multiplicative.ofAdd x) ∈ V ↔ x ∈ M)
    (hUV : U.map f.toMonoidHom = V) : L.map E.toAddMonoidHom = M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (hM _).mp
    change phi (Multiplicative.ofAdd (E y)) ∈ V
    rw [hcompat, ← hUV]
    exact ⟨_, (hL y).mpr hy, rfl⟩
  · intro hx
    have hx' := (hM x).mpr hx
    rw [← hUV] at hx'
    obtain ⟨g, hg, he⟩ := hx'
    have hE := hcompat (E.symm x)
    rw [E.apply_symm_apply] at hE
    have hg' : g = phi (Multiplicative.ofAdd (E.symm x)) := f.injective (he.trans hE)
    refine ⟨E.symm x, ?_, E.apply_symm_apply x⟩
    apply (hL _).mp
    rw [← hg']
    exact hg

def unitaryStarCoefficientAut (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2) ≃+
      CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2) :=
  addEquivOfMultiplicative (coordinateConjugate (unitaryRootStar q s (starPlane q s))
    (projectiveHermitianStarEquiv q s t ht htc) f
    (unitaryRootStar_map_of_incidence q s f _ _ hinc))

theorem unitaryStarCoefficientAut_intertwines (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s)
    (A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) :
    projectiveHermitianStarHom q s t ht htc
      (Multiplicative.ofAdd (unitaryStarCoefficientAut q s t ht htc f hinc A)) =
      f (projectiveHermitianStarHom q s t ht htc (Multiplicative.ofAdd A)) :=
  coordinateConjugate_apply (unitaryRootStar q s (starPlane q s))
    (projectiveHermitianStarEquiv q s t ht htc) f
    (unitaryRootStar_map_of_incidence q s f _ _ hinc) (Multiplicative.ofAdd A)

theorem unitaryStarCoefficientAut_rootLine (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s)
    (v w : Fin 2 → q.Extension 2) (hv : v ≠ 0) (hw : w ≠ 0)
    (he : unitarySingularPointActionHom q s f (starPoint q s v hv) = starPoint q s w hw) :
    (CFSGHermitianTwoByTwoRankOne.rankOneLine (definingFieldAutomorphism q 2)
      (fun z => extension_two_pow_twice q z) v).map
        (unitaryStarCoefficientAut q s t ht htc f hinc).toAddMonoidHom =
      CFSGHermitianTwoByTwoRankOne.rankOneLine (definingFieldAutomorphism q 2)
        (fun z => extension_two_pow_twice q z) w := by
  apply additive_line_transport (projectiveHermitianStarHom q s t ht htc)
    (projectiveHermitianStarHom_injective q s t ht htc)
    (unitaryStarCoefficientAut q s t ht htc f hinc) f
    (unitaryStarCoefficientAut_intertwines q s t ht htc f hinc)
    _ _ (unitaryPointRoot q s (starPoint q s v hv)) (unitaryPointRoot q s (starPoint q s w hw))
    (projectiveHermitian_mem_pointRoot_iff q s t ht htc v hv)
    (projectiveHermitian_mem_pointRoot_iff q s t ht htc w hw)
  rw [unitaryPointRoot_action, he]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
