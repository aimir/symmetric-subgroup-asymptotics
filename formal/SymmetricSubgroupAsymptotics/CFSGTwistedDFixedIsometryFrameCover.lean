import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryFirstPair
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDBasePairTailIsometry
import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPairAlignment

/-! Direct fixed-field frame elimination of EVERY actual Q-isometry.
One literal relative-root word leaves exactly a linear isometry of the
anisotropic norm plane. The induction never assumes a K-linear lift or
membership in the ambient elementary component. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryFrameCover
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedTailLinear CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeTailEmbedding CFSGTwistedDMaximalSpaceOrbit
open CFSGTwistedDOpposedPairAlignment CFSGTwistedDAnisotropicNormForm
open CFSGTwistedDBasePoleCoordinates CFSGTwistedA2FixedField

theorem tail_root_coordinates (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace (n + 1) q) :
    poleEquiv n q (fixedLinearHom (n + 1) q (tailRelativeHom n q g) v) =
      (positiveHead n q v, (fixedLinearHom n q g (tailLinear n q v), negativeHead n q v)) :=
  Prod.ext (positiveHead_fixed_action n q g v)
    (Prod.ext (tail_fixed_action n q g v) (negativeHead_fixed_action n q g v))

theorem exists_residual (n : ℕ) (q : CFSG.PrimePower)
    (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q)
    (hQ : ∀ v, fixedQuadraticForm n q (L v) = fixedQuadraticForm n q v) :
    ∃ (g : relativeRootGroup n q) (T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2),
      (∀ a, normForm q (T a) = normForm q a) ∧
      ∀ v, fixedLinearHom n q g (L v) = CFSGTwistedDNormPlaneLift.lift n q T v := by
  induction n with
  | zero =>
    obtain ⟨g, he, hf⟩ := CFSGTwistedDFixedIsometryFirstPair.exists_normalize 0 q L hQ
    let M := L.trans (fixedLinearHom 0 q g)
    have hM (v) : fixedQuadraticForm 0 q (M v) = fixedQuadraticForm 0 q v :=
      (fixedLinearHom_preserves_Q 0 q g (L v)).trans (hQ v)
    obtain ⟨T, hT, hMT⟩ := CFSGTwistedDBasePairTailIsometry.exists_tail q M hM he hf
    refine ⟨g, T, hT, ?_⟩
    intro v
    apply (basePoleEquiv q).injective
    rw [CFSGTwistedDNormPlaneLift.base_coordinates]
    exact hMT v
  | succ n ih =>
    obtain ⟨a, he, hf⟩ := CFSGTwistedDFixedIsometryFirstPair.exists_normalize (n + 1) q L hQ
    let M := L.trans (fixedLinearHom (n + 1) q a)
    have hM (v) : fixedQuadraticForm (n + 1) q (M v) = fixedQuadraticForm (n + 1) q v :=
      (fixedLinearHom_preserves_Q (n + 1) q a (L v)).trans (hQ v)
    obtain ⟨U, hU, hMU⟩ := CFSGTwistedDFixedPairTailIsometry.exists_tail n q M hM he hf
    obtain ⟨b, T, hT, hres⟩ := ih U hU
    refine ⟨tailRelativeHom n q b * a, T, hT, ?_⟩
    intro v
    have hact : fixedLinearHom (n + 1) q (tailRelativeHom n q b * a) (L v) =
        fixedLinearHom (n + 1) q (tailRelativeHom n q b) (M v) := by
      rw [map_mul]
      rfl
    apply (poleEquiv n q).injective
    rw [hact, tail_root_coordinates, CFSGTwistedDNormPlaneLift.pole_coordinates]
    have hp := congrArg Prod.fst (hMU v)
    have ht := congrArg (fun x => x.2.1) (hMU v)
    have hn := congrArg (fun x => x.2.2) (hMU v)
    change positiveHead n q (M v) = positiveHead n q v at hp
    change tailLinear n q (M v) = U (tailLinear n q v) at ht
    change negativeHead n q (M v) = negativeHead n q v at hn
    rw [hp, ht, hn, hres]

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryFrameCover
