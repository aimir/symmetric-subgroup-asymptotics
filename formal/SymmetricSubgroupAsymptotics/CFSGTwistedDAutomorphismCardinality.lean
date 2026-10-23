import SymmetricSubgroupAsymptotics.CFSGTwistedDAutomorphismGeometry
import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGroup

/-! The faithful original automorphism action is encoded by a genuine
fixed-field automorphism and the point image of an actual similitude.
Scalar-kernel cancellation bounds that point image by the full original
fixed-Q isometry group. No isometry index or outer-order bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAutomorphismCardinality
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDAutomorphismGeometry CFSGTwistedDPointAction
open CFSGTwistedDMaximalSingularDimension CFSGTwistedDPointStars CFSGTwistedA2FixedField
open CFSGQuadraticSimilitudeGroup CFSGOrthogonalDIndexQuadraticSubspacePoints

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite
local instance (n : ℕ) (q : CFSG.PrimePower) :
    Finite (fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q) :=
  Finite.of_injective (fun L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q =>
    (L : fixedSpace n q → fixedSpace n q)) DFunLike.coe_injective
local instance (q : CFSG.PrimePower) : Finite (fixedField q ≃+* fixedField q) :=
  Finite.of_injective (fun sigma : fixedField q ≃+* fixedField q =>
    (sigma : fixedField q → fixedField q)) DFunLike.coe_injective

theorem original_card_aut_le_field_mul_isometries (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    Nat.card (MulAut (CFSG.Models.TwistedD (s + 4) q)) ≤
      Nat.card (fixedField q ≃+* fixedField q) *
        Nat.card (isometries (fixedQuadraticForm (s + 2) q)) := by
  classical
  let Q := fixedQuadraticForm (s + 2) q
  let x : Fin (s + 3) → fixedField q := fun _ => 1
  have hx : positiveEmbedding (s + 2) q x ≠ 0 := by
    intro he
    have hz := positiveEmbedding_injective (s + 2) q (he.trans (map_zero _).symm)
    have hh := congrFun hz (0 : Fin (s + 3))
    exact one_ne_zero hh
  letI : Nontrivial (fixedSpace (s + 2) q) := ⟨⟨_, 0, hx⟩⟩
  choose sigma t L ht hL hpoints using
    (fun f : MulAut (CFSG.Models.TwistedD (s + 4) q) => original_exists_field_linear_factor s q f)
  let lift : MulAut (CFSG.Models.TwistedD (s + 4) q) → similitudes Q :=
    fun f => ⟨(L f, Units.mk0 (t f) (ht f)), hL f⟩
  let encode : MulAut (CFSG.Models.TwistedD (s + 4) q) →
      (fixedField q ≃+* fixedField q) × (pointHom Q).range :=
    fun f => (sigma f, ⟨pointHom Q (lift f), ⟨lift f, rfl⟩⟩)
  have hinj : Function.Injective encode := by
    intro f g he
    have hs : sigma f = sigma g := congrArg Prod.fst he
    have hp : pointHom Q (lift f) = pointHom Q (lift g) :=
      congrArg (fun z : (fixedField q ≃+* fixedField q) × (pointHom Q).range => z.2.val) he
    apply originalPointActionHom_injective s q
    apply Equiv.ext
    intro P
    apply Subtype.ext
    rw [hpoints f, hpoints g, hs]
    have hPL := congrArg (fun e : Equiv.Perm (Points Q) => (e P).val) hp
    change P.val.map (L f).toLinearMap = P.val.map (L g).toLinearMap at hPL
    rw [hPL]
  have hc := Nat.card_le_card_of_injective encode hinj
  rw [Nat.card_prod] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (pointImage_card_le_isometries Q))

end SymmetricSubgroupAsymptotics.CFSGTwistedDAutomorphismCardinality
