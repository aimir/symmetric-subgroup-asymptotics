import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalFixedCorrespondence
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSL
import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangularPGroup

/-! A literal upper-unitriangular defining-characteristic subgroup in the
SAME original twisted-A fixed source, all ranks and all prime powers.
The natural subgroup is the exact intersection of upper-unitriangular
matrices with the defining diagram-field fixed equation. Its source
injection is proved from the actual scalar action kernel and diagonal1.
No full-SU equality, Sylow assertion or derived inclusion is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUpperUnipotent
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGTwistedAIntervalSource
open CFSGSerreSquareZeroMatrix CFSGSerreOrdinaryTwists

abbrev Fixed (r : ℕ) (q : CFSG.PrimePower) :=
  fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)

def naturalFixed (r : ℕ) (q : CFSG.PrimePower) :
    Subgroup (NaturalElementary (q.Extension 2) r) :=
  ((diagramFieldUnitHom (q.Extension 2) r
    (definingFieldAutomorphism q 2).toRingHom).comp
      (NaturalElementary (q.Extension 2) r).subtype).eqLocus
        (NaturalElementary (q.Extension 2) r).subtype

def naturalUnipotent (r : ℕ) (q : CFSG.PrimePower) :
    Subgroup (NaturalElementary (q.Extension 2) r) :=
  (CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) (r + 1)).comap
    (naturalToSpecialLinear (q.Extension 2) r) ⊓ naturalFixed r q

theorem naturalUnipotent_fixed (r : ℕ) (q : CFSG.PrimePower) (g : naturalUnipotent r q) :
    diagramFieldUnitHom (q.Extension 2) r (definingFieldAutomorphism q 2).toRingHom
      g.val.val = g.val.val := g.property.2

def upperMatrixHom (r : ℕ) (q : CFSG.PrimePower) : naturalUnipotent r q →*
    CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) (r + 1) where
  toFun g := ⟨naturalToSpecialLinear (q.Extension 2) r g.val, g.property.1⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem upperMatrixHom_injective (r : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (upperMatrixHom r q) := by
  intro g h he
  apply Subtype.ext
  apply (naturalSpecialLinearEquiv (q.Extension 2) r).injective
  exact congrArg (fun u : CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) (r + 1) =>
    u.val) he

theorem naturalUnipotent_isPGroup (r : ℕ) (q : CFSG.PrimePower) :
    IsPGroup q.prime (naturalUnipotent r q) := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact (CFSGUpperUnitriangular.upperUnitriangular_isPGroup
    (F := q.Extension 2) (p := q.prime) (r + 1)).of_injective
      (upperMatrixHom r q) (upperMatrixHom_injective r q)

def unipotentToOriginalFixed (r : ℕ) (q : CFSG.PrimePower) :
    naturalUnipotent r q →* Fixed r q where
  toFun g := fixedElementOfNaturalUnit r q g.val (naturalUnipotent_fixed r q g)
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun g : Model (CartanMatrix.A r) (q.Extension 2) => g.val)
      (map_one (elementaryToModel (q.Extension 2) r))
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun g : Model (CartanMatrix.A r) (q.Extension 2) => g.val)
      (map_mul (elementaryToModel (q.Extension 2) r) g.val h.val)

theorem unipotentToOriginalFixed_injective (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower) :
    Function.Injective (unipotentToOriginalFixed r q) := by
  apply (unipotentToOriginalFixed r q).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  change g = 1
  change unipotentToOriginalFixed r q g = 1 at hg
  have hsource : elementaryToModel (q.Extension 2) r g.val = 1 := by
    apply Subtype.ext
    exact congrArg (fun h : Fixed r q => h.val) hg
  have haction : naturalElementaryAction (q.Extension 2) r g.val = 1 := by
    rw [← elementaryToModel_action, hsource, map_one]
  have hk : g.val ∈ (naturalElementaryAction (q.Extension 2) r).ker := haction
  rw [naturalElementaryAction_ker (q.Extension 2) r hr] at hk
  obtain ⟨c, hc⟩ := (naturalElementary_center_iff_scalar (q.Extension 2) r hr g.val).mp hk
  have hdiag : (g.val.val : Mat (q.Extension 2) r) 0 0 = 1 := g.property.1.2 0
  have hs := congrArg (fun M : Mat (q.Extension 2) r => M 0 0) hc
  change (g.val.val : Mat (q.Extension 2) r) 0 0 =
    (c • (1 : Mat (q.Extension 2) r)) 0 0 at hs
  rw [hdiag] at hs
  have hcone : c = 1 := by
    simpa only [Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one] using hs.symm
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (g.val.val : Mat (q.Extension 2) r) = 1
  rw [hc, hcone, one_smul]

def originalUnipotent (r : ℕ) (q : CFSG.PrimePower) : Subgroup (Fixed r q) :=
  (unipotentToOriginalFixed r q).range

theorem originalUnipotent_isPGroup (r : ℕ) (q : CFSG.PrimePower) :
    IsPGroup q.prime (originalUnipotent r q) :=
  (naturalUnipotent_isPGroup r q).of_surjective
    (unipotentToOriginalFixed r q).rangeRestrict
    (unipotentToOriginalFixed r q).rangeRestrict_surjective

end SymmetricSubgroupAsymptotics.CFSGTwistedAUpperUnipotent
