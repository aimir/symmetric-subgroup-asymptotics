import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIsotropicPointCoverage
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralPointOrthogonality
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralPointFaithful

/-! The faithful original-model automorphism action is on ALL literal
signed-isotropic natural point lines, not only a chosen natural orbit.
Actual vector clearing proves the equality of the two point carriers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

theorem unitaryCentralVector_ne_zero (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) : unitaryCentralVector q s g ≠ 0 := by
  have h := matrixUnit_column_ne_zero g.val.val (0 : Fin (s + 4))
  simpa only [unitaryCentralVector, Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem unitaryCentralPoints_iff_singular (q : CFSG.PrimePower) (s : ℕ)
    (P : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2)) :
    (∃ g : naturalFixed (s + 3) q, conjugateCentralPoint q (s + 1) g = P) ↔
      Module.finrank (q.Extension 2) P = 1 ∧ ∀ v ∈ P, unitaryNaturalPair q (s + 3) v v = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [conjugateCentralPoint_eq_span]
    change Module.finrank (q.Extension 2) ((q.Extension 2) ∙ unitaryCentralVector q s g) = 1 ∧ _
    refine ⟨finrank_span_singleton (unitaryCentralVector_ne_zero q s g), ?_⟩
    intro v hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    rw [← ha]
    change hermitianPair (definingFieldAutomorphism q 2) _ (a • _) (a • _) = 0
    rw [hermitianPair_smul]
    change definingFieldAutomorphism q 2 a * a * unitaryNaturalPair q (s + 3)
      (unitaryCentralVector q s g) (unitaryCentralVector q s g) = 0
    rw [unitaryCentralVector_pair, centralRootAxisFunctional_self, mul_zero]
  · rintro ⟨hd, hnorm⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp (by rw [hd]))
    have he : (q.Extension 2) ∙ v = P :=
      Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hv)
        (by rw [hd, finrank_span_singleton hv0])
    obtain ⟨g, hg⟩ := exists_conjugateCentralPoint_of_isotropic q s v hv0 (hnorm v hv)
    exact ⟨g, hg.trans he⟩

def unitarySingularPoints (q : CFSG.PrimePower) (s : ℕ) :=
  {P : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) //
    Module.finrank (q.Extension 2) P = 1 ∧ ∀ v ∈ P, unitaryNaturalPair q (s + 3) v v = 0}

def unitaryCentralSingularPointEquiv (q : CFSG.PrimePower) (s : ℕ) :
    unitaryCentralPoints q s ≃ unitarySingularPoints q s where
  toFun P := ⟨P.val, (unitaryCentralPoints_iff_singular q s P.val).mp P.property⟩
  invFun P := ⟨P.val, (unitaryCentralPoints_iff_singular q s P.val).mpr P.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def unitarySingularPointActionHom (q : CFSG.PrimePower) (s : ℕ) :
    MulAut (CFSG.Models.TwistedA (s + 3) q) →* Equiv.Perm (unitarySingularPoints q s) :=
  (unitaryCentralSingularPointEquiv q s).permCongrHom.toMonoidHom.comp
    (unitaryCentralPointActionHom q s)

theorem unitarySingularPointActionHom_injective (q : CFSG.PrimePower) (s : ℕ)
    [IsSimpleGroup (CFSG.Models.TwistedA (s + 3) q)] :
    Function.Injective (unitarySingularPointActionHom q s) :=
  (unitaryCentralSingularPointEquiv q s).permCongrHom.injective.comp
    (unitaryCentralPointActionHom_injective q s)

theorem unitarySingularPointAction_preserves_orthogonality (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (P Q : unitarySingularPoints q s) :
    (∀ v ∈ (unitarySingularPointActionHom q s f P).val,
      ∀ w ∈ (unitarySingularPointActionHom q s f Q).val, unitaryNaturalPair q (s + 3) v w = 0) ↔
        ∀ v ∈ P.val, ∀ w ∈ Q.val, unitaryNaturalPair q (s + 3) v w = 0 :=
  unitaryCentralPointAction_preserves_orthogonality q s f
    ((unitaryCentralSingularPointEquiv q s).symm P) ((unitaryCentralSingularPointEquiv q s).symm Q)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
