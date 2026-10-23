import SymmetricSubgroupAsymptotics.CFSGFFourE6RestrictedCentralizerCapacity
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootCentralizer

/-! Concrete q^9 fixed-U centralizers over the ORIGINAL quadratic
coefficient field. The already proved finite-field embedding is fixed
by the literal q-Frobenius; no fixed-field census or unitary group
identification is used. Centralization is against the FULL extension-
field root line, via generated orthogonal root factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6QuadraticCentralizerCapacity
open CFSGFFourE6RestrictedCentralizerCapacity CFSGFFourE6CentralizerRootPilot
open CFSGFFourE6CentralizerRootTransport CFSGSerreOrdinaryTwists
open CFSGTwistedE6GeckFixedRootFamilyCover CFSGTwistedE6GeckOriginalRootCentralizer

theorem quadratic_root_centralizer_card_lower_nine (q : CFSG.PrimePower)
    (r : List (Fin 4)) : q.order^9≤Nat.card
      (fixedRootCentralizer (q.Extension 2) (definingFieldAutomorphism q 2) (transportedHighest r)) := by
  have hfix (a : q.Field) : definingFieldAutomorphism q 2
      ((CFSGTwistedA2FixedField.baseEmbedding q).toRingHom a)=
        (CFSGTwistedA2FixedField.baseEmbedding q).toRingHom a :=
    CFSGTwistedA2FixedField.baseEmbedding_fixed q a
  have h := fixed_root_centralizer_card_lower_nine
    (CFSGTwistedA2FixedField.baseEmbedding q).toRingHom (definingFieldAutomorphism q 2) hfix r
  simpa only [q.card_field] using h

theorem quadratic_menu_centralizer_card_lower_nine (q : CFSG.PrimePower)
    (k : relativeRootMenu highestRoot) : q.order^9≤Nat.card
      (fixedRootCentralizer (q.Extension 2) (definingFieldAutomorphism q 2) k.val) := by
  rcases k with ⟨k,⟨r,rfl⟩⟩
  exact quadratic_root_centralizer_card_lower_nine q r

theorem quadratic_menu_matrix_centralizer_card_lower_nine (q : CFSG.PrimePower)
    (k : relativeRootMenu highestRoot) :
    q.order^9≤Nat.card (matrixRootCentralizer q k.val) :=
  quadratic_menu_centralizer_card_lower_nine q k

end SymmetricSubgroupAsymptotics.CFSGFFourE6QuadraticCentralizerCapacity
