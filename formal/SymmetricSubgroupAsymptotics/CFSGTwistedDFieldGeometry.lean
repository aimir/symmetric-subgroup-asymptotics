import SymmetricSubgroupAsymptotics.CFSGTwistedDPointOrthogonality
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldFrobeniusEmbedding
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSemilinearDimension
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Algebra

/-! Every actual fixed-field automorphism extends by a literal prime-
Frobenius power to the original quadratic extension. Coordinate action
commutes with the defining twist and preserves the SAME fixed quadratic
form semilinearly, including its anisotropic norm plane. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFieldGeometry
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedDPointStars CFSGTwistedDPlaneFamilyAction CFSGTwistedA2FixedField
open CFSGSerreOrdinaryTwists CFSGFiniteFieldAutomorphisms

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : CharP (fixedField q) q.prime :=
  (fixedField q).subtype.charP (fixedField q).subtype.injective q.prime
local instance (q : CFSG.PrimePower) : Algebra (ZMod q.prime) (fixedField q) :=
  ZMod.algebra (fixedField q) q.prime
local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite
local instance (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    RingHomInvPair sigma.toRingHom sigma.symm.toRingHom := RingHomInvPair.of_ringEquiv sigma
local instance (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    RingHomInvPair sigma.symm.toRingHom sigma.toRingHom := RingHomInvPair.of_ringEquiv_symm sigma

def extensionExponent (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    ℕ :=
  (Classical.choose (exists_primeFrobenius_pow (fixedField q) q.prime sigma)).val

def extensionAut (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    q.Extension 2 ≃+* q.Extension 2 :=
  primeFrobenius (q.Extension 2) q.prime ^ extensionExponent q sigma

theorem extensionAut_fixed (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q)
    (a : fixedField q) : extensionAut q sigma (a : q.Extension 2) = (sigma a : q.Extension 2) := by
  have he := embedding_primeFrobenius_pow q.prime (fixedField q).subtype
    (extensionExponent q sigma) a
  have hk := Classical.choose_spec (exists_primeFrobenius_pow (fixedField q) q.prime sigma)
  change primeFrobenius (fixedField q) q.prime ^ extensionExponent q sigma = sigma at hk
  simpa only [hk] using he

theorem extensionAut_symm_fixed (q : CFSG.PrimePower)
    (sigma : fixedField q ≃+* fixedField q) (a : fixedField q) :
    (extensionAut q sigma).symm (a : q.Extension 2) = (sigma.symm a : q.Extension 2) := by
  apply (extensionAut q sigma).injective
  rw [RingEquiv.apply_symm_apply, extensionAut_fixed, sigma.apply_symm_apply]

theorem coordinate_fixed (n : ℕ) (q : CFSG.PrimePower)
    (tau : q.Extension 2 ≃+* q.Extension 2) (v : fixedSpace n q) :
    vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) (tau ∘ v.val) = tau ∘ v.val := by
  funext i
  change (tau (v.val (CFSGOrthogonalDGenerationForkTorus.flip n i))) ^ q.order = tau (v.val i)
  rw [← map_pow]
  exact congrArg tau (congrFun v.property i)

def vectorEquiv (n : ℕ) (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    fixedSpace n q ≃ₛₗ[sigma.toRingHom] fixedSpace n q where
  toFun v := ⟨extensionAut q sigma ∘ v.val, coordinate_fixed n q _ v⟩
  invFun v := ⟨(extensionAut q sigma).symm ∘ v.val, coordinate_fixed n q _ v⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    exact (extensionAut q sigma).symm_apply_apply (v.val i)
  right_inv v := by
    apply Subtype.ext
    funext i
    exact (extensionAut q sigma).apply_symm_apply (v.val i)
  map_add' v w := by
    apply Subtype.ext
    funext i
    change extensionAut q sigma (v.val i + w.val i) = _
    exact map_add _ _ _
  map_smul' a v := by
    apply Subtype.ext
    funext i
    change extensionAut q sigma ((a : q.Extension 2) * v.val i) =
      (sigma a : q.Extension 2) * extensionAut q sigma (v.val i)
    rw [map_mul, extensionAut_fixed]

theorem quadratic_map (n : ℕ) (q : CFSG.PrimePower)
    (sigma : fixedField q ≃+* fixedField q) (v : fixedSpace n q) :
    fixedQuadraticForm n q (vectorEquiv n q sigma v) = sigma (fixedQuadraticForm n q v) := by
  apply Subtype.ext
  rw [fixedQuadraticForm_apply]
  change splitQuadraticForm (q.Extension 2) (n + 2) (extensionAut q sigma ∘ v.val) = _
  have hraw : splitQuadraticForm (q.Extension 2) (n + 2) (extensionAut q sigma ∘ v.val) =
      extensionAut q sigma (splitQuadraticForm (q.Extension 2) (n + 2) v.val) := by
    simp only [splitQuadraticForm_apply, CFSGOrthogonalDIndexQuadraticForm.splitQ,
      CFSGOrthogonalDIndexQuadraticForm.leftPart, CFSGOrthogonalDIndexQuadraticForm.rightPart,
      dotProduct, Function.comp_apply, map_sum, map_mul]
  rw [hraw, ← fixedQuadraticForm_apply, extensionAut_fixed]

theorem polar_map (n : ℕ) (q : CFSG.PrimePower)
    (sigma : fixedField q ≃+* fixedField q) (v w : fixedSpace n q) :
    (fixedQuadraticForm n q).polarBilin (vectorEquiv n q sigma v) (vectorEquiv n q sigma w) =
      sigma ((fixedQuadraticForm n q).polarBilin v w) := by
  change fixedQuadraticForm n q (vectorEquiv n q sigma v + vectorEquiv n q sigma w) -
    fixedQuadraticForm n q (vectorEquiv n q sigma v) - fixedQuadraticForm n q (vectorEquiv n q sigma w) = _
  rw [← map_add, quadratic_map, quadratic_map, quadratic_map, ← map_sub, ← map_sub]
  rfl

theorem singular_map_iff (n : ℕ) (q : CFSG.PrimePower)
    (sigma : fixedField q ≃+* fixedField q) (W : Submodule (fixedField q) (fixedSpace n q)) :
    (∀ x ∈ W.map (vectorEquiv n q sigma).toLinearMap, fixedQuadraticForm n q x = 0) ↔
      ∀ x ∈ W, fixedQuadraticForm n q x = 0 := by
  constructor
  · intro h x hx
    apply sigma.injective
    rw [map_zero, ← quadratic_map]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h x ⟨v, hv, rfl⟩
    change fixedQuadraticForm n q (vectorEquiv n q sigma v) = 0
    rw [quadratic_map, h v hv, map_zero]

def pointEquiv (s : ℕ) (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    Equiv.Perm (SingularPoints s q) :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (vectorEquiv (s + 2) q sigma)).toEquiv (fun P => by
    change (Module.finrank (fixedField q) P = 1 ∧ ∀ x ∈ P, fixedQuadraticForm (s + 2) q x = 0) ↔
      (Module.finrank (fixedField q) (P.map (vectorEquiv (s + 2) q sigma).toLinearMap) = 1 ∧
        ∀ x ∈ P.map (vectorEquiv (s + 2) q sigma).toLinearMap, fixedQuadraticForm (s + 2) q x = 0)
    rw [CFSGFiniteFieldSemilinearDimension.finrank_map, singular_map_iff])

def planeEquiv (s : ℕ) (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    Equiv.Perm (SingularPlanes s q) :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (vectorEquiv (s + 2) q sigma)).toEquiv (fun P => by
    change (Module.finrank (fixedField q) P = 2 ∧ ∀ x ∈ P, fixedQuadraticForm (s + 2) q x = 0) ↔
      (Module.finrank (fixedField q) (P.map (vectorEquiv (s + 2) q sigma).toLinearMap) = 2 ∧
        ∀ x ∈ P.map (vectorEquiv (s + 2) q sigma).toLinearMap, fixedQuadraticForm (s + 2) q x = 0)
    rw [CFSGFiniteFieldSemilinearDimension.finrank_map, singular_map_iff])

theorem incidence (s : ℕ) (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q)
    (P : SingularPoints s q) (L : SingularPlanes s q) :
    (pointEquiv s q sigma P).val ≤ (planeEquiv s q sigma L).val ↔ P.val ≤ L.val :=
  Submodule.map_le_map_iff_of_injective (vectorEquiv (s + 2) q sigma).injective _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedDFieldGeometry
