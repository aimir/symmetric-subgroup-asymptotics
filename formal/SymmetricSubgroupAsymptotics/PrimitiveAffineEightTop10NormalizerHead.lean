import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop10TopCertificate
import SymmetricSubgroupAsymptotics.GeneratedSylowNormalizerPointCertificate
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

/-! Selected top 10: unchanged literal action; only 9 Sylow rows.
Generated from SHA-checked selected producer data. All finite identities are kernel checked. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop10NormalizerHead

abbrev Source := PrimitiveAffineEightFrameTop10TopCertificate.Source
local instance : Group Source := PrimitiveAffineEightFrameTop10TopCertificate.group
abbrev Literal := Subgroup.closure (Set.range PrimitiveAffineEightFrameTop10TopCertificate.generators)

local instance sourceAction : MulAction Source (Fin 8) :=
  MulAction.compHom (Fin 8) PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.toMonoidHom

def transporterWord : Fin 8 → List (Fin 9) :=
  ![[], [5], [3, 4], [4], [8], [8, 5], [8, 3, 4], [8, 4]]
def transporter (x : Fin 8) : Source :=
  ((transporterWord x).map PrimitiveAffineEightFrameTop10TopCertificate.ambient).prod

theorem transporter_point : ∀ x : Fin 8, transporter x • (0 : Fin 8) = x := by
  decide +kernel

local instance sourceTransitive : MulAction.IsPretransitive Source (Fin 8) := ⟨by
  intro x y
  refine ⟨transporter y * (transporter x)⁻¹, ?_⟩
  have hx : (transporter x)⁻¹ • x = (0 : Fin 8) := by
    calc
      (transporter x)⁻¹ • x = (transporter x)⁻¹ • (transporter x • (0 : Fin 8)) :=
        congrArg (fun z : Fin 8 => (transporter x)⁻¹ • z) (transporter_point x).symm
      _ = 0 := inv_smul_smul _ _
  rw [mul_smul, hx, transporter_point]⟩

def sylowGenerator : Fin 2 → Source :=
  ![PrimitiveAffineEightFrameTop10TopCertificate.ambient 0 * (PrimitiveAffineEightFrameTop10TopCertificate.ambient 3)⁻¹, PrimitiveAffineEightFrameTop10TopCertificate.ambient 0]
def normalizer : Source := PrimitiveAffineEightFrameTop10TopCertificate.ambient 2 * PrimitiveAffineEightFrameTop10TopCertificate.ambient 3 * PrimitiveAffineEightFrameTop10TopCertificate.ambient 7 * PrimitiveAffineEightFrameTop10TopCertificate.ambient 8

def sylowWord : Fin 9 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 1], [0, 0, 1], [0, 1, 1], [0, 0, 1, 1]]
def sylowElement (i : Fin 9) : Source :=
  ((sylowWord i).map sylowGenerator).prod
def sylowNext : Fin 9 → Fin 2 → Fin 9 :=
  ![![1, 2], ![3, 4], ![4, 5], ![0, 6], ![6, 7], ![7, 0], ![2, 8], ![8, 1], ![5, 3]]
def cayley : FiniteCayleyCertificate sylowGenerator 9 where
  elements := sylowElement
  identity := 0
  identity_eq := by decide +kernel
  next := sylowNext
  next_eq := by decide +kernel
  words := sylowWord
  words_eq := by decide +kernel

theorem rows_injective : Function.Injective cayley.elements := by decide +kernel

def path : Fin 8 → List (Fin 2 ⊕ Fin 2) :=
  ![[], [], [.inl 0], [.inl 0, .inl 0], [], [.inr 1, .inl 0, .inl 0], [.inr 1], [.inr 1, .inl 0]]
def pointCertificate :
    GeneratedSylowNormalizerPointCertificate.Certificate (G := Source) (Fin 8) 2 9 where
  generators := sylowGenerator
  cayley := cayley
  rows_injective := rows_injective
  group_factorization := by rw [PrimitiveAffineEightFrameTop10TopCertificate.source_card]; decide +kernel
  normalizer := normalizer
  forward := by
    intro j
    apply (cayley.mem_closure_iff _).mpr
    fin_cases j
    · exact ⟨8, by decide +kernel⟩
    · exact ⟨6, by decide +kernel⟩
  backward := by
    intro j
    apply (cayley.mem_closure_iff _).mpr
    fin_cases j
    · exact ⟨4, by decide +kernel⟩
    · exact ⟨7, by decide +kernel⟩
  representative := 1
  path := path
  covers := by decide +kernel

abbrev literalStabilizer := MulAction.stabilizer Literal (0 : Fin 8)
abbrev stabilizer := MulAction.stabilizer Source (0 : Fin 8)

def stabilizerEquiv : stabilizer ≃* literalStabilizer where
  toFun h := ⟨PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv h.1, h.2⟩
  invFun h := ⟨PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.symm h.1, by
    change PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv
      (PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.symm h.1) ∈ literalStabilizer
    rw [MulEquiv.apply_symm_apply]
    exact h.2⟩
  left_inv h := Subtype.ext
    (PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.symm_apply_apply h.1)
  right_inv h := Subtype.ext
    (PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.apply_symm_apply h.1)
  map_mul' h k := Subtype.ext
    (PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.map_mul h.1 k.1)

theorem source_head_le_two {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : stabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod 2) L V)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind stabilizer.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Source (ZMod 2))) ≤ 2 :=
  pointCertificate.head_le_two 0 f hf rho hL hdim hrho B

theorem literal_head_le_two {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : literalStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod 2) L V)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind literalStabilizer.subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Literal (ZMod 2))) ≤ 2 := by
  let eG := PrimitiveAffineEightFrameTop10TopCertificate.originalEquiv.symm
  let f' := f.comp stabilizerEquiv.toMonoidHom
  let eV : Representation.Equiv (rho.comp f)
      ((rho.comp f').comp stabilizerEquiv.symm.toMonoidHom) := {
    toLinearEquiv := LinearEquiv.refl (ZMod 2) V
    isIntertwining' := by
      intro h
      ext v
      change rho (f h) v = rho (f (stabilizerEquiv (stabilizerEquiv.symm h))) v
      rw [stabilizerEquiv.apply_symm_apply] }
  exact CoinducedGroupLocalTransport.uniform_head_le literalStabilizer stabilizer
    eG stabilizerEquiv.symm (fun _ => rfl) (rho.comp f) (rho.comp f') eV 2
    (fun A => source_head_le_two f' (hf.comp stabilizerEquiv.surjective) hL rho hdim hrho A) B

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop10NormalizerHead

end
