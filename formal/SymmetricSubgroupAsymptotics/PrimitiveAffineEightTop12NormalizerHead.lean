import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21TopCertificate
import SymmetricSubgroupAsymptotics.GeneratedSylowNormalizerPointCertificate
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

/-! Selected top 12: unchanged literal action; only 3 Sylow rows.
Generated from SHA-checked selected producer data. All finite identities are kernel checked. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop12NormalizerHead

abbrev Source := PrimitiveAffineEightFrameRow21TopCertificate.Source
local instance : Group Source := PrimitiveAffineEightFrameRow21TopCertificate.group
abbrev Literal := Subgroup.closure (Set.range PrimitiveAffineEightFrameRow21TopCertificate.generators)

local instance sourceAction : MulAction Source (Fin 8) :=
  MulAction.compHom (Fin 8) PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.toMonoidHom

def transporterWord : Fin 8 → List (Fin 5) :=
  ![[], [0], [3], [3, 0], [3, 3], [3, 3, 0], [4, 3, 3], [4, 3, 3, 0]]
def transporter (x : Fin 8) : Source :=
  ((transporterWord x).map PrimitiveAffineEightFrameRow21TopCertificate.ambient).prod

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

def sylowGenerator : Fin 1 → Source :=
  ![PrimitiveAffineEightFrameRow21TopCertificate.ambient 4 * PrimitiveAffineEightFrameRow21TopCertificate.ambient 3]
def normalizer : Source := PrimitiveAffineEightFrameRow21TopCertificate.ambient 0 * PrimitiveAffineEightFrameRow21TopCertificate.ambient 2

def sylowWord : Fin 3 → List (Fin 1) :=
  ![[], [0], [0, 0]]
def sylowElement (i : Fin 3) : Source :=
  ((sylowWord i).map sylowGenerator).prod
def sylowNext : Fin 3 → Fin 1 → Fin 3 :=
  ![![1], ![2], ![0]]
def cayley : FiniteCayleyCertificate sylowGenerator 3 where
  elements := sylowElement
  identity := 0
  identity_eq := by decide +kernel
  next := sylowNext
  next_eq := by decide +kernel
  words := sylowWord
  words_eq := by decide +kernel

theorem rows_injective : Function.Injective cayley.elements := by decide +kernel

def path : Fin 8 → List (Fin 1 ⊕ Fin 2) :=
  ![[], [], [], [.inr 0], [.inl 0, .inl 0], [.inr 0, .inl 0, .inl 0], [.inl 0], [.inl 0, .inr 0]]
def pointCertificate :
    GeneratedSylowNormalizerPointCertificate.Certificate (G := Source) (Fin 8) 1 3 where
  generators := sylowGenerator
  cayley := cayley
  rows_injective := rows_injective
  group_factorization := by rw [PrimitiveAffineEightFrameRow21TopCertificate.source_card]; decide +kernel
  normalizer := normalizer
  forward := by
    intro j
    apply (cayley.mem_closure_iff _).mpr
    fin_cases j
    · exact ⟨1, by decide +kernel⟩
  backward := by
    intro j
    apply (cayley.mem_closure_iff _).mpr
    fin_cases j
    · exact ⟨1, by decide +kernel⟩
  representative := 2
  path := path
  covers := by decide +kernel

abbrev literalStabilizer := MulAction.stabilizer Literal (0 : Fin 8)
abbrev stabilizer := MulAction.stabilizer Source (0 : Fin 8)

def stabilizerEquiv : stabilizer ≃* literalStabilizer where
  toFun h := ⟨PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv h.1, h.2⟩
  invFun h := ⟨PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.symm h.1, by
    change PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv
      (PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.symm h.1) ∈ literalStabilizer
    rw [MulEquiv.apply_symm_apply]
    exact h.2⟩
  left_inv h := Subtype.ext
    (PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.symm_apply_apply h.1)
  right_inv h := Subtype.ext
    (PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.apply_symm_apply h.1)
  map_mul' h k := Subtype.ext
    (PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.map_mul h.1 k.1)

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
  let eG := PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.symm
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

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop12NormalizerHead

end
