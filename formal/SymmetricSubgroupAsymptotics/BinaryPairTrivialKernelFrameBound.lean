import SymmetricSubgroupAsymptotics.BinaryPairTernaryOrbitHead
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! The faithful-pair-action branch of the sixteen-point frame inequality.
When the original pair kernel is trivial, the original ambient and its
actual eight-pair range are equivalent. Every original normal subgroup is
transported together with ambient conjugation; no subgroup monotonicity is
used. The moving-orbit theorem supplies the original frame head bound8. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (hker : F.top.ker = ⊥)

/-- Equivalence with the actual pair range, using the original top map. -/
def faithfulTopEquiv : U ≃* F.top.range :=
  MulEquiv.ofBijective F.top.rangeRestrict
    ⟨fun _ _ h => (MonoidHom.ker_eq_bot_iff F.top).mp hker
      (congrArg (fun z : F.top.range => (z : Equiv.Perm I)) h),
      F.top.rangeRestrict_surjective⟩

include hker in
theorem trivialKernel_relativeHead_le_two
    (htop : ∀ (M : Subgroup F.top.range) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2)
    (N : Subgroup U) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 := by
  let e := F.faithfulTopEquiv hker
  let M : Subgroup F.top.range := N.map e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have he := relativeCharacterAmbientCongr 2 e N M rfl
  rw [← he.finrank_eq]
  exact htop M

variable [Finite X] [Finite I] [MulAction.IsPretransitive U X]
  {C V : Type} [Group C] [Finite C]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (hI : Nat.card I = 8) (x : X)
  (f : MulAction.stabilizer U x →* C) (hf : Function.Surjective f)
  (rho : Representation (ZMod 2) C V)
  (hC : Nat.card C = 3 ∨ Nat.card C = 6)
  (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)

include hker hI hf hC hdim hrho in
/-- The complete 2+8 bound for the original normal and original frame.
The sole finite-top obligation is the all-normal bound on the actual
faithful eight-point range, independently discharged by its catalogue. -/
theorem trivialKernel_original_sum_le_ten
    (htop : ∀ (M : Subgroup F.top.range) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2)
    (N : Subgroup U) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer U x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) U (ZMod 2))) ≤ 10 := by
  have hn := F.trivialKernel_relativeHead_le_two hker htop N
  have hb := BinaryPairTernaryOrbitHead.original_head_le_eight
    F hI x f hf rho hC hdim hrho B
  exact Nat.add_le_add hn hb

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
