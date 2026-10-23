import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveRootIntrinsic
import SymmetricSubgroupAsymptotics.CFSGSylowCentreFamily
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyPermutation

/-! An actual original-model automorphism action on the natural
conjugate central points. Its stability is proved through intrinsic
Sylow centres and the actual original projective cover. No named-root
preservation or semilinear automorphism hypothesis is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGTwistedANaturalMatrices
open CFSGSylowCentreFamily

def unitaryCentralPoints (q : CFSG.PrimePower) (s : ℕ) :=
  {P : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2) //
    ∃ g : naturalFixed (s + 3) q, conjugateCentralPoint q (s + 1) g = P}

def unitaryCentralPointLabel (q : CFSG.PrimePower) (s : ℕ)
    (P : unitaryCentralPoints q s) : Subgroup (CFSG.Models.TwistedA (s + 3) q) :=
  conjugateProjectiveCentralRootLine q s
    (unitaryProjectiveCover q s (Classical.choose P.property))

theorem unitaryCentralPointLabel_representative (q : CFSG.PrimePower) (s : ℕ)
    (P : unitaryCentralPoints q s) (g : naturalFixed (s + 3) q)
    (hg : conjugateCentralPoint q (s + 1) g = P.val) :
    unitaryCentralPointLabel q s P =
      conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s g) := by
  apply (conjugateProjectiveCentralRootLine_eq_iff_point_eq q s _ g).mpr
  exact (Classical.choose_spec P.property).trans hg.symm

theorem unitaryCentralPointLabel_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (unitaryCentralPointLabel q s) := by
  intro P Q he
  have hh := (conjugateProjectiveCentralRootLine_eq_iff_point_eq q s
    (Classical.choose P.property) (Classical.choose Q.property)).mp he
  apply Subtype.ext
  exact (Classical.choose_spec P.property).symm.trans
    (hh.trans (Classical.choose_spec Q.property))

theorem projectiveCentralRootLine_eq_sylow_center (q : CFSG.PrimePower) (s : ℕ) :
    projectiveCentralRootLine q s = ambientCenter
      (unitaryProjectiveSylow q s : Subgroup (CFSG.Models.TwistedA (s + 3) q)) := by
  rw [unitaryProjectiveSylow_coe]
  exact projectiveCentralRootLine_eq_intrinsic_center q s

theorem unitaryCentralPointLabel_stable (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (P : unitaryCentralPoints q s) :
    ∃ Q : unitaryCentralPoints q s,
      unitaryCentralPointLabel q s Q = (unitaryCentralPointLabel q s P).map f.toMonoidHom := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  letI : Finite (CFSG.Models.TwistedA (s + 3) q) :=
    Finite.of_surjective (unitaryProjectiveCover q s) (unitaryProjectiveCover_surjective q s)
  let g : naturalFixed (s + 3) q := Classical.choose P.property
  obtain ⟨h, hh⟩ := conjugate_centres_stable (unitaryProjectiveSylow q s) f
    (unitaryProjectiveCover q s g)
  obtain ⟨h, rfl⟩ := unitaryProjectiveCover_surjective q s h
  let Q : unitaryCentralPoints q s := ⟨conjugateCentralPoint q (s + 1) h, ⟨h, rfl⟩⟩
  refine ⟨Q, ?_⟩
  rw [unitaryCentralPointLabel_representative q s Q h rfl,
    unitaryCentralPointLabel_representative q s P g (Classical.choose_spec P.property)]
  change (projectiveCentralRootLine q s).map
      (MulAut.conj (unitaryProjectiveCover q s h)).toMonoidHom =
    ((projectiveCentralRootLine q s).map
      (MulAut.conj (unitaryProjectiveCover q s g)).toMonoidHom).map f.toMonoidHom
  simpa only [← projectiveCentralRootLine_eq_sylow_center q s] using hh

def unitaryCentralPointActionHom (q : CFSG.PrimePower) (s : ℕ) :
    MulAut (CFSG.Models.TwistedA (s + 3) q) →* Equiv.Perm (unitaryCentralPoints q s) :=
  CFSGSubgroupFamilyPermutation.permutationHom (unitaryCentralPointLabel q s)
    (unitaryCentralPointLabel_injective q s) (unitaryCentralPointLabel_stable q s)

theorem unitaryCentralPointAction_label (q : CFSG.PrimePower) (s : ℕ)
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q)) (P : unitaryCentralPoints q s) :
    unitaryCentralPointLabel q s (unitaryCentralPointActionHom q s f P) =
      (unitaryCentralPointLabel q s P).map f.toMonoidHom :=
  CFSGSubgroupFamilyPermutation.label_permutation (unitaryCentralPointLabel q s)
    (unitaryCentralPointLabel_injective q s) (unitaryCentralPointLabel_stable q s) f P

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
