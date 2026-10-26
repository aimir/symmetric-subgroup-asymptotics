import SymmetricSubgroupAsymptotics.CFSGMathieuElevenFourTransversalSeedImages

/-! The eight-code upper-capacity whitelist from selected receipt
9bc0898f963e0d450331c2de3219ef8d910aa70671d8a41d2df9bfe8423474c0. No positive relator checks are needed for an upper bound.
Global completeness is proved separately by the eleven natural prefixes.
Data are not proof until the primary kernel checks pass. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenAcceptedCodes
open CFSGMathieuElevenFourTransversalCover

def acceptedCodes : Finset Code :=
  {(((2 : Fin 11),⟨(1 : Fin 11),by decide⟩),(⟨(9 : Fin 11),by decide⟩,⟨(5 : Fin 11),by decide⟩)),
    (((2 : Fin 11),⟨(3 : Fin 11),by decide⟩),(⟨(8 : Fin 11),by decide⟩,⟨(9 : Fin 11),by decide⟩)),
    (((6 : Fin 11),⟨(3 : Fin 11),by decide⟩),(⟨(7 : Fin 11),by decide⟩,⟨(6 : Fin 11),by decide⟩)),
    (((6 : Fin 11),⟨(8 : Fin 11),by decide⟩),(⟨(6 : Fin 11),by decide⟩,⟨(4 : Fin 11),by decide⟩)),
    (((7 : Fin 11),⟨(8 : Fin 11),by decide⟩),(⟨(5 : Fin 11),by decide⟩,⟨(9 : Fin 11),by decide⟩)),
    (((7 : Fin 11),⟨(9 : Fin 11),by decide⟩),(⟨(3 : Fin 11),by decide⟩,⟨(8 : Fin 11),by decide⟩)),
    (((10 : Fin 11),⟨(5 : Fin 11),by decide⟩),(⟨(8 : Fin 11),by decide⟩,⟨(9 : Fin 11),by decide⟩)),
    (((10 : Fin 11),⟨(10 : Fin 11),by decide⟩),(⟨(2 : Fin 11),by decide⟩,⟨(4 : Fin 11),by decide⟩))}

theorem acceptedCodes_card_le_eight : acceptedCodes.card≤8 := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenAcceptedCodes
