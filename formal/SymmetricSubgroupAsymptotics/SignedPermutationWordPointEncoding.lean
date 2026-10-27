import SymmetricSubgroupAsymptotics.SignedPermutationWordPointEvaluation

/-! An erased-state evaluator is sound whenever its four raw letter maps
encode the corresponding typed maps. Induction retains a typed shadow at
every intermediate state. No range invariant or capacity is assumed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SignedPermutationWordPointEncoding
open SignedPermutationWordPointEvaluation

theorem applyWord_encoding {X Y : Type*} (encode : X → Y)
    (vf vi uf ui : X → X) (wf wi zf zi : Y → Y)
    (hvf : ∀ p, wf (encode p) = encode (vf p))
    (hvi : ∀ p, wi (encode p) = encode (vi p))
    (huf : ∀ p, zf (encode p) = encode (uf p))
    (hui : ∀ p, zi (encode p) = encode (ui p))
    (w : List Letter) (p : X) :
    applyWord wf wi zf zi w (encode p) = encode (applyWord vf vi uf ui w p) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp only [applyWord, pointLetter, ih, hvf, hvi, huf, hui]

end SymmetricSubgroupAsymptotics.SignedPermutationWordPointEncoding
