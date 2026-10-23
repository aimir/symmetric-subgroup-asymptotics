import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Group

/-! The actual quotient conjugation action of an ORIGINAL normal
abelian subgroup. Its associated semidirect product has the same
underlying order as the original extension; the original need not split. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AbelianExtensionConjugation
variable {G : Type*} [Group G] (N:Subgroup G) [N.Normal] [IsMulCommutative N]

theorem kernel_le_conjugation_ker : N≤(MulAut.conjNormal:G→*MulAut N).ker := by
  intro g hg
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro n
  apply Subtype.ext
  change g*(n:G)*g⁻¹=(n:G)
  have hc : g*(n:G)=(n:G)*g :=
    congrArg (fun z:N=>z.val) (mul_comm' (⟨g,hg⟩:N) n)
  rw [hc,mul_assoc,mul_inv_cancel,mul_one]

def quotientConjugation : G⧸N→*MulAut N :=
  QuotientGroup.lift N MulAut.conjNormal (kernel_le_conjugation_ker N)

theorem quotientConjugation_mk (g:G) :
    quotientConjugation N (QuotientGroup.mk' N g)=MulAut.conjNormal g := rfl

abbrev AssociatedSplit := N⋊[quotientConjugation N](G⧸N)

instance associatedSplit_finite [Finite G] : Finite (AssociatedSplit N) :=
  Finite.of_equiv (N×(G⧸N)) SemidirectProduct.equivProd.symm

theorem associatedSplit_card : Nat.card (AssociatedSplit N)=Nat.card G := by
  rw [SemidirectProduct.card]
  change Nat.card N*N.index=Nat.card G
  exact N.card_mul_index

omit [IsMulCommutative N] in
theorem left_translate_mul (x y:G) (n m:N) :
    ((n:G)*x)*((m:G)*y)=((n*MulAut.conjNormal x m:N):G)*(x*y) := by
  simp only [Subgroup.coe_mul,MulAut.conjNormal_apply]
  group

omit [IsMulCommutative N] in
theorem commute_translates_iff (x y:G) (hxy:Commute x y) (n m:N) :
    Commute ((n:G)*x) ((m:G)*y)↔n*MulAut.conjNormal x m=m*MulAut.conjNormal y n := by
  constructor
  · intro hc
    have he := hc.eq
    rw [left_translate_mul N x y n m,left_translate_mul N y x m n,←hxy.eq] at he
    exact Subtype.ext (mul_right_cancel he)
  · intro he
    change ((n:G)*x)*((m:G)*y)=((m:G)*y)*((n:G)*x)
    rw [left_translate_mul N x y n m,left_translate_mul N y x m n,←hxy.eq,
      congrArg (fun z:N=>z.val) he]

end SymmetricSubgroupAsymptotics.AbelianExtensionConjugation
