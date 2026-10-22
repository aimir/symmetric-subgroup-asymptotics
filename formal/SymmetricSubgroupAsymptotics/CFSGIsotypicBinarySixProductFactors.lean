import SymmetricSubgroupAsymptotics.CFSGIsotypicSimpleCentralizerSix
import SymmetricSubgroupAsymptotics.CFSGCentralizerSupplementIsotypic
import SymmetricSubgroupAsymptotics.CFSGProductSolubleCentralizer
import SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormal

/-! A faithful irreducible binary representation of a power of a
noncommutative simple group has at most one factor when its dimension
divides six. Each coordinate factor has homogeneous restriction because
it is supplemented by its actual centralizer. A second factor would
then embed in a proved soluble original linear centralizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGIsotypicBinarySixProductFactors
open CFSGProductFactorCentralizer CFSGPrimeBinaryAbelianNormal

theorem factor_index_subsingleton
    {I S V : Type} [Finite I] [Group S] [Finite S] [IsSimpleGroup S]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) (I → S) V)
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hdvd : Module.finrank (ZMod 2) V ∣ 6) (hnc : ¬ IsMulCommutative S) :
    Subsingleton I := by
  rcases subsingleton_or_nontrivial I with hi | hi
  · exact hi
  letI : Nontrivial I := hi
  letI : Representation.IsIrreducible rho := hrho
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  let i : I := Classical.arbitrary I
  let H := factor (S := S) i
  let C := Subgroup.centralizer (H : Set (I → S))
  letI : H.Normal := factor_normal i
  letI : IsSimpleGroup H := (factorEquiv (S := S) i).symm.isSimpleGroup
  have hHnc : ¬ IsMulCommutative H := by
    intro hH
    letI : IsMulCommutative H := hH
    apply hnc
    exact ⟨⟨fun a b => (factorEquiv (S := S) i).injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩
  let sigma : Representation (ZMod 2) H V := rho.comp H.subtype
  have hsf : Function.Injective sigma := by
    intro a b hab
    exact Subtype.ext (hf hab)
  have hss := CliffordRawRestriction.proved.semisimple rho hrho H
  have hiso :=
    CFSGCentralizerSupplementIsotypic.restriction_isotypic_of_centralizer_supplement
      rho hrho H (factor_sup_centralizer_eq_top i)
  letI : IsSolvable (CFSGIrreducibleLinearCentralizer.linearCentralizer sigma) :=
    CFSGIsotypicSimpleCentralizerSix.isotypic_simple_centralizer_soluble
      sigma hsf hHnc hdvd hss hiso
  have hc (c : C) (h : H) : (c : I → S) * h = h * c :=
    ((Subgroup.mem_centralizer_iff.mp c.property) h h.property).symm
  letI : IsSolvable C := solvable_of_solvable_injective
    (f := commutingSubgroupHom rho H C hc)
    (commutingSubgroupHom_injective rho hf H C hc)
  have hns : ¬ IsSolvable S := by
    intro hs
    exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  exact CFSGProductSolubleCentralizer.subsingleton_of_soluble_centralizer i hns

end SymmetricSubgroupAsymptotics.CFSGIsotypicBinarySixProductFactors
