import SymmetricSubgroupAsymptotics.SimpleTwoCoordinateOrdinaryGenerators
import SymmetricSubgroupAsymptotics.TwoBlockWreathNormalGenerators
import SymmetricSubgroupAsymptotics.ActualWreathCompressionTower

/-! A faithful two-block wreath source with full simple local component
costs the ACTUAL local ordinary rank plus its actual top rank. Existing
literal top-kernel coordinate surjectivity retains diagonal correlations;
the actual top transporter supplies the coordinate swap. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoBlockSimpleLocalOrdinaryGenerators
open PermutationalWreathProduct TwoBlockWreathNormalGenerators

private theorem conjugate_coordinate {L Q I : Type} [Group L] [Group Q] [MulAction Q I]
    (a x : PermutationalWreathProduct L Q I) (hx : x.right = 1) (i : I) :
    (a*x*a⁻¹).left (a.right • i) = a.left (a.right • i)*x.left i*(a.left (a.right • i))⁻¹ := by
  simp only [mul_left,mul_right,inv_left,Pi.mul_apply,Pi.inv_apply,
    hx,mul_one,inv_smul_smul,smul_inv_smul]

theorem genRank_le_local_add_top
    {G L Q I : Type} [Group G] [Finite G] [Group L] [Finite L] [IsSimpleGroup L]
    [Group Q] [Finite Q] [Fintype I] [MulAction Q I] [FaithfulSMul Q I]
    [MulAction.IsPretransitive Q I]
    (rho : G →* PermutationalWreathProduct L Q I) (hI : Nat.card I = 2)
    (hrho : Function.Injective rho) (htop : Function.Surjective (top rho))
    (hfull : Compression.FullComponent rho) :
    MarkedC4.genRank G ≤ MarkedC4.genRank L + MarkedC4.genRank Q := by
  let e : I ≃ Fin 2 := Finite.equivFinOfCardEq hI
  let i₀ : I := e.symm 0
  let i₁ : I := e.symm 1
  let N := (top rho).ker
  let f : N →* L := coordinate rho i₀
  let g : N →* L := coordinate rho i₁
  have hjoint : Function.Injective (fun x : N => (f x,g x)) := by
    intro x y he
    apply coordinates_joint_injective rho hrho
    funext i
    have hi : i = e.symm (e i) := (e.symm_apply_apply i).symm
    rw [hi]
    have h0 := congrArg Prod.fst he
    have h1 := congrArg Prod.snd he
    generalize e i = j
    fin_cases j
    · exact h0
    · exact h1
  obtain ⟨q,hq⟩ := MulAction.exists_smul_eq Q i₁ i₀
  obtain ⟨h,hh⟩ := htop q
  have hswap : (rho h).right • i₁ = i₀ := by
    change (rho h).right = q at hh
    rw [hh]
    exact hq
  have hconj (x : N) : f ((MulAut.conjNormal h) x) =
      (MulAut.conj ((rho h).left i₀)) (g x) := by
    have hx : (rho (x : G)).right = 1 := x.property
    have hc := conjugate_coordinate (rho h) (rho (x : G)) hx i₁
    rw [hswap] at hc
    change (rho (h*(x : G)*h⁻¹)).left i₀ = _
    rw [map_mul,map_mul,map_inv]
    exact hc
  have hh := SimpleTwoCoordinateOrdinaryGenerators.genRank_le_local_add_quotient
    N f g (coordinate_surjective rho hI hfull i₀) (coordinate_surjective rho hI hfull i₁)
    hjoint h (MulAut.conj ((rho h).left i₀)) hconj
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective (top rho) htop)] at hh
  exact hh

theorem state_genRank_le_local_add_top
    {Q I : Type} [Group Q] [Finite Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I) [IsSimpleGroup S.D] (hI : Nat.card I = 2) :
    MarkedC4.genRank S.A ≤ MarkedC4.genRank S.D + MarkedC4.genRank Q := by
  letI : MulAction.IsPretransitive Q I := S.top_pretransitive
  exact genRank_le_local_add_top S.rho hI S.rho_injective S.top_surjective S.fullComponent

end SymmetricSubgroupAsymptotics.TwoBlockSimpleLocalOrdinaryGenerators
