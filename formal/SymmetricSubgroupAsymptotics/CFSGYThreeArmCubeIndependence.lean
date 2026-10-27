import SymmetricSubgroupAsymptotics.CFSGYAdjacentDerivedNoncentral
import SymmetricSubgroupAsymptotics.TernaryPairedInversionIndependence
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! The three literal arm cubes have independent ternary coordinates in
the ACTUAL full derived-centre quotient. Genuine derived products of
first-arm reflections invert two coordinates and fix the third. This
does not assert any cycler, Heisenberg normalizer or action-degree bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYThreeArmCubeIndependence
open CFSG.Models.YGroups CFSGYAdjacentDerivedNoncentral

private theorem cross_commute (arms : Arms) (a b : Fin 3) (hab : a≠b)
    (d e : Fin 2) : Commute (generator arms (near arms a d))
      (generator arms (near arms b e)) := by
  let x := generator arms (near arms a d)
  let y := generator arms (near arms b e)
  have hx : x^2=1 := CFSGGeneration.y_generator_sq arms _
  have hy : y^2=1 := CFSGGeneration.y_generator_sq arms _
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy)
  have hne : near arms a d≠near arms b e := by
    intro h
    have he : a=b := congrArg (fun q : Node arms =>
      match q with | none => (0 : Fin 3) | some v => v.1) h
    exact hab he
  have hnot : ¬Adjacent arms (near arms a d) (near arms b e) := by
    intro h
    exact hab h.1
  have hp : (x*y)⁻¹=x*y := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using
      CFSGReduction.y_nonadjacent_product_sq arms _ _ ⟨hne,hnot⟩)
  have he : y*x=x*y := by simpa only [mul_inv_rev,hi,hj] using hp
  exact he.symm

theorem armCube_commute (arms : Arms) (a b : Fin 3) (hab : a≠b) :
    Commute (armCube arms a) (armCube arms b) := by
  apply Subtype.ext
  change (generator arms (near arms a 0)*generator arms (near arms a 1))*
      (generator arms (near arms b 0)*generator arms (near arms b 1)) = _
  exact ((cross_commute arms a b hab 0 0).mul_right
      (cross_commute arms a b hab 0 1)).mul_left
    ((cross_commute arms a b hab 1 0).mul_right (cross_commute arms a b hab 1 1))

theorem sectionArmCube_commute (arms : Arms) (a b : Fin 3) (hab : a≠b) :
    Commute (sectionArmCube arms a) (sectionArmCube arms b) := by
  have h := congrArg
    (QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms))))
    (armCube_commute arms a b hab).eq
  simpa only [map_mul] using h

def sectionArmInverter (arms : Arms) (a b : Fin 3) : SimpleSection arms :=
  QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms)))
    (armInverter arms a b)

theorem sectionArmInverter_first (arms : Arms) (a b : Fin 3) (hab : a≠b) :
    sectionArmInverter arms a b * sectionArmCube arms a *
      (sectionArmInverter arms a b)⁻¹ = (sectionArmCube arms a)⁻¹ := by
  have h := congrArg
    (QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms))))
    (armCube_conjugated_inverse arms a b hab)
  simpa only [map_mul,map_inv] using h

private theorem armInverter_swap (arms : Arms) (a b : Fin 3) (hab : a≠b) :
    armInverter arms a b=armInverter arms b a := by
  apply Subtype.ext
  exact (cross_commute arms a b hab 0 0).eq

theorem sectionArmInverter_second (arms : Arms) (a b : Fin 3) (hab : a≠b) :
    sectionArmInverter arms a b * sectionArmCube arms b *
      (sectionArmInverter arms a b)⁻¹ = (sectionArmCube arms b)⁻¹ := by
  have hs : sectionArmInverter arms a b=sectionArmInverter arms b a :=
    congrArg (QuotientGroup.mk'
      (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms))))
      (armInverter_swap arms a b hab)
  rw [hs]
  exact sectionArmInverter_first arms b a (Ne.symm hab)

theorem sectionArmInverter_other (arms : Arms) (a b k : Fin 3)
    (hak : a≠k) (hbk : b≠k) :
    sectionArmInverter arms a b * sectionArmCube arms k *
      (sectionArmInverter arms a b)⁻¹ = sectionArmCube arms k := by
  have hc : Commute (armInverter arms a b) (armCube arms k) := by
    apply Subtype.ext
    change (generator arms (near arms a 0)*generator arms (near arms b 0))*
        (generator arms (near arms k 0)*generator arms (near arms k 1)) = _
    exact ((cross_commute arms a k hak 0 0).mul_right
        (cross_commute arms a k hak 0 1)).mul_left
      ((cross_commute arms b k hbk 0 0).mul_right (cross_commute arms b k hbk 0 1))
  have hd : armInverter arms a b*armCube arms k*(armInverter arms a b)⁻¹=
      armCube arms k := by rw [hc.eq]; group
  have h := congrArg
    (QuotientGroup.mk' (Subgroup.center (commutator (CFSG.Models.YGroups.Group arms)))) hd
  simpa only [map_mul,map_inv] using h

theorem exponents_divisible (arms : Arms)
    (hn : ¬IsMulCommutative (SimpleSection arms)) (i j k : ℕ)
    (hrel : sectionArmCube arms 0 ^ i * sectionArmCube arms 1 ^ j *
      sectionArmCube arms 2 ^ k=1) : 3∣i ∧ 3∣j ∧ 3∣k := by
  let f : SimpleSection arms →* SimpleSection arms :=
    (MulAut.conj (sectionArmInverter arms 0 1)).toMonoidHom
  let g : SimpleSection arms →* SimpleSection arms :=
    (MulAut.conj (sectionArmInverter arms 0 2)).toMonoidHom
  apply TernaryPairedInversionIndependence.exponents_divisible f g
    (sectionArmCube arms 0) (sectionArmCube arms 1) (sectionArmCube arms 2)
    (sectionArmCube_commute arms 0 1 (by decide))
    (sectionArmCube_commute arms 0 2 (by decide))
    (sectionArmCube_commute arms 1 2 (by decide))
    (sectionArmCube_order_three arms 0 hn) (sectionArmCube_order_three arms 1 hn)
    (sectionArmCube_order_three arms 2 hn)
  · exact sectionArmInverter_first arms 0 1 (by decide)
  · exact sectionArmInverter_second arms 0 1 (by decide)
  · exact sectionArmInverter_other arms 0 1 2 (by decide) (by decide)
  · exact sectionArmInverter_first arms 0 2 (by decide)
  · exact sectionArmInverter_other arms 0 2 1 (by decide) (by decide)
  · exact sectionArmInverter_second arms 0 2 (by decide)
  · exact hrel

theorem bounded_exponents_zero (arms : Arms)
    (hn : ¬IsMulCommutative (SimpleSection arms)) (i j k : ℕ)
    (hi : i<3) (hj : j<3) (hk : k<3)
    (hrel : sectionArmCube arms 0 ^ i * sectionArmCube arms 1 ^ j *
      sectionArmCube arms 2 ^ k=1) : i=0 ∧ j=0 ∧ k=0 := by
  obtain ⟨hdi,hdj,hdk⟩ := exponents_divisible arms hn i j k hrel
  rcases hdi with ⟨m,hm⟩
  rcases hdj with ⟨n,hn'⟩
  rcases hdk with ⟨r,hr⟩
  omega

end SymmetricSubgroupAsymptotics.CFSGYThreeArmCubeIndependence
