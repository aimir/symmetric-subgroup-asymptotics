import SymmetricSubgroupAsymptotics.TernaryHeisenbergThreeGeneratorHom
import SymmetricSubgroupAsymptotics.TernaryPairedInversionIndependence

/-! A literal three-cycle on three commuting ternary roots yields the
Heisenberg collecting relation. Paired inversions prove the central
diagonal nontrivial in the SAME group. In a Y application every root,
cycler and inverter must first be an actual derived-centre image, and
the displayed identities still require actual word certificates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryThreeCycleHeisenberg
variable {G : Type*} [Group G]

def difference (a b : G) : G := a*b⁻¹
def diagonal (a b c : G) : G := a⁻¹*b⁻¹*c⁻¹

theorem difference_cube (a b : G) (ha : a^3=1) (hb : b^3=1)
    (hab : Commute a b) : difference a b ^ 3=1 := by
  change (a*b⁻¹)^3=1
  rw [hab.inv_right.mul_pow,inv_pow,ha,hb,inv_one,mul_one]

theorem diagonal_cube (a b c : G) (ha : a^3=1) (hb : b^3=1) (hc : c^3=1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) :
    diagonal a b c ^ 3=1 := by
  change (a⁻¹*b⁻¹*c⁻¹)^3=1
  rw [(hac.inv_inv.mul_left hbc.inv_inv).mul_pow,hab.inv_inv.mul_pow]
  simp only [inv_pow,ha,hb,hc,inv_one,mul_one]

theorem difference_commute_diagonal (a b c : G)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) :
    Commute (difference a b) (diagonal a b c) := by
  have ha : Commute a (a⁻¹*b⁻¹*c⁻¹) :=
    (((Commute.refl a).inv_right).mul_right hab.inv_right).mul_right hac.inv_right
  have hb : Commute b⁻¹ (a⁻¹*b⁻¹*c⁻¹) :=
    ((hab.symm.inv_inv.mul_right (Commute.refl b⁻¹)).mul_right hbc.inv_inv)
  exact ha.mul_left hb

theorem rotation_fixes_diagonal (a b c r : G)
    (hab : Commute a b) (hac : Commute a c)
    (hra : r*a*r⁻¹=b) (hrb : r*b*r⁻¹=c) (hrc : r*c*r⁻¹=a) :
    Commute r (diagonal a b c) := by
  have hfix : r*diagonal a b c*r⁻¹=diagonal a b c := by
    calc
      r*diagonal a b c*r⁻¹ = (r*a*r⁻¹)⁻¹*(r*b*r⁻¹)⁻¹*(r*c*r⁻¹)⁻¹ := by
        dsimp only [diagonal]
        group
      _ = b⁻¹*c⁻¹*a⁻¹ := by rw [hra,hrb,hrc]
      _ = a⁻¹*(b⁻¹*c⁻¹) :=
        (hab.inv_inv.mul_right hac.inv_inv).eq.symm
      _ = diagonal a b c := (mul_assoc _ _ _).symm
  change r*diagonal a b c=diagonal a b c*r
  calc
    r*diagonal a b c = (r*diagonal a b c*r⁻¹)*r := by group
    _ = diagonal a b c*r := by rw [hfix]

theorem rotation_difference (a b c r : G) (hb : b^3=1) (hab : Commute a b)
    (hra : r*a*r⁻¹=b) (hrb : r*b*r⁻¹=c) :
    r*difference a b*r⁻¹=difference a b*diagonal a b c := by
  have hb' : b⁻¹*b⁻¹=b := by
    calc
      b⁻¹*b⁻¹ = (b⁻¹*b⁻¹)*(b^3) := by rw [hb,mul_one]
      _ = b := by group
  have hright : difference a b*diagonal a b c=b*c⁻¹ := by
    calc
      difference a b*diagonal a b c = a*(b⁻¹*a⁻¹)*(b⁻¹*c⁻¹) := by
        dsimp only [difference,diagonal]
        group
      _ = a*(a⁻¹*b⁻¹)*(b⁻¹*c⁻¹) := by rw [hab.inv_inv.eq.symm]
      _ = (b⁻¹*b⁻¹)*c⁻¹ := by group
      _ = b*c⁻¹ := by rw [hb']
  calc
    r*difference a b*r⁻¹ = (r*a*r⁻¹)*(r*b*r⁻¹)⁻¹ := by
      dsimp only [difference]
      group
    _ = b*c⁻¹ := by rw [hra,hrb]
    _ = difference a b*diagonal a b c := hright.symm

theorem collecting_relation (a b c r : G) (hb : b^3=1)
    (hab : Commute a b) (hac : Commute a c)
    (hra : r*a*r⁻¹=b) (hrb : r*b*r⁻¹=c) (hrc : r*c*r⁻¹=a) :
    r*difference a b=difference a b*r*diagonal a b c := by
  have hc := rotation_fixes_diagonal a b c r hab hac hra hrb hrc
  calc
    r*difference a b = (r*difference a b*r⁻¹)*r := by group
    _ = (difference a b*diagonal a b c)*r := by
      rw [rotation_difference a b c r hb hab hra hrb]
    _ = difference a b*(diagonal a b c*r) := mul_assoc _ _ _
    _ = difference a b*(r*diagonal a b c) := congrArg (fun g => difference a b*g) hc.eq.symm
    _ = difference a b*r*diagonal a b c := (mul_assoc _ _ _).symm

/-- The first root already gives the upper transvection on the
Heisenberg quotient. It needs no separate normalizer word search. -/
theorem root_conjugates_difference (a b : G) (hab : Commute a b) :
    a*difference a b*a⁻¹=difference a b := by
  have hc : Commute a (difference a b) := (Commute.refl a).mul_right hab.inv_right
  rw [hc.eq]
  group

theorem root_conjugates_diagonal (a b c : G) (hab : Commute a b) (hac : Commute a c) :
    a*diagonal a b c*a⁻¹=diagonal a b c := by
  have hc : Commute a (diagonal a b c) :=
    (((Commute.refl a).inv_right).mul_right hab.inv_right).mul_right hac.inv_right
  rw [hc.eq]
  group

theorem root_conjugates_rotation (a b r : G) (hra : r*a*r⁻¹=b) :
    a*r*a⁻¹=difference a b*r := by
  calc
    a*r*a⁻¹ = a*(r*a*r⁻¹)⁻¹*r := by group
    _ = difference a b*r := by rw [hra]; rfl

theorem diagonal_ne_one (a b c : G) (f g : G →* G)
    (ha : a^3=1) (hb : b^3=1) (hc : c^3=1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (hfa : f a=a⁻¹) (hfb : f b=b⁻¹) (hfc : f c=c)
    (hga : g a=a⁻¹) (hgb : g b=b) (hgc : g c=c⁻¹)
    (hne : a≠1) : diagonal a b c≠1 := by
  intro hrel
  have ha' : (a⁻¹)^3=1 := by rw [inv_pow,ha,inv_one]
  have hb' : (b⁻¹)^3=1 := by rw [inv_pow,hb,inv_one]
  have hc' : (c⁻¹)^3=1 := by rw [inv_pow,hc,inv_one]
  have hh := TernaryPairedInversionIndependence.factors_eq_one f g a⁻¹ b⁻¹ c⁻¹
    hab.inv_inv hac.inv_inv hbc.inv_inv ha' hb' hc'
    (by simp only [map_inv,hfa]) (by simp only [map_inv,hfb])
    (by simp only [map_inv,hfc]) (by simp only [map_inv,hga])
    (by simp only [map_inv,hgb]) (by simp only [map_inv,hgc]) hrel
  exact hne (inv_eq_one.mp hh.1)

def hom (a b c r : G) (ha : a^3=1) (hb : b^3=1) (hc : c^3=1) (hr : r^3=1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (hra : r*a*r⁻¹=b) (hrb : r*b*r⁻¹=c) (hrc : r*c*r⁻¹=a) :
    CFSGHeisenbergCoordinateGroup.Element (ZMod 3) 1 →* G :=
  TernaryHeisenbergThreeGeneratorHom.hom (difference a b) r (diagonal a b c)
    (difference_cube a b ha hb hab) hr (diagonal_cube a b c ha hb hc hab hac hbc)
    (difference_commute_diagonal a b c hab hac hbc)
    (rotation_fixes_diagonal a b c r hab hac hra hrb hrc)
    (collecting_relation a b c r hb hab hac hra hrb hrc)

theorem hom_injective (a b c r : G) (f g : G →* G)
    (ha : a^3=1) (hb : b^3=1) (hc : c^3=1) (hr : r^3=1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (hra : r*a*r⁻¹=b) (hrb : r*b*r⁻¹=c) (hrc : r*c*r⁻¹=a)
    (hfa : f a=a⁻¹) (hfb : f b=b⁻¹) (hfc : f c=c)
    (hga : g a=a⁻¹) (hgb : g b=b) (hgc : g c=c⁻¹)
    (hne : a≠1) : Function.Injective (hom a b c r ha hb hc hr hab hac hbc hra hrb hrc) :=
  TernaryHeisenbergThreeGeneratorHom.hom_injective (difference a b) r (diagonal a b c)
    (difference_cube a b ha hb hab) hr (diagonal_cube a b c ha hb hc hab hac hbc)
    (difference_commute_diagonal a b c hab hac hbc)
    (rotation_fixes_diagonal a b c r hab hac hra hrb hrc)
    (collecting_relation a b c r hb hab hac hra hrb hrc)
    (diagonal_ne_one a b c f g ha hb hc hab hac hbc hfa hfb hfc hga hgb hgc hne)

end SymmetricSubgroupAsymptotics.TernaryThreeCycleHeisenberg
