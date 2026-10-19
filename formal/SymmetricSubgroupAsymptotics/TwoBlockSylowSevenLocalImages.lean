import SymmetricSubgroupAsymptotics.PermutationalWreathFunctionCoinduced
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Finite

/-! In an actual full-component two-block wreath embedding, a Sylow seven
fixes both blocks and has full Sylow image in each local component. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoBlockSylowSevenLocalImages
open PermutationalWreathProduct
local instance twoBlockSylowSevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {G D Q I : Type} [Group G] [Finite G] [Group D] [Finite D]
  [Group Q] [MulAction Q I] [Finite I]
  (rho : G →* PermutationalWreathProduct D Q I)
  (hfull : Compression.FullComponent rho) (hI : Nat.card I = 2)
  (P : Sylow 7 G)

private def pointMap : G →* Equiv.Perm I :=
  (MulAction.toPermHom Q I).comp (rightHom.comp rho)

include hI

/-- An odd Sylow cannot permute two actual blocks. -/
theorem fixes_blocks (p : P) (i : I) : (rho p.val).right • i = i := by
  let f : P →* Equiv.Perm I := (pointMap rho).comp (P : Subgroup G).subtype
  have hp : IsPGroup 7 f.range :=
    P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hd : Nat.card f.range ∣ 2 := by
    have hh := f.range.card_subgroup_dvd_card
    simpa only [Nat.card_perm, hI, show Nat.factorial 2 = 2 from rfl] using hh
  have hc : Nat.card f.range = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
    · exact hh
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
      have ht : 2 ∣ 7 ^ n := by rw [← hn, hh]
      have : 2 ∣ 7 := Nat.prime_two.dvd_of_dvd_pow ht
      norm_num at this
  letI : Subsingleton f.range := Finite.card_le_one_iff_subsingleton.mp (by omega)
  have he : f p = 1 := congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict p) 1)
  exact congrArg (fun s : Equiv.Perm I => s i) he

private theorem le_stabilizer (i : I) :
    (P : Subgroup G) ≤ FunctionCoinduced.stabilizer rho i := by
  intro p hp
  exact fixes_blocks rho hI P ⟨p, hp⟩ i

/-- Each local map is defined on the SAME actual Sylow subgroup. -/
def localMap (i : I) : P →* D :=
  (FunctionCoinduced.stabilizerComponent rho i).comp
    { toFun := fun p => ⟨p.val, le_stabilizer rho hI P i p.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp] theorem local_apply (i : I) (p : P) :
    localMap rho hI P i p = (rho p.val).left i := rfl

include hfull in
/-- Fullness, not an assumption on the final image size, supplies the
local Sylow image. The single factor seven in the local order determines it. -/
theorem local_range_card (hD : (Nat.card D).factorization 7 = 1) (i : I) :
    Nat.card (localMap rho hI P i).range = 7 := by
  let H := FunctionCoinduced.stabilizer rho i
  let psi : H →* D := FunctionCoinduced.stabilizerComponent rho i
  have hs : Function.Surjective psi := by
    intro d
    obtain ⟨g, hg, hd⟩ := hfull i d
    exact ⟨⟨g, hg⟩, hd⟩
  let S : Sylow 7 H := P.subtype (le_stabilizer rho hI P i)
  let R : Sylow 7 D := S.mapSurjective hs
  have hrange : (localMap rho hI P i).range = (R : Subgroup D) := by
    ext d
    rw [Sylow.coe_mapSurjective, Subgroup.mem_map]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨p.val, le_stabilizer rho hI P i p.property⟩, p.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.val, hg⟩, rfl⟩
  rw [hrange, Sylow.card_eq_multiplicity, hD, pow_one]

end SymmetricSubgroupAsymptotics.TwoBlockSylowSevenLocalImages
