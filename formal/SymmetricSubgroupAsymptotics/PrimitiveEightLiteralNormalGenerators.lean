import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20AffineSocleClosure
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow22QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops
import SymmetricSubgroupAsymptotics.SimpleChiefFamilies

/-! All ambient normal subgroups of the seven primitive eight-point literal
actions are normally cyclic. The affine rows use their actual normal chains;
the two retained finite rows use existing normal-join words; the final two
rows use the alternating and symmetric normal-subgroup theorems. No new
enumeration or conjugacy-cardinality computation is used here.

This file does not assert that an arbitrary primitive eight-point action is
one of these seven. The exact catalogue filtering is a separate obligation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveEightLiteralNormalGenerators

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem total_of_three_values {G : Type} [Group G] (M : Subgroup G)
    (h : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = M ∨ N = ⊤)
    (N K : Subgroup G) (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N := by
  rcases h N hN with rfl | rfl | rfl <;>
    rcases h K hK with rfl | rfl | rfl <;> simp

theorem row18_normal_total
    (N K : Subgroup DegreeTwoPairedEightSharedTops.Top18)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N :=
  total_of_three_values _
    PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.normalChain.normal_eq_bot_or_middle_or_top
    N K hN hK

namespace Row19

abbrev Source := PrimitiveAffineEightFrameRow27TopCertificate.Source
local instance : Group Source := PrimitiveAffineEightFrameRow27TopCertificate.group

private def state (i : Fin 4) : Subgroup Source :=
  Subgroup.closure (Set.range
    (PrimitiveAffineEightFrameRow27NormalCertificate.stateGenerators i))

private theorem state_total (i j : Fin 4) : state i ≤ state j ∨ state j ≤ state i := by
  have h01 : state 0 ≤ state 1 :=
    (PrimitiveAffineEightFrameRow27NormalCertificate.transition 0 3).parentToChild.closure_le
  have h12 : state 1 ≤ state 2 :=
    (PrimitiveAffineEightFrameRow27NormalCertificate.transition 1 1).parentToChild.closure_le
  have h23 : state 2 ≤ state 3 :=
    (PrimitiveAffineEightFrameRow27NormalCertificate.transition 2 2).parentToChild.closure_le
  have hm : Monotone state := Fin.monotone_iff_le_succ.mpr (by
    intro k
    fin_cases k
    · exact h01
    · exact h12
    · exact h23)
  exact (le_total i j).elim (fun h => Or.inl (hm h)) (fun h => Or.inr (hm h))

theorem source_normal_total (N K : Subgroup Source) (hN : N.Normal) (hK : K.Normal) :
    N ≤ K ∨ K ≤ N := by
  letI := hN
  letI := hK
  obtain ⟨i, rfl⟩ := PrimitiveAffineEightFrameRow27NormalCertificate.complete N
  obtain ⟨j, rfl⟩ := PrimitiveAffineEightFrameRow27NormalCertificate.complete K
  exact state_total i j

end Row19

theorem row19_normal_total
    (N K : Subgroup DegreeTwoPairedEightSharedTops.top19.top)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N := by
  letI : Group Row19.Source := PrimitiveAffineEightFrameRow27TopCertificate.group
  exact normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.surjective
    Row19.source_normal_total N K hN hK

theorem row20_normal_total
    (N K : Subgroup DegreeTwoPairedEightSharedTops.Top20)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N :=
  total_of_three_values _
    PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.normalChain.normal_eq_bot_or_middle_or_top
    N K hN hK

namespace Row21

abbrev Source := PrimitiveAffineEightFrameRow28TopCertificate.Source
local instance : Group Source := PrimitiveAffineEightFrameRow28TopCertificate.group

private def state (i : Fin 2) : Subgroup Source :=
  Subgroup.closure (Set.range
    (PrimitiveAffineEightFrameRow28NormalCertificate.stateGenerators i))

private theorem state_total (i j : Fin 2) : state i ≤ state j ∨ state j ≤ state i := by
  have h01 : state 0 ≤ state 1 :=
    (PrimitiveAffineEightFrameRow28NormalCertificate.transition 0 1).parentToChild.closure_le
  have hm : Monotone state := Fin.monotone_iff_le_succ.mpr (by
    intro k
    fin_cases k
    exact h01)
  exact (le_total i j).elim (fun h => Or.inl (hm h)) (fun h => Or.inr (hm h))

theorem source_normal_total (N K : Subgroup Source) (hN : N.Normal) (hK : K.Normal) :
    N ≤ K ∨ K ≤ N := by
  letI := hN
  letI := hK
  obtain ⟨i, rfl⟩ := PrimitiveAffineEightFrameRow28NormalCertificate.complete N
  obtain ⟨j, rfl⟩ := PrimitiveAffineEightFrameRow28NormalCertificate.complete K
  exact state_total i j

end Row21

theorem row21_normal_total
    (N K : Subgroup DegreeTwoPairedEightSharedTops.top21.top)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N := by
  letI : Group Row21.Source := PrimitiveAffineEightFrameRow28TopCertificate.group
  exact normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow28TopCertificate.originalEquiv.surjective
    Row21.source_normal_total N K hN hK

theorem row22_normal_total
    (N K : Subgroup DegreeTwoPairedEightSharedTops.top22.top)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N :=
  PrimitiveAffineDegreeTwoPairedEightRow22QuotientSocles.top_normal_total N K hN hK

theorem row23_normal_total
    (N K : Subgroup DegreeTwoPairedEightSharedTops.Top23)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N := by
  letI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (α := Fin 8) (by norm_num)
  let e : DegreeTwoPairedEightSharedTops.Top23 ≃* alternatingGroup (Fin 8) :=
    MulEquiv.subgroupCongr DegreeTwoPairedEightSharedTops.top23_eq_alternating
  letI : IsSimpleGroup DegreeTwoPairedEightSharedTops.Top23 := e.isSimpleGroup
  rcases hN.eq_bot_or_eq_top with rfl | rfl <;> simp

private theorem symmetric_normal_total
    (N K : Subgroup (Equiv.Perm (Fin 8))) (hN : N.Normal) (hK : K.Normal) :
    N ≤ K ∨ K ≤ N := by
  letI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (α := Fin 8) (by norm_num)
  apply total_of_three_values (alternatingGroup (Fin 8)) _ N K hN hK
  intro A hA
  by_cases hb : A = ⊥
  · exact Or.inl hb
  · right
    letI := hA
    letI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hb
    exact indexTwo_maximal (alternatingGroup (Fin 8))
      alternatingGroup.index_eq_two A
      (Equiv.Perm.alternatingGroup_le_of_normal (by norm_num) inferInstance)

theorem row24_normal_total
    (N K : Subgroup DegreeTwoPairedEightSharedTops.Top24)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N := by
  let e : DegreeTwoPairedEightSharedTops.Top24 ≃* Equiv.Perm (Fin 8) :=
    (MulEquiv.subgroupCongr DegreeTwoPairedEightSharedTops.top24_eq_top).trans
      Subgroup.topEquiv
  exact normalSubgroups_total_of_surjective e.symm.toMonoidHom e.symm.surjective
    symmetric_normal_total N K hN hK

/-- Exact normal-chain dispatch for literal rows18 through24. -/
theorem normal_total (j : Fin 24) (hj : 17 ≤ j.val)
    (N K : Subgroup (DegreeTwoPairedEightSharedTops.interface j).top)
    (hN : N.Normal) (hK : K.Normal) : N ≤ K ∨ K ≤ N := by
  have hcases : j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row18_normal_total N K hN hK
  · exact row19_normal_total N K hN hK
  · exact row20_normal_total N K hN hK
  · exact row21_normal_total N K hN hK
  · exact row22_normal_total N K hN hK
  · exact row23_normal_total N K hN hK
  · exact row24_normal_total N K hN hK

/-- Uniform ambient normal generation on each of the seven original
literal primitive-eight groups, including every original normal subgroup. -/
theorem normal_generating_singletons (j : Fin 24) (hj : 17 ≤ j.val) :
    ∀ N : Subgroup (DegreeTwoPairedEightSharedTops.interface j).top, N.Normal →
      ∃ x : Fin 1 → (DegreeTwoPairedEightSharedTops.interface j).top,
        Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_singletons_of_finite_normal_total (normal_total j hj)

end PrimitiveEightLiteralNormalGenerators
end SymmetricSubgroupAsymptotics

end
