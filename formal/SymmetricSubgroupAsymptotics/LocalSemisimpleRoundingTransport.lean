import SymmetricSubgroupAsymptotics.LocalSemisimpleRoundingCompression

/-! Pull back the actual semisimple kernel and every quotient axis along an
actual group equivalence; the original physical width remains unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LocalSemisimpleRoundingCompressionData

/-- Change only the numeric width label, keeping the actual group fixed. -/
def changeWidth {G : Type} [Group G] {w w' : ℕ}
    (C : LocalSemisimpleRoundingCompressionData G w) (h : w=w') :
    LocalSemisimpleRoundingCompressionData G w' := h ▸ C

/-- The actual inverse-image kernel, rather than an abstract order match. -/
def comapEquiv {G H : Type} [Group G] [Group H] {w : ℕ}
    (C : LocalSemisimpleRoundingCompressionData H w) (e : G≃*H) :
    LocalSemisimpleRoundingCompressionData G w := by
  let E := C.E.comap e.toMonoidHom
  have he : E.map e.toMonoidHom=C.E :=
    Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective C.E
  let a : E≃*C.E := (e.subgroupMap E).trans (MulEquiv.subgroupCongr he)
  let q := QuotientGroup.congr E C.E e he
  exact {
    E := E
    chart := {
      ι := C.chart.ι
      factor := C.chart.factor
      simple := C.chart.simple
      centerless := C.chart.centerless
      equiv := a.trans C.chart.equiv }
    quotientDegree := C.quotientDegree
    quotientDegree_pos := C.quotientDegree_pos
    quotientAction := C.quotientAction.comp q.toMonoidHom
    quotientAction_injective := C.quotientAction_injective.comp q.injective
    degree_bound := C.degree_bound
    quotientDegree_gap := C.quotientDegree_gap }

end SymmetricSubgroupAsymptotics.LocalSemisimpleRoundingCompressionData
