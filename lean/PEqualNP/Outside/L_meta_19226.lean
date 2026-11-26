import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19226

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [11, 12]⟩], output := 13 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19226

theorem PEqualNP.Outside.L_meta_19226 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4812 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19226.c1, PEqualNP.Outside.L_meta_19226.f1, by decide, by decide⟩
