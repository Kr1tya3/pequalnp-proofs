import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19250

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.not, [1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [5, 14]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [15, 18]⟩], output := 19 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19250

theorem PEqualNP.Outside.L_meta_19250 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577150 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19250.c1, PEqualNP.Outside.L_meta_19250.f1, by decide, by decide⟩
