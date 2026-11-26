import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19423

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 8]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.and, [0, 16]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [17, 18]⟩], output := 19 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19423

theorem PEqualNP.Outside.L_meta_19423 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24871982 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19423.c1, PEqualNP.Outside.L_meta_19423.f1, by decide, by decide⟩
