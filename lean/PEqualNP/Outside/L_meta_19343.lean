import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19343

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.or, [14, 16]⟩], output := 17 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19343

theorem PEqualNP.Outside.L_meta_19343 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236078 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19343.c1, PEqualNP.Outside.L_meta_19343.f1, by decide, by decide⟩
