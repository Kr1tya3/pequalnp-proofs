import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19583

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.and, [10, 15]⟩, ⟨GateOp.or, [16, 17]⟩], output := 18 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19583

theorem PEqualNP.Outside.L_meta_19583 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7882302 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19583.c1, PEqualNP.Outside.L_meta_19583.f1, by decide, by decide⟩
