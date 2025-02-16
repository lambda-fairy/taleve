import Mathlib

namespace Vector

variable {α : Type*} {n : ℕ}

theorem ofFn_get (v : Vector α n) : ofFn v.get = v := by
  ext
  apply getElem_ofFn

theorem get_ofFn (f : Fin n → α) : (ofFn f).get = f := by
  ext
  apply getElem_ofFn

-- Needs a `'` because the version in mathlib is for `List.Vector`...
def _root_.Equiv.vectorEquivFin' : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, Vector.get_ofFn⟩

instance fintype' [Fintype α] : Fintype (Vector α n) :=
  Fintype.ofEquiv (Fin n → α) Equiv.vectorEquivFin'.symm

end Vector
