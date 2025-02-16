import Taleve.Defs

namespace Taleve

open Lean
open Lean.Parser.Tactic (sepByIndentSemicolon)
open Lean.PrettyPrinter

declare_syntax_cat cell
scoped syntax "- " : cell
scoped syntax "# " : cell
scoped syntax "I " : cell
scoped syntax "O " : cell
scoped syntax "T " : cell
scoped syntax "S " : cell
scoped syntax "Z " : cell
scoped syntax "J " : cell
scoped syntax "L " : cell

syntax row := withPosition((lineEq cell)*)
scoped syntax (name := board) "board " sepByIndentSemicolon(row) : term

open Lean.Macro in
macro_rules
  | `(term| board $rows:row*) => do
    let rows := ← (rows : TSyntaxArray `Taleve.row).reverse.mapM fun
      | `(row| $cells*) => do
        let cells := ← cells.mapM fun
          | `(cell| -) => ``(none)
          | `(cell| #) => ``(some Mino.gray)
          | `(cell| I) => ``(some (Mino.colored Piece.I))
          | `(cell| O) => ``(some (Mino.colored Piece.O))
          | `(cell| T) => ``(some (Mino.colored Piece.T))
          | `(cell| S) => ``(some (Mino.colored Piece.S))
          | `(cell| Z) => ``(some (Mino.colored Piece.Z))
          | `(cell| J) => ``(some (Mino.colored Piece.J))
          | `(cell| L) => ``(some (Mino.colored Piece.L))
          | _ => throwUnsupported
        -- Use `:)` so that type errors are reported using `Row` instead of the underlying `Vector`.
        ``((Row.mk #v[ $[$cells],* ] :))
      | _ => throwUnsupported
    -- Use `:)` so that type errors are reported using `Board` instead of the underlying `Vector`.
    ``((Board.mk #v[ $[$rows],* ] :))

@[app_unexpander Board.mk]
def unexpandBoard : Unexpander
  | `($_boardMk { toArray := #[$rows,*], size_toArray := $_ }) => do
    let rows := ← (rows : TSyntaxArray `term).reverse.mapM fun
      | `(Row.mk { toArray := #[$cells,*], size_toArray := $_ }) => do
        let cells := ← (cells : TSyntaxArray `term).mapM fun
          | `(none) => `(cell| -)
          | `(some Mino.gray) => `(cell| #)
          -- FIXME this doesn't work
          | `(some (Mino.colored Piece.I)) => `(cell| I)
          | `(some (Mino.colored Piece.O)) => `(cell| O)
          | `(some (Mino.colored Piece.T)) => `(cell| T)
          | `(some (Mino.colored Piece.S)) => `(cell| S)
          | `(some (Mino.colored Piece.Z)) => `(cell| Z)
          | `(some (Mino.colored Piece.J)) => `(cell| J)
          | `(some (Mino.colored Piece.L)) => `(cell| L)
          | _ => throw ()
        `(row| $cells*)
      | _ => throw ()
    `(board $rows;*)
  | _ => throw ()

private def testBoard : Board 10 4 := board
  Z Z - - # - J J J I
  T Z Z - - # O O J I
  T T S S # - O O L I
  T S S - - # L L L I

end Taleve
