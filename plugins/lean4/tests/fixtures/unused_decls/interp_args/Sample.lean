import Lean
open Lean Meta
-- Fixture (#185 review): a string interpolates exactly where Lean's syntax
-- says so. `throwErrorAt ref "…"` (ref an identifier, or `stx.getArgs[0]!`
-- followed by a comment) and `trace[cls] "…"` interpolate after their
-- argument, so `live` and `used` are referenced. `logInfo`, `Lean.logInfo`
-- and `panic!` take ordinary strings, whose `{…}` is literal text, so
-- `dead`, `dead2` and `dead3` are not.
def live : Nat := 1
def used : Nat := 2
def viaAt : CoreM Unit := throwErrorAt Syntax.missing "value: {live}"
def viaIdx (stx : Syntax) : CoreM Unit :=
  throwErrorAt stx.getArgs[0]! /- ref -/ "value: {live}"
def viaTrace : MetaM Unit := do trace[Meta.debug] "value: {used}"
def dead : Nat := 3
def dead2 : Nat := 4
def dead3 : Nat := 5
def viaLog : CoreM Unit := logInfo "value: {dead}"
def viaQual : CoreM Unit := Lean.logInfo "value: {dead2}"
def viaPanic : String := panic! "value: {dead3}"
#check viaAt
#check viaIdx
#check viaTrace
#check viaLog
#check viaQual
#check viaPanic
