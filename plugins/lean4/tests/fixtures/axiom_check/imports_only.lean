-- Fixture: file has NO declarations at all — just imports and comments.
-- This is a legitimate declaration-free file. The heuristic must NOT
-- mark it UNVERIFIED (false positive) — it must fall through to the
-- "No declarations found" branch and return cleanly.
import Init

-- A comment about the module.
