-- The shim maps names starting with `Sorry.` to a `sorryAx` dependency,
-- so this simulates a real-world custom-axiom finding (a file that
-- accidentally uses `sorry`). The RED "uses non-standard axiom" line
-- should fire and the run should exit non-zero.
namespace Sorry

theorem needs_sorry : True := trivial

end Sorry
