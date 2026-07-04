-- Locks in dotted-namespace qualification: `namespace Foo.Bar` is a
-- single frame `ns:Foo.Bar`, so `quux` gets prefix `Foo.Bar.`, not
-- `Foo.Bar.quux` broken into two frames.
namespace Foo.Bar

theorem quux : True := trivial

end Foo.Bar
