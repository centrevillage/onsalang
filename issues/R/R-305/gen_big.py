import sys, os
d = sys.argv[1]
n = int(sys.argv[2])
# a: one fn, many uses
open(f"{d}/a_uses.onsa", "w").write("fn BadFn() -> I32 { 1 }\npub fn f() -> I32 {\n  var t = 0\n" + "".join("  t = t + BadFn()\n" for _ in range(n)) + "  t\n}\n")
# b: many E0320 fns, 3 uses each
s = "".join(f"fn BadF{i}() -> I32 {{ {i} }}\n" for i in range(n))
s += "pub fn g() -> I32 {\n  var t = 0\n" + "".join(f"  t = t + BadF{i}() + BadF{i}() + BadF{i}()\n" for i in range(n)) + "  t\n}\n"
open(f"{d}/b_many_decls.onsa", "w").write(s)
# c: one fn with many E0320 locals
s = "pub fn g() -> I32 {\n" + "".join(f"  let badL{i} = {i}\n" for i in range(n)) + "  var t = 0\n" + "".join(f"  t = t + badL{i}\n" for i in range(n)) + "  t\n}\n"
open(f"{d}/c_many_locals.onsa", "w").write(s)
# d: giant string with holes of many E0320 locals
s = "pub fn g() -> Str uses {Alloc} {\n" + "".join(f"  let badL{i} = {i}\n" for i in range(n)) + "  \"" + " ".join("{badL%d}" % i for i in range(n)) + "\"\n}\n"
open(f"{d}/d_string_holes.onsa", "w").write(s)
# e: deep nesting of blocks with local used deepest
k = 60
s = "pub fn g(c: Bool) -> I32 {\n  let badV = 1\n" + "".join("  " * (i + 1) + "if c {\n" for i in range(k)) + "  " * (k + 1) + "badV\n" + "".join("  " * (k - i) + "} else { 0 }\n" for i in range(k)) + "}\n"
open(f"{d}/e_deep.onsa", "w").write(s)
# f: many fns, each with a E0320 local (n fns)
s = "".join(f"pub fn f{i}(badP: I32) -> I32 {{ badP + badP }}\n" for i in range(n))
open(f"{d}/f_many_fns_params.onsa", "w").write(s)
# g: many structs each with E0320 field, uses
s = "".join(f"pub struct S{i} {{ badF: I32 }}\npub fn r{i}(s: S{i}) -> I32 {{ s.badF }}\n" for i in range(n))
open(f"{d}/g_many_fields.onsa", "w").write(s)
# h: many types with same impl method bad name
s = "".join(f"pub struct S{i} {{ x: I32 }}\nimpl S{i} {{ pub fn Get(self) -> I32 {{ self.x }} }}\npub fn r{i}(s: S{i}) -> I32 {{ s.Get() }}\n" for i in range(n))
open(f"{d}/h_many_methods.onsa", "w").write(s)
