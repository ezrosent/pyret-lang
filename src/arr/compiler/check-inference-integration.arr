provide *
provide-types *

import ast as A
import parse-pyret as PP
import option as O

import "compiler/type-structs.arr" as TS
import "compiler/type-check.arr" as T
import "compiler/type-check-structs.arr" as TCS
import "compiler/gensym.arr" as G
import "compiler/compile-structs.arr" as C
import "compiler/resolve-scope.arr" as RS
import "compiler/desugar.arr" as D
import string-dict as SD

libs = C.minimal-builtins

fun str-to-ast(str):
  D.desugar(RS.resolve-names(RS.desugar-scope(PP.surface-parse(str, "test"), libs), libs).ast, libs)
end

check:
    datatype-program = ```
data Foo:
  | foo
  | bar(x,y)
end

fun foobar(f):
  cases (Foo) f:
    | foo => bar(4, 4)
    | bar(_,_) => foo
   end
end


check "ohhh goodness":
  baz = foo
  foobar(foo) is bar(4, 4)
  foobar(bar(4, 4)) is baz
end
  ```
    print(T.type-check(str-to-ast(datatype-program), libs)) satisfies C.is-ok
end
