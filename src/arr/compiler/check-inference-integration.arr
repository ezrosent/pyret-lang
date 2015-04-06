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
  multiple-function-ids = ```
fun add1(x):
  x + 1
end
fun id(x): x end
fun n(b):
  not(b)
end
fun p(s):
  "hi"
end
fun q(b):  if b: "hi" else: "hello" end end

fun add2(s, n):
  "hithere"
end

check "Hi there!":
  a = 7
  s = "hithere"
  add1(6) is a
  add1(a) is 5
  add2(s, 44) is "hithere"
  "hithere" is id(s)
  n(true) is false
  q(true) is p("hi")
end
  ```
  T.type-check(str-to-ast(multiple-function-ids),libs) satisfies C.is-ok
  mulmlul = ```
fun blurp(s):
  s + "HI"
end

check "blurp":
  blurp("blurp") satisfies (_ == "blurpHI")
end
```
  T.type-check(str-to-ast(mulmlul), libs) satisfies C.is-ok

#  polymorphism = ```
#fun id(x): x end
#check "look over there":
#  id(1) is 1
#  id("hi") is "hi"
#  id("bool") is "bool"
#end
#```
#  print(T.type-check(str-to-ast(polymorphism),libs)) satisfies C.is-ok
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
  foobar(baz) is foo
end
  ```
   T.type-check(str-to-ast(datatype-program), libs) satisfies C.is-ok
end
