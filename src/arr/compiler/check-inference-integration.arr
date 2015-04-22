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

  datatype-program-sparse= ```
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
  foobar(foo) is foo
end
```
  parse1=str-to-ast(datatype-program-sparse)
   T.type-check(parse1, libs) satisfies C.is-ok

  datatype-program-sparse-where= ```
data Foo:
  | foo
  | bar(x,y)
end

fun foobar(f):
  cases (Foo) f:
    | foo => bar(4, 4)
    | bar(_,_) => foo
   end
where:
  foobar(foo) is foo
  foobar(foo) is foo
end
```
#   desugar1 = RS.desugar-scope(PP.surface-parse(datatype-program-sparse, "test"), libs)
#   desugar2 = RS.desugar-scope(PP.surface-parse(datatype-program-sparse-where, "test"), libs)
# parse2 = str-to-ast(datatype-program-sparse-where)
#   print(desugar1)
#      print(desugar2)
   fancy-program=```
data Animal:
  | boa(name :: String, length :: Number)
  | armadillo(name :: String, is-alive :: Boolean)
end

s1 = boa("Slithers", 10)
s2 = boa("Monty", 5)
s3 = boa("Feathered", 15)
a1 = armadillo("Houston", true)
a2 = armadillo("Austin", false)

fun to-transport(a):
  cases (Animal) a:
    | boa(n, _) => not(n == "Monty")
    | armadillo(_, is-alive) => is-alive
  end
end

fun run-over-1(a):
  cases (Animal) a:
    | boa(_, _) => raise("doesn't apply to boas")
    | armadillo(n, _) => armadillo(n, false)
  end
end

check:
  run-over-1(a1) is armadillo("Houston", false)
  run-over-1(a2) is armadillo("Austin", false)
  run-over-1(s1) raises ""
  to-transport(a1) is false
  to-transport(s1) is true
end

fun run-over-2(a):
  armadillo(a.name, false)
end
check:
  run-over = run-over-2
  run-over-2(a1) is armadillo("Houston", false)
  run-over-2(a2) is armadillo("Austin", false)
  run-over-2(s1) is armadillo("Slithers", false) # WRONG!
end

fun run-over-3(a :: Animal%(is-armadillo)):
  armadillo(a.name, false)
end
check:
  run-over-3(a1) is armadillo("Houston", false)
  run-over-3(a2) is armadillo("Austin", false)
  run-over-3(s1) raises ""
end
 ```
  T.type-check(str-to-ast(fancy-program), libs) satisfies C.is-ok

  stream-program = ```

data Stream<T>:
  | lz-link(h :: T, t :: ( -> Stream<T>))
end

rec ones = lz-link(1, lam(): ones end)
fun nats-from(n :: Number): lz-link(n, lam(): nats-from(n + 1) end) end
rec nats = nats-from(0)

fun lz-first<T>(s :: Stream<T>) -> T: s.h end
fun lz-rest<T>(s :: Stream<T>) -> Stream<T>: s.t() end

fun take<T>(n, s :: Stream<T>) -> List<T>:
  if n == 0:
    empty
  else:
    link(lz-first(s), take(n - 1, lz-rest(s)))
  end
end

fun lz-map2<A,B>(f :: (A, A -> B),
                  s1 :: Stream<A>, s2 :: Stream<A>)
    -> Stream<B>:
  lz-link(f(lz-first(s1), lz-first(s2)),
    lam(): lz-map2(f, lz-rest(s1), lz-rest(s2)) end)
end

fun lz-map(f, s): lz-link(f(lz-first(s)), lam(): lz-map(f, lz-rest(s)) end) end

check:
  take(3, ones) is [list: 1, 1, 1]
  take(10, nats) is range(0, 10)
  take(10, nats-from(1)) is map((_ + 1), range(0, 10))
end
  ```
#TODO: type of nats-from isn't inferred since it's in another one!
#TODO: Lists. We're not recognizing them. Imports? Data types? Exprs?
#TODO: Lists and Options are parameterized types. What even are those!
#TODO: inferring data field types from tests
#TODO: It didn't like fold and empty :(
#TODO: We just added s-id-letrec. Do we need to care about s-id-var?
#T.type-check(str-to-ast(stream-program), libs) satisfies C.is-ok

  bst-program = ```
  data BT:
  | leaf
  | node(v :: Number, l :: BT, r :: BT)
end

# Buggy well-formedness check
fun is-a-bst-buggy(b) -> Boolean:
  cases (BT) b:
    | leaf => true
    | node(v, l, r) =>
    (cases (BT) l:
      | leaf => true
      | node(lv, ll, lr) => lv <= v
    end) and
    (cases (BT) r:
      | leaf => true
      | node(rv, rl, rr) => v <= rv
    end) and
    is-a-bst-buggy(l) and is-a-bst-buggy(r)
  end
end

check:
  is-a-bst-buggy(node(5, leaf, leaf)) is true
  is-a-bst-buggy(node(5, node(3, leaf, leaf), node(7, leaf, leaf))) is true
  is-a-bst-buggy(node(5, node(3, node(1, leaf, leaf), node(4, leaf, leaf)), leaf)) is true
  is-a-bst-buggy(node(5, node(3, node(4, leaf, leaf), leaf), leaf)) is false
  is-a-bst-buggy(node(5, node(6, leaf, leaf), leaf)) is false
  is-a-bst-buggy(node(5, node(3, node(6, leaf, leaf), leaf), leaf)) is false
  is-a-bst-buggy(node(5, node(3, leaf, node(6, leaf, leaf)), leaf))
    is true # WRONG!
end

# Well-formedness check for BSTs
fun is-a-bst(big-b) -> Boolean:
  fun walker(b :: BT, checker :: (Number -> Boolean)) -> Boolean:
    cases (BT) b:
      | leaf => true
      | node(v, l, r) =>
        checker(v) and
        walker(l,
          lam(n :: Number):
            (n <= v) and checker(n)
          end)
        and
        walker(r,
          lam(n :: Number):
            (n >= v) and checker(n)
          end)
    end
  end
  walker(big-b, lam(n): true end)
end

check:
  is-a-bst(node(5, leaf, leaf)) is true
  is-a-bst(node(5, node(3, leaf, leaf), node(7, leaf, leaf))) is true
  is-a-bst(node(5, node(3, node(1, leaf, leaf), node(4, leaf, leaf)), leaf)) is true
  is-a-bst(node(5, node(3, node(4, leaf, leaf), leaf), leaf)) is false
  is-a-bst(node(5, node(6, leaf, leaf), leaf)) is false
  is-a-bst(node(5, node(3, node(6, leaf, leaf), leaf), leaf)) is false
  is-a-bst(node(5, node(3, leaf, node(6, leaf, leaf)), leaf)) is false
end
##
type BST = BT%(is-a-bst)
type TSet = BST

mt-set = leaf

fun is-in-bt(e, s):
  cases (BT) s:
    | leaf => false
    | node(v, l, r) =>
      if e == v:
        true
      else:
        is-in-bt(e, l) or is-in-bt(e, r)
      end
  end
end

fun is-in(e, s):
  cases (BT) s:
    | leaf => false
    | node(v, l, r) =>
      if e == v:
        true
      else if e < v:
        is-in(e, l)
      else if e > v:
        is-in(e, r)
      end
  end
end
#
fun insert(e, s):
  cases (BT) s:
    | leaf => node(e, leaf, leaf)
    | node(v :: Number, l :: BT, r :: BT) =>
      if e == v:
        s
      else if e < v:
        node(v, insert(e, l), r)
      else if e > v:
        node(v, l, insert(e, r))
      end
  end
end
#


fun size(s):
  cases (BST) s:
    | leaf => 0
    | node(v, l, r) =>
      1 + size(l) + size(r)
  end
end

#
check:
  s09 =  node(1, leaf,
    node(2, leaf,
      node(3, leaf,
        node(4, leaf, leaf))))
#
#insert-many(range(0, 10), mt-set)
#
  is-in-bt(5, s09) is true
  is-in-bt(11, s09) is false
#
  is-in(5, s09) is true
  is-in(11, s09) is false
  size(insert(5, insert(5, mt-set))) is 1
  size(leaf) is 1
insert(4, s09) is node(4, leaf, leaf)
 insert(4, leaf) is node(4, leaf, leaf)
  insert(4, insert(3, insert(2, insert(1, mt-set)))) is
  node(1, leaf,
    node(2, leaf,
      node(3, leaf,
        node(4, leaf, leaf))))

  insert(5, insert(5, mt-set)) satisfies is-a-bst
  insert(4, insert(3, insert(2, insert(1, mt-set)))) satisfies is-a-bst
end
 ```

  T.type-check(str-to-ast(bst-program),libs) satisfies C.is-ok
end

