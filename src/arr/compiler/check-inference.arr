#lang pyret

provide *
provide-types *

import ast as A
import parse-pyret as PP
import option as O
import "compiler/type-constraints.arr" as TC
import "compiler/type-structs.arr" as TS
import "compiler/gensym.arr" as G

type Type = TS.Type


fun bind(op, fn):
  doc:```added bind for maybe monad to make some of the type constraint stuff
         easier```
  cases (Option) op:
    | some(n) => fn(n)
    | none => none
  end
end


# from type-structs.arr
# data Type:
#   | t-name(module-name :: Option<String>, id :: Name)
#   | t-var(id :: Name)
#   | t-arrow(args :: List<Type>, ret :: Type)
#   | t-app(onto :: Type % (is-t-name), args :: List<Type> % (is-link))
#   | t-top
#   | t-bot
#   | t-record(fields :: TypeMembers)
#   | t-forall(introduces :: List<TypeVariable>, onto :: Type)
#   | t-ref(typ :: Type)
# end

# t-number  = t-name(none, A.s-type-global("Number"))
# t-string  = t-name(none, A.s-type-global("String"))
# t-boolean = t-name(none, A.s-type-global("Boolean"))

fun get-info(exp :: A.Expr) -> Option<Type>:
  doc:```
      Extracts a type from an expression. Currently, only a subset of types are
      supported. We return none for unsupported types.
      ```
  fun get-name(name :: A.Name) -> Option<Type>:
    doc:```
        generate a type-variable for an identifier
        TODO: get this to work for same id -> same type variable
        ```
    cases (A.Name) name:
     | s-name(l, s) => some(TS.t-var(A.s-name(l, G.make-name(s))))
     | else => none #raise("[check-inferer] unsupported namespace")
    end
  end

  cases (A.Expr) exp:
   | s-str(_, s) => some(TS.t-string)
   | s-bool(_, b) => some(TS.t-boolean)
   | s-num(_, n) => some(TS.t-number)
   | s-id(_, id) => get-name(id)
   | s-app(_, func, args) => f-type = cases (A.Expr) func:
                                       | s-id(_, id) => get-name(id)
                                       | else        => none
                                      end
                             # this type might be wrong
                             arg-types = args.foldr(lam(shadow exp, acc):
                                 cases (Option<Type>) get-info(exp):
                                   | some(t) => link(t, acc)
                                   | none    => acc
                                 end
                               end, empty)

                             f-type.and-then(lam(t :: TS.Type): (TS.t-arrow(arg-types, t)) end)
   | else => raise("[check-inferer] trying to infer on something that, like, come on.")
  end
end

fun make-cons(lhs :: Option<Type>, rhs :: Option<Type>) -> Option<TC.TypeConstraint>:
  doc: ```
       Given the type information from the left and right hand sides of an
       is check operation, generate a type constraint if possible
       ```
  bind(lhs,
      lam(l-type :: Type): bind(rhs,
      lam(r-type :: Type): some(TC.Bounds(l-type, r-type)););)
 end



check-inferer = A.default-map-visitor.{
  s-check-test(self, l, op, refinement, left, right):

    when op == A.s-op-is:
      lhs = get-info(left)
#print(lhs)
      when is-some(right):
        print(make-cons(lhs, bind(right, lam(e :: A.Expr): get-info(e);)))
      end
    end
    # this line is for default-map-visitor:
    A.s-check-test(l, op, self.option(refinement), left.visit(self), self.option(right))
  end
}
check:
  d = A.dummy-loc
  le-program = ```
fun add1(x):
  x + 1
where:
  add1(2) is 3
end
  ```
  PP.surface-parse(le-program, "test").visit(check-inferer)#.visit(A.dummy-loc-visitor)
  is A.s-id(d, A.s-name(d, "x"))
end
