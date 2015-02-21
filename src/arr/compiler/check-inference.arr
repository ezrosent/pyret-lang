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
  s-check(self, l, name, body, keyword-check):
    print(name)
    print(body)

    fun get-Op(exp :: A.Expr):
      cases (A.Expr) exp:
        | s-app(_, func, args) => cases (A.Expr) func:
                                    | s-id(_, id) => [list: id]
                                    | else        => empty
                                  end
        | else => empty # raise("[check-inferer] wanted an app")
      end
    end
    
    names = cases (A.Expr) body:
      | s-block(shadow l, stmts) => stmts.map(lam(e):
          cases (A.Expr) e:
            | s-check-test(_, op, refin, left, right) => get-Op(left)
                 .append(cases (Option<A.Expr>) right:
                          | some(n) => get-Op(n)
                          | none => empty
                         end)
            | else => raise("[check-inferer] things other than s-check-test unsupported")
          end
         end).foldr(lam(el, acc): acc.append(el);, empty)
      | else => raise("[check-inferer] check block not in a block")
    end
    print(names)

    A.s-check(l, name, body.visit(self), keyword-check)
  end,
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

# check-stmts-visitor-new = A.default-map-visitor.{
#   s-check-test(self, l, op, refinement, left, right):
#     term = A.s-check-test(l, op, refinement, left, right)
#     fun check-op(fieldname):
#       A.s-app(l, A.s-dot(l, U.checkers(l), fieldname),
#         [list: ast-pretty(term), left, right.value, ast-srcloc(l)])
#     end
#     fun check-refinement(shadow refinement, fieldname):
#       A.s-app(l, A.s-dot(l, U.checkers(l), fieldname),
#         [list: ast-pretty(term), refinement, left, right.value, ast-srcloc(l)])
#     end
#     cases(A.CheckOp) op:
#       | s-op-is            =>
#         cases(Option) refinement:
#           | none                    => check-op("check-is")
#           | some(shadow refinement) => check-refinement(refinement, "check-is-refinement")
#         end
#       | s-op-is-not        =>
#         cases(Option) refinement:
#           | none                    => check-op("check-is-not")
#           | some(shadow refinement) => check-refinement(refinement, "check-is-not-refinement")
#         end
#       | s-op-is-op(opname)    =>
#         check-refinement(A.s-id(l, A.s-name(l, A.get-op-fun-name(opname))), "check-is-refinement")
#       | s-op-is-not-op(opname) =>
#         check-refinement(A.s-id(l, A.s-name(l, A.get-op-fun-name(opname))), "check-is-not-refinement")
#       | s-op-satisfies        =>
#         check-op("check-satisfies")
#       | s-op-satisfies-not    =>
#         check-op("check-satisfies-not")
#       | s-op-raises           =>
#         A.s-app(l, A.s-dot(l, U.checkers(l), "check-raises-str"),
#           [list: ast-pretty(term), ast-lam(left), right.value, ast-srcloc(l)])
#       | s-op-raises-not       =>
#         A.s-app(l, A.s-dot(l, U.checkers(l), "check-raises-not"),
#           [list: ast-pretty(term), ast-lam(left), ast-srcloc(l)])
#       | s-op-raises-other     =>
#         A.s-app(l, A.s-dot(l, U.checkers(l), "check-raises-other-str"),
#           [list: ast-pretty(term), ast-lam(left), right.value, ast-srcloc(l)])
#       | s-op-raises-satisfies =>
#         A.s-app(l, A.s-dot(l, U.checkers(l), "check-raises-satisfies"),
#           [list: ast-pretty(term), ast-lam(left), right.value, ast-srcloc(l)])
#       | s-op-raises-violates  =>
#         A.s-app(l, A.s-dot(l, U.checkers(l), "check-raises-violates"),
#           [list: ast-pretty(term), ast-lam(left), right.value, ast-srcloc(l)])
#       | else => raise("Check test operator " + op.label() + " not yet implemented at " + torepr(l))
#     end
#   end,
#   s-check(self, l, name, body, keyword-check):
#     # collapse check blocks into top layer
#     print("woah!")
#     body.visit(self)
#   end
# }

check:
  d = A.dummy-loc
  le-program = ```
fun add1(x):
  x + 1
where:
  add1(2) is 3
end

check "Hi there!":
  add1(5) is 6
  add2(4) is 6
end
  ```
  PP.surface-parse(le-program, "test").visit(check-inferer)#.visit(A.dummy-loc-visitor)
  is A.s-id(d, A.s-name(d, "x"))
end
