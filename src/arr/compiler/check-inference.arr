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

#TODO: Add support for environments
getEnv = lam(): empty;

setEnv = lam(l): l end



data TGuess:
  | f-guess(args :: List<Option<Type>>, rt :: Option<Type>)
  | id-guess(t :: Option<Type>)
end

data TInfo:
  | t-info(id :: String, guess :: List<TGuess>)
end


data IdInfo:
  | id-info(name :: String, ty :: Type)
end

type ReturnEnv = List<TInfo>
type TEnv = List<IdInfo>


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

check-inferer = A.default-map-visitor.{
  s-check(self, l, _name, body, keyword-check):
    print(_name)
    print(body)

    fun extract-name(n :: A.Name) -> Option<String>:
      doc:```
          Gets a string representation of a `Name`
          ```
      cases (A.Name) n:
        | s-name(loc, s) => some(s)
        | else           => none
      end
    end

    fun t-infer(env :: TEnv, exp :: A.Expr) -> Option<Type>:
      doc:```
          Infers best guess at the type of an expression given `env`
          ```
      cases (A.Expr) exp:
        | s-id(loc, id) => bind(extract-name(id), lam(s :: String):
          env.lookup(lam(t-i):
            t-i.id == s
          end)
        end)
        | s-str(loc, _)  => some(TS.t-string)
        | s-num(loc, _)  => some(TS.t-number)
        | s-bool(loc, _) => some(TS.t-boolean)
        | else           => none
      end
    end
    is-s-app = A.is-s-app
    shadow t-infer = t-infer(getEnv(), _)

    fun get-fun(exp :: A.Expr) -> Option<A.Expr%(is-s-app)>:
      doc:```
          This extracts a function from a given expression. Right now we do
          this in a shallow fashion, but we have it in a helper so we can add
          extra cases as we see fit.
          ```
      cases (A.Expr) exp:
        | s-app(loc, f, args) => some(exp)
        | else => none
      end
    end

    fun get-fun-name(_fun :: A.Expr) -> Option<String>:
      doc:```
          Attempts to find the name of a expression in function-position
          For now, this assumes that the function name is an s-id or an s-id-letrec,
          More complicated cases like
            lam(x):
              if x:
                fun-i-want-to-test-1
              else:
                fun-i-want-to-test-2
              end
            end(test-input)
          aren't handled right now because halting problem
          ```
      cases (A.Expr) _fun:
        | s-id(loc, name) => extract-name(name)
        | s-id-letrec(loc, name, _) => extract-name(name)
        | else => none
      end
    end

    fun add-guess(f-name :: String, guess :: TGuess, infos :: ReturnEnv) -> ReturnEnv:
      doc:```
          Adds the guess for the type of f-name to infos.
          ```
      cases (List<TInfo>) infos:
        | empty => [list: t-info(f-name, [list: guess])]
        | link(f, r) => if f.id == f-name:
          link(t-info(f-name, link(guess, f.guess)), r)
          else:
            link(f, add-guess(f-name, guess, r))
          end
      end
    end

    fun infer-binding(app :: A.Expr%(is-s-app), rt :: Option<Type>, rest) -> ReturnEnv:
      doc:```
          Given a function application, adds a guess at the function's type to the value
          returned by `rest`
          ```
      cases (Option<String>) get-fun-name(app._fun):
        | none => rest()
        | some(n) => print("infer-binding:")
            print(n)
            args = app.args.map(t-infer)
            add-guess(n, f-guess(args, rt), rest())
      end
    end

    fun t-bind(elist :: List<A.Expr>) -> ReturnEnv:
      cases (List<A.Expr>) elist:
        | empty => empty
        | link(f, r) => recur = lam(): t-bind(r) end
         cases (A.Expr) f:
           | s-check-test(loc, op, refinement, left, right) => #TODO: only assuming op-is
             l-fun = print(get-fun(left))
             r-fun = print(bind(right, lam(shadow right): get-fun(right);))
             ask:
               | is-none(l-fun) and is-none(r-fun) then: recur()
               | is-none(l-fun) and is-some(r-fun) then: infer-binding(r-fun.value, t-infer(left), recur)
               | is-some(l-fun) and is-none(r-fun) then: infer-binding(l-fun.value, print(bind(right,
                     lam(shadow right): t-infer(right);)), recur)
               | is-some(l-fun) and is-some(r-fun) then: l-funs = infer-binding(l-fun.value(), none, recur)
                                                         infer-binding(r-fun.value(), none, lam(): l-funs;)
               | otherwise: raise("[check-infer/t-bind] impossible state")
             end

           # TODO: do we care about annotation on `name`
           | s-let(loc, binding, value, _) =>
             cases (Option) t-infer(getEnv(), value):
               | none => recur()
               | some(n) =>
                   setEnv(link(id-info(binding.id, n), getEnv()))
                   recur()
             end
          | else => recur()
         end
      end
    end

    print(t-bind(body.stmts))
    A.s-check(l, _name, body.visit(self), keyword-check)
  end,
}


check:
  d = A.dummy-loc
  le-program = ```
fun add1(x):
  x + 1
end

check "Hi there!":
  add1(6) is 7
  add1(4) is 5
  add2(6) is 8
end
  ```
  PP.surface-parse(le-program, "test").visit(check-inferer)
  satisfies (lam(x): true;)
end
