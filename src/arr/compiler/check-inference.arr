#lang pyret

provide *
provide-types *

import ast as A
import parse-pyret as PP
import option as O
import "compiler/type-check.arr" as TC
import "compiler/type-structs.arr" as TS
import "compiler/type-check-structs.arr" as TCS
import "compiler/gensym.arr" as G
import "compiler/compile-structs.arr" as C
import "compiler/resolve-scope.arr" as RS
import string-dict as SD

type Type = TS.Type

fun bind(op, fn):
  doc:```added bind for maybe monad to make some of the type constraint stuff
  easier```
  cases (Option) op:
    | some(n) => fn(n)
    | none => none
  end
end

#TODO: Add inference for identifiers
#TODO: turn ReturnEnv into mutablestringdict

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

is-t-record = TS.is-t-record


#variant data constructor name -> type of data
type VariantEnv = SD.MutableStringDict<Type>

type ReturnEnv = List<TInfo>
type TEnv = List<IdInfo>

fun extract-name(n :: A.Name) -> Option<String>:
  doc:```
      Gets a string representation of a `Name`
      ```
  cases (A.Name) n:
    | s-name(loc, s) => some(s)
    | else           => none
  end
end


is-s-app = A.is-s-app
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

fun datatype-infer(ast :: A.Program) -> VariantEnv:
  info = TCS.empty-tc-info("data-scrape")
  ret = [SD.mutable-string-dict:]
  ast.visit(A.default-map-visitor.{
    s-data-expr(
        self,
        loc :: A.Loc,
        name :: String,
        namet :: A.Name,
        params :: List<A.Name>, # type params
        mixins :: List<A.Expr>,
        variants :: List<A.Variant>,
        shared-members :: List<A.Member>,
        _check :: Option<A.Expr>
      ):
#print(variants)
#      typ = TC.synthesis-datatype(loc, name, namet, params,
#          mixins, variants, shared-members, _check, info).typ
      typ = TS.t-var(namet)
      variants.map(lam(v): ret.set-now(v.name, typ);)
      A.s-data-expr(
          loc,
          name,
          namet.visit(self),
          params.map(_.visit(self)),
          mixins.map(_.visit(self)),
          variants.map(_.visit(self)),
          shared-members.map(_.visit(self)),
          self.option(_check)
        )
    end

  })
  print(ret.keys-now().to-list())
  ret

end

check-inferer = lam(sd :: VariantEnv):
  var _env = empty
  var _retenv = empty
  fun t-infer(env :: TEnv, exp :: A.Expr) -> Option<Type>:
    doc:```
        Infers best guess at the type of an expression given `env`
        ```
    cases (A.Expr) exp:
      | s-id(loc, id) => cases (Option<Type>) bind(extract-name(id), sd.get-now(_)):
        | none => bind(extract-name(id), lam(s :: String):
                    bind(env.find(lam(t-i):
                      t-i.name == s
                    end), lam(info): some(info.ty);)
                  end)
        | some(n) => some(n)
       end
      | s-str(loc, _)  => some(TS.t-string)
      | s-num(loc, _)  => some(TS.t-number)
      | s-bool(loc, _) => some(TS.t-boolean)
      | s-app(loc, f, args) => bind(get-fun-name(f), sd.get-now(_))
      | else           => none
    end
  end

  fun get-fun(exp :: A.Expr) -> Option<A.Expr%(is-s-app)>:
    doc:```
        This extracts a function from a given expression. Right now we do
        this in a shallow fashion, but we have it in a helper so we can add
        extra cases as we see fit.
        ```
    cases (A.Expr) exp:
      | s-app(loc, f, args) =>  cases (Option<String>) get-fun-name(f):
                                  | none => none
                                  | some(n) => cases (Option<Type>) sd.get-now(n):
                                                 | none => some(exp)
                                                 | some(_) => none
                                               end
                                end
      | else => none
    end
  end


  A.default-map-visitor.{
  ret-env(self):
    _retenv
  end,
  set-retenv(self, re):
    _retenv := re

    end,
  s-check(self, l, _name, body, keyword-check):
    shadow t-infer = t-infer(self.getEnv(), _)

    fun infer-binding(app :: A.Expr%(is-s-app), rt :: Option<Type>, rest :: (-> ReturnEnv)) -> ReturnEnv:
      doc:```
          Given a function application, adds a guess at the function's type to the value
          returned by `rest`
          ```
      cases (Option<String>) get-fun-name(app._fun):
        | none => rest()
        | some(n) =>
            args = app.args.map(t-infer)
            add-guess(n, f-guess(args, rt), rest())
      end
    end

    fun t-bind(elist :: List<A.Expr>) -> ReturnEnv:
      doc:```
          Generates a list of guesses (potential types) for functions in the check block
          ```
      cases (List<A.Expr>) elist:
        | empty => empty
        | link(f, r) => recur = lam(): t-bind(r) end
         cases (A.Expr) f:
           | s-check-test(loc, op, refinement, left, right) => #TODO: only assuming op-is
             l-fun = get-fun(left)
             r-fun = bind(right, lam(shadow right): get-fun(right);)
             ask:
               | is-none(l-fun) and is-none(r-fun) then: recur()
               | is-none(l-fun) and is-some(r-fun) then: infer-binding(r-fun.value, t-infer(left), recur)
               | is-some(l-fun) and is-none(r-fun) then: infer-binding(l-fun.value, bind(right,
                     lam(shadow right): t-infer(right);), recur)
               | is-some(l-fun) and is-some(r-fun) then: l-funs = infer-binding(l-fun.value, none, recur)
                                                         infer-binding(r-fun.value, none, lam(): l-funs;)
               | otherwise: raise("[check-infer/t-bind] impossible state")
             end

           # TODO: do we care about annotation on `name`
           | s-let(loc, binding, value, _) =>
             cases (Option) t-infer(value):
               | none => recur()
               | some(n) =>
                   self.setEnv(link(id-info(extract-name(binding.id).value, n), self.getEnv()))
                   recur()
             end
          | else => recur()
         end
      end
    end
    self.set-retenv(t-bind(body.stmts) + self.ret-env())
    A.s-check(l, _name, body.visit(self), keyword-check)
  end,
  setEnv(self, new-env :: TEnv):
    _env := new-env
  end,
  getEnv(self):
    _env
  end
}
end

fun check-infer(ast :: A.Program) -> ReturnEnv:
  doc:```
      Performs type inference of the ast's checks, and returns the types inferred
      in the form of a ReturnEnv.
      ```
  variant-dict = datatype-infer(ast)
  checker = check-inferer(variant-dict)
  ast.visit(checker)
  checker.ret-env()
end

fun has-type(re :: ReturnEnv, id :: String, guess :: TGuess) -> Boolean:
  cases (Option<TInfo>) re.find(lam(t-i): t-i.id == id;):
    | some(info) => is-some(info.guess.find(lam(g): g == guess;))
    | none => false
  end
end

check:
  one-check = ```
  fun add1(x):
    x + 1
  end

  check "check block 1":
    add1(3) is 5
  end
  ```
  one-check-res = check-infer(PP.surface-parse(one-check, "test"))
  one-check-res satisfies has-type(_, "add1", f-guess([list: some(TS.t-number)], some(TS.t-number)))

  multiple-functions-ids = ```
fun add1(x):
  x + 1
end
fun n(b):
  not(b)
end

check "Hi there!":
  a = 7
  s = "hithere"
  add1(6) is a
  add1(a) is 5
  add2(s, 44) is "hithere"
  "hithere" is id(s)
  n(true) is false
  p("hello!") is q(true)
end
  ```
  multiple-funs-res = check-infer(PP.surface-parse(multiple-functions-ids, "test"))
  multiple-funs-res satisfies has-type(_, "add1", f-guess([list: some(TS.t-number)], some(TS.t-number)))
  multiple-funs-res satisfies has-type(_, "id", f-guess([list: some(TS.t-string)], some(TS.t-string)))
  multiple-funs-res satisfies has-type(_, "n", f-guess([list: some(TS.t-boolean)], some(TS.t-boolean)))
  multiple-funs-res satisfies has-type(_, "add2", f-guess([list: some(TS.t-string), some(TS.t-number)], some(TS.t-string)))
  multiple-funs-res satisfies has-type(_, "p", f-guess([list: some(TS.t-string)], none))
  multiple-funs-res satisfies has-type(_, "q", f-guess([list: some(TS.t-boolean)], none))

  datatype-program = ```
data Foo:
  | foo
  | bar(x,y)
end

fun foobar(f):
  cases (Foo) f:
    | foo => bar(none, none)
    | bar(_,_) => foo
   end
end


check "ohhh goodness":
  foobar(foo) is bar(none, none)
  foobar(bar(none, none)) is foo
end
  ```
  prog = PP.surface-parse(datatype-program, "test")
  # desugar data exprs
  datatype-res = check-infer(RS.desugar-scope(prog, C.minimal-builtins))
  print(datatype-res)
end
