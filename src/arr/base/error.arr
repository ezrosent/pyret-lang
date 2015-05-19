provide *
provide-types *
# import arrays as A
# import lists as L

data RuntimeError:
  | message-exception(message :: String) with:
    _tostring(self, shadow tostring):
      self.message
    end
  | no-cases-matched(loc, val) with:
    _tostring(self, shadow tostring):
      "At " + self.loc.format(true) + ", no branches matched in the cases expression for value\n" + torepr(self.val)
    end
  | no-branches-matched(loc, expression :: String) with:
    _tostring(self, shadow tostring):
      "No branches matched in the `" + self.expression + "` expression at " + self.loc.format(true)
    end
  | internal-error(message, info-args) with:
    _tostring(self, shadow tostring):
      "Internal error: " + self.message + "; relevant arguments: " + torepr(self.info-args)
    end
  | field-not-found(loc, obj, field :: String) with:
    _tostring(self, shadow tostring):
      "Error at " + self.loc.format(true) + ": field " + self.field + " not found on " + torepr(self.obj)
    end
  | lookup-non-object(loc, non-obj, field :: String) with:
    _tostring(self, shadow tostring):
      "Error at " + self.loc.format(true) + ": tried to look up field " + self.field + " on " + torepr(self.non-obj) + ", but it does not have fields"
    end
  | extend-non-object(loc, non-obj) with:
    _tostring(self, shadow tostring):
      "Error at " + self.loc.format(true) + ": tried to extend a non-object " + torepr(self.non-obj)
    end
  | non-boolean-condition(loc, typ, value) with:
    _tostring(self, shadow tostring):
      "Error: expected a Boolean for the condition of a " + self.typ + " at " + self.loc.format(true) + ", but got " + torepr(self.value)
    end
  | non-boolean-op(loc, position, typ, value) with:
    _tostring(self, shadow tostring):
      "Error: expected a Boolean for the " + self.position + " argument to " + self.typ + " at " + self.loc.format(true) + ", but got " + torepr(self.value)
    end
  | generic-type-mismatch(val, typ :: String) with:
    _tostring(self, shadow tostring):
      "Error: expected " + self.typ + ", but got " + torepr(self.val)
    end
  | outside-numeric-range(val, low, high) with:
    _tostring(self, shadow tostring):
      "Error: expected a number between " + torepr(self.low) + " and " + torepr(self.high) + ", but got " + torepr(self.val)
    end
  | plus-error(val1, val2) with:
    _tostring(self, shadow tostring):
      "Error: Invalid use of +.  Either both arguments must be strings, both must be numbers, or the left operand must have a _plus method. Got: \n" + torepr(self.val1) + "\nand \n" + torepr(self.val2)
    end
  | numeric-binop-error(val1, val2, opname, methodname) with:
    _tostring(self, shadow tostring):
      "Error: Invalid use of " + self.opname + ".  Either both arguments must be numbers, or the left operand must have a " + self.methodname + " method.  Got: \n" + torepr(self.val1) + "\nand \n" + torepr(self.val2)
    end
  | cases-arity-mismatch(branch-loc, num-args, actual-arity) with:
    _tostring(self, shadow tostring):
      "Error: The cases branch at " + self.branch-loc.format(true) + " expects " + tostring(self.num-args)
        + " arguments, but the actual value has " + tostring(self.actual-arity)
        + (if self.actual-arity == 1: " field" else: " fields" end)
    end
  | cases-singleton-mismatch(branch-loc, should-be-singleton :: Boolean) with:
    _tostring(self, shadow tostring):
      if self.should-be-singleton:
        "Error: The cases branch at " + self.branch-loc.format(true) + " expects to receive parameters, but the value being examined is a singleton"
      else:
        "Error: The cases branch at " + self.branch-loc.format(true) + " expects the value being examined to be a singleton, but it actually has fields"
      end
    end
  | arity-mismatch(fun-loc, expected-arity, args) with:
    _tostring(self, shadow tostring):
      "Error: The function at " + self.fun-loc.format(true) + " expects " + tostring(self.expected-arity) + " arguments, but got " + tostring(self.args.length())
    end
  | non-function-app(loc, non-fun-val) with:
    _tostring(self, shadow tostring):
      "Error: Expected a function at " + self.loc.format(true) + ", but got " + torepr(self.non-fun-val)
    end
  | bad-app(loc, fun-name :: String, message :: String, arg-position :: Number, arg-val)
  | uninitialized-id(loc, name :: String) with:
    _tostring(self, shadow tostring):
      "Error: The identifier " + self.name + " was used at " + self.loc.format(true) + " before it was defined."
    end
  | module-load-failure(names) with: # names is List<String>
    _tostring(self, shadow tostring):
      "Error: The following modules failed to load: " + torepr(self.names)
    end
  | invalid-array-index(method-name :: String, array, index :: Number, reason :: String) with: # array is Array
    _tostring(self, shadow tostring):
      "Error: Bad array index " + tostring(self.index) + " in " + self.method-name + ": " + self.reason
    end
  | equality-failure(reason :: String, value1, value2) with:
    _tostring(self, shadow tostring):
      "Error: Attempted to compare incomparable values " + torepr(self.value1) +
        " and " + torepr(self.value2) + "; " + self.reason
    end

  | user-break
end

data ParseError:
  | parse-error-next-token(loc, next-token :: String) with:
    _tostring(self, shadow tostring):
      "parse error around " + self.loc.format(true) + ", next token was " + self.next-token
    end
  | parse-error-eof(loc) with:
    _tostring(self, shadow tostring):
      "parse error at end of file at " + self.loc.format(true)
    end
  | parse-error-unterminated-string(loc) with:
    _tostring(self, shadow tostring):
      "parse error with an incomplete string literal, starting around " + self.loc.format(true)
    end
  | empty-block(loc) with:
    _tostring(self, shadow tostring):
      "Empty block at " + self.loc.format(true)
    end
  | bad-block-stmt(loc) with:
    _tostring(self, shadow tostring):
      "Expected a val binding or an expression, but got something else " + self.loc.format(true)
    end
  | bad-check-block-stmt(loc) with:
    _tostring(self, shadow tostring):
      "Expected a val binding or an expression, but got something else " + self.loc.format(true)
    end
  | fun-missing-colon(loc) with:
    _tostring(self, shadow tostring): "fun-missing-colon: " + self.loc.format(true) end
  | fun-missing-end(loc) with:
    _tostring(self, shadow tostring): "fun-missing-end: " + self.loc.format(true) end
  | args-missing-comma(loc) with:
    _tostring(self, shadow tostring): "args-missing-comma: " + self.loc.format(true) end
  | app-args-missing-comma(loc) with:
    _tostring(self, shadow tostring): "app-args-missing-comma: " + self.loc.format(true) end
  | missing-end(loc)
  | missing-comma(loc)
end
