define(['./rnglr'],
/** @param {{Grammar : {fromSerializable : !Function}, Nonterm : !Object, Token : !Object, Rule : !Object}} E */
function(E) {
  const Grammar = E.Grammar;
  const Nonterm = E.Nonterm;
  const Token = E.Token;
  const Rule = E.Rule;

  var g_json = {
    "start": "START",
    "name": "grammar",
    "acceptStates": [
      0,
      1
    ],
    "mode": "RNGLR",
    "derivable": {
      "program": [
        "prelude",
        "prelude_I0_opt",
        "prelude_I1_star",
        "ε",
        "prelude_I0",
        "provide-stmt",
        "prelude_I1",
        "import-stmt",
        "block",
        "stmt",
        "block_I0_star",
        "block_I0",
        "let-expr",
        "fun-expr",
        "data-expr",
        "datatype-expr",
        "when-expr",
        "var-expr",
        "assign-expr",
        "check-test",
        "check-expr",
        "graph-expr",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "prelude": [
        "prelude_I0_opt",
        "prelude_I1_star",
        "ε",
        "prelude_I0",
        "provide-stmt",
        "prelude_I1",
        "import-stmt"
      ],
      "block": [
        "block_I0_star",
        "ε",
        "block_I0",
        "stmt",
        "let-expr",
        "fun-expr",
        "data-expr",
        "datatype-expr",
        "when-expr",
        "var-expr",
        "assign-expr",
        "check-test",
        "check-expr",
        "graph-expr",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "end": [],
      "prelude_I0_opt": [
        "ε",
        "prelude_I0",
        "provide-stmt"
      ],
      "prelude_I1_star": [
        "ε",
        "prelude_I1",
        "import-stmt"
      ],
      "prelude_I0": [
        "provide-stmt"
      ],
      "provide-stmt": [],
      "prelude_I1": [
        "import-stmt"
      ],
      "import-stmt": [],
      "import-stmt_I1": [
        "import-name",
        "import-string"
      ],
      "import-name": [],
      "import-string": [],
      "stmt": [
        "let-expr",
        "fun-expr",
        "data-expr",
        "datatype-expr",
        "when-expr",
        "var-expr",
        "assign-expr",
        "check-test",
        "check-expr",
        "graph-expr",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "block_I0_star": [
        "ε",
        "block_I0",
        "stmt",
        "let-expr",
        "fun-expr",
        "data-expr",
        "datatype-expr",
        "when-expr",
        "var-expr",
        "assign-expr",
        "check-test",
        "check-expr",
        "graph-expr",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "block_I0": [
        "stmt",
        "let-expr",
        "fun-expr",
        "data-expr",
        "datatype-expr",
        "when-expr",
        "var-expr",
        "assign-expr",
        "check-test",
        "check-expr",
        "graph-expr",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "let-expr": [],
      "fun-expr": [],
      "data-expr": [],
      "datatype-expr": [],
      "when-expr": [],
      "var-expr": [],
      "assign-expr": [],
      "check-test": [
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "check-expr": [],
      "graph-expr": [],
      "binding": [],
      "binop-expr": [
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "binding_I0_opt": [
        "ε",
        "binding_I0"
      ],
      "binding_I2_opt": [
        "ε",
        "binding_I2"
      ],
      "binding_I0": [],
      "binding_I2": [],
      "ann": [
        "name-ann",
        "record-ann",
        "arrow-ann",
        "app-ann",
        "pred-ann",
        "dot-ann"
      ],
      "fun-header": [],
      "doc-string": [
        "doc-string_I0_opt",
        "ε",
        "doc-string_I0"
      ],
      "where-clause": [
        "where-clause_I0_opt",
        "ε",
        "where-clause_I0"
      ],
      "ty-params": [
        "ty-params_I0_opt",
        "ε",
        "ty-params_I0"
      ],
      "args": [],
      "return-ann": [
        "return-ann_I0_opt",
        "ε",
        "return-ann_I0"
      ],
      "ty-params_I0_opt": [
        "ε",
        "ty-params_I0"
      ],
      "ty-params_I0": [],
      "ty-params_I0_I1_star": [
        "ε",
        "ty-params_I0_I1",
        "list-ty-param"
      ],
      "ty-params_I0_I1": [
        "list-ty-param"
      ],
      "list-ty-param": [],
      "args_I0": [],
      "args_I1_opt": [
        "ε",
        "args_I1",
        "binding"
      ],
      "args_I1": [
        "binding"
      ],
      "args_I1_I0_star": [
        "ε",
        "args_I1_I0",
        "list-arg-elt"
      ],
      "args_I1_I0": [
        "list-arg-elt"
      ],
      "list-arg-elt": [],
      "return-ann_I0_opt": [
        "ε",
        "return-ann_I0"
      ],
      "return-ann_I0": [],
      "doc-string_I0_opt": [
        "ε",
        "doc-string_I0"
      ],
      "doc-string_I0": [],
      "where-clause_I0_opt": [
        "ε",
        "where-clause_I0"
      ],
      "where-clause_I0": [],
      "check-op": [],
      "data-mixins": [
        "data-mixins_I0_opt",
        "ε",
        "data-mixins_I0"
      ],
      "data-expr_I5_opt": [
        "ε",
        "data-expr_I5",
        "first-data-variant"
      ],
      "data-expr_I6_star": [
        "ε",
        "data-expr_I6",
        "data-variant"
      ],
      "data-sharing": [
        "data-sharing_I0_opt",
        "ε",
        "data-sharing_I0"
      ],
      "data-expr_I5": [
        "first-data-variant"
      ],
      "first-data-variant": [],
      "data-expr_I6": [
        "data-variant"
      ],
      "data-variant": [],
      "data-mixins_I0_opt": [
        "ε",
        "data-mixins_I0"
      ],
      "data-mixins_I0": [],
      "mixins": [
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "variant-members": [],
      "data-with": [
        "data-with_I0_opt",
        "ε",
        "data-with_I0"
      ],
      "variant-members_I0": [],
      "variant-members_I1_opt": [
        "ε",
        "variant-members_I1",
        "variant-member",
        "binding"
      ],
      "variant-members_I1": [
        "variant-member",
        "binding"
      ],
      "variant-members_I1_I0_star": [
        "ε",
        "variant-members_I1_I0",
        "list-variant-member"
      ],
      "variant-member": [
        "binding"
      ],
      "variant-members_I1_I0": [
        "list-variant-member"
      ],
      "list-variant-member": [],
      "variant-member_I0_opt": [
        "ε",
        "variant-member_I0"
      ],
      "variant-member_I0": [],
      "data-with_I0_opt": [
        "ε",
        "data-with_I0"
      ],
      "data-with_I0": [],
      "fields": [
        "field"
      ],
      "data-sharing_I0_opt": [
        "ε",
        "data-sharing_I0"
      ],
      "data-sharing_I0": [],
      "mixins_I0_star": [
        "ε",
        "mixins_I0",
        "list-mixin"
      ],
      "mixins_I0": [
        "list-mixin"
      ],
      "list-mixin": [],
      "datatype-expr_I4_opt": [
        "ε",
        "datatype-expr_I4",
        "first-datatype-variant"
      ],
      "datatype-expr_I5_star": [
        "ε",
        "datatype-expr_I5",
        "datatype-variant"
      ],
      "datatype-expr_I4": [
        "first-datatype-variant"
      ],
      "first-datatype-variant": [],
      "datatype-expr_I5": [
        "datatype-variant"
      ],
      "datatype-variant": [],
      "constructor-clause": [],
      "constructor-clause_I1": [],
      "graph-expr_I1_star": [
        "ε",
        "graph-expr_I1",
        "let-expr"
      ],
      "graph-expr_I1": [
        "let-expr"
      ],
      "binop-clause": [
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "binop-expr_I1_star": [
        "ε",
        "binop-expr_I1"
      ],
      "binop-expr_I1": [],
      "binop": [],
      "not-expr": [],
      "expr": [
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "paren-expr": [],
      "id-expr": [],
      "prim-expr": [
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "lambda-expr": [],
      "method-expr": [],
      "app-expr": [],
      "left-app-expr": [],
      "obj-expr": [],
      "list-expr": [],
      "dot-expr": [],
      "bracket-expr": [],
      "colon-expr": [],
      "colon-bracket-expr": [],
      "get-bang-expr": [],
      "update-expr": [],
      "extend-expr": [],
      "if-expr": [],
      "cases-expr": [],
      "for-expr": [],
      "try-expr": [],
      "user-block-expr": [],
      "inst-expr": [],
      "num-expr": [],
      "bool-expr": [],
      "string-expr": [],
      "lambda-expr_I2_opt": [
        "ε",
        "lambda-expr_I2",
        "args"
      ],
      "lambda-expr_I2": [
        "args"
      ],
      "app-args": [],
      "app-args_I1_opt": [
        "ε",
        "app-args_I1",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "app-args_I1": [
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "app-args_I1_I0_star": [
        "ε",
        "app-args_I1_I0",
        "app-arg-elt"
      ],
      "app-args_I1_I0": [
        "app-arg-elt"
      ],
      "app-arg-elt": [],
      "left-app-fun-expr": [
        "id-expr"
      ],
      "inst-expr_I2_star": [
        "ε",
        "inst-expr_I2",
        "inst-elt"
      ],
      "inst-expr_I2": [
        "inst-elt"
      ],
      "inst-elt": [],
      "obj-fields": [
        "obj-field"
      ],
      "obj-fields_I0_star": [
        "ε",
        "obj-fields_I0",
        "list-obj-field"
      ],
      "obj-field": [],
      "obj-fields_I2_opt": [
        "ε",
        "obj-fields_I2"
      ],
      "obj-fields_I0": [
        "list-obj-field"
      ],
      "list-obj-field": [],
      "obj-fields_I2": [],
      "key": [],
      "obj-field_A1_I2_opt": [
        "ε",
        "obj-field_A1_I2"
      ],
      "obj-field_A1_I2": [],
      "fields_I0_star": [
        "ε",
        "fields_I0",
        "list-field"
      ],
      "field": [],
      "fields_I2_opt": [
        "ε",
        "fields_I2"
      ],
      "fields_I0": [
        "list-field"
      ],
      "list-field": [],
      "fields_I2": [],
      "list-elt": [],
      "list-expr_I1_opt": [
        "ε",
        "list-expr_I1",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "list-expr_I1": [
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ],
      "list-expr_I1_I0_star": [
        "ε",
        "list-expr_I1_I0",
        "list-elt"
      ],
      "list-expr_I1_I0": [
        "list-elt"
      ],
      "if-expr_I4_star": [
        "ε",
        "if-expr_I4",
        "else-if"
      ],
      "if-expr_I5_opt": [
        "ε",
        "if-expr_I5"
      ],
      "if-expr_I4": [
        "else-if"
      ],
      "else-if": [],
      "if-expr_I5": [],
      "cases-expr_I1": [],
      "cases-expr_I6_star": [
        "ε",
        "cases-expr_I6",
        "cases-branch"
      ],
      "cases-expr_I7_opt": [
        "ε",
        "cases-expr_I7"
      ],
      "cases-expr_I6": [
        "cases-branch"
      ],
      "cases-branch": [],
      "cases-expr_I7": [],
      "cases-branch_I2_opt": [
        "ε",
        "cases-branch_I2",
        "args"
      ],
      "cases-branch_I2": [
        "args"
      ],
      "for-bind": [],
      "for-bind-elt": [],
      "for-expr_I3_opt": [
        "ε",
        "for-expr_I3",
        "for-bind"
      ],
      "for-expr_I3": [
        "for-bind"
      ],
      "for-expr_I3_I0_star": [
        "ε",
        "for-expr_I3_I0",
        "for-bind-elt"
      ],
      "for-expr_I3_I0": [
        "for-bind-elt"
      ],
      "try-expr_I3": [],
      "name-ann": [],
      "record-ann": [],
      "arrow-ann": [],
      "app-ann": [],
      "pred-ann": [],
      "dot-ann": [],
      "record-ann_A0_I1_opt": [
        "ε",
        "record-ann_A0_I1",
        "ann-field"
      ],
      "record-ann_A0_I1": [
        "ann-field"
      ],
      "record-ann_A0_I1_I0_star": [
        "ε",
        "record-ann_A0_I1_I0",
        "list-ann-field"
      ],
      "ann-field": [],
      "record-ann_A0_I1_I0": [
        "list-ann-field"
      ],
      "list-ann-field": [],
      "arrow-ann_I0": [],
      "arrow-ann_I1_opt": [
        "ε",
        "arrow-ann_I1",
        "ann",
        "name-ann",
        "record-ann",
        "arrow-ann",
        "app-ann",
        "pred-ann",
        "dot-ann"
      ],
      "arrow-ann_I1": [
        "ann",
        "name-ann",
        "record-ann",
        "arrow-ann",
        "app-ann",
        "pred-ann",
        "dot-ann"
      ],
      "arrow-ann_I1_I0_star": [
        "ε",
        "arrow-ann_I1_I0",
        "arrow-ann-elt"
      ],
      "arrow-ann_I1_I0": [
        "arrow-ann-elt"
      ],
      "arrow-ann-elt": [],
      "app-ann_I0": [
        "name-ann",
        "dot-ann"
      ],
      "app-ann_I2_star": [
        "ε",
        "app-ann_I2",
        "app-ann-elt"
      ],
      "app-ann_I2": [
        "app-ann-elt"
      ],
      "app-ann-elt": [],
      "pred-ann_I1": [],
      "START": [
        "program",
        "ε",
        "prelude",
        "prelude_I0_opt",
        "prelude_I1_star",
        "prelude_I0",
        "provide-stmt",
        "prelude_I1",
        "import-stmt",
        "block",
        "stmt",
        "block_I0_star",
        "block_I0",
        "let-expr",
        "fun-expr",
        "data-expr",
        "datatype-expr",
        "when-expr",
        "var-expr",
        "assign-expr",
        "check-test",
        "check-expr",
        "graph-expr",
        "binop-expr",
        "binop-clause",
        "not-expr",
        "expr",
        "paren-expr",
        "id-expr",
        "prim-expr",
        "lambda-expr",
        "method-expr",
        "app-expr",
        "left-app-expr",
        "obj-expr",
        "list-expr",
        "dot-expr",
        "bracket-expr",
        "colon-expr",
        "colon-bracket-expr",
        "get-bang-expr",
        "update-expr",
        "extend-expr",
        "if-expr",
        "cases-expr",
        "for-expr",
        "try-expr",
        "user-block-expr",
        "inst-expr",
        "num-expr",
        "bool-expr",
        "string-expr"
      ]
    },
    "rulesByOldId": {
      "0": {
        "name": "program",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "1": {
        "name": "end",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "END"
          }
        ]
      },
      "2": {
        "name": "end",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "SEMI"
          }
        ]
      },
      "3": {
        "name": "prelude",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I0_opt"
          },
          {
            "type": "Nonterm",
            "name": "prelude_I1_star"
          }
        ]
      },
      "4": {
        "name": "prelude_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "5": {
        "name": "prelude_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I0"
          }
        ]
      },
      "6": {
        "name": "prelude_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "provide-stmt"
          }
        ]
      },
      "7": {
        "name": "prelude_I1_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "8": {
        "name": "prelude_I1_star",
        "action": "Rule.ListCons(\"prelude_I1\", \"prelude_I1_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I1"
          },
          {
            "type": "Nonterm",
            "name": "prelude_I1_star"
          }
        ]
      },
      "9": {
        "name": "prelude_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "import-stmt"
          }
        ]
      },
      "10": {
        "name": "import-stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "IMPORT"
          },
          {
            "type": "Nonterm",
            "name": "import-stmt_I1"
          },
          {
            "type": "Token",
            "name": "AS"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "11": {
        "name": "import-stmt_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "import-name"
          }
        ]
      },
      "12": {
        "name": "import-stmt_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "import-string"
          }
        ]
      },
      "13": {
        "name": "import-name",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "14": {
        "name": "import-string",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "STRING"
          }
        ]
      },
      "15": {
        "name": "provide-stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PROVIDE"
          },
          {
            "type": "Nonterm",
            "name": "stmt"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "16": {
        "name": "provide-stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PROVIDE"
          },
          {
            "type": "Token",
            "name": "STAR"
          }
        ]
      },
      "17": {
        "name": "block",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "block_I0_star"
          }
        ]
      },
      "18": {
        "name": "block_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "19": {
        "name": "block_I0_star",
        "action": "Rule.ListCons(\"block_I0\", \"block_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "block_I0"
          },
          {
            "type": "Nonterm",
            "name": "block_I0_star"
          }
        ]
      },
      "20": {
        "name": "block_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "stmt"
          }
        ]
      },
      "21": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "let-expr"
          }
        ]
      },
      "22": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fun-expr"
          }
        ]
      },
      "23": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-expr"
          }
        ]
      },
      "24": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-expr"
          }
        ]
      },
      "25": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "when-expr"
          }
        ]
      },
      "26": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "var-expr"
          }
        ]
      },
      "27": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "assign-expr"
          }
        ]
      },
      "28": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "check-test"
          }
        ]
      },
      "29": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "check-expr"
          }
        ]
      },
      "30": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "graph-expr"
          }
        ]
      },
      "31": {
        "name": "let-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "EQUALS"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "32": {
        "name": "binding",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding_I0_opt"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "binding_I2_opt"
          }
        ]
      },
      "33": {
        "name": "binding_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "34": {
        "name": "binding_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding_I0"
          }
        ]
      },
      "35": {
        "name": "binding_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "SHADOW"
          }
        ]
      },
      "36": {
        "name": "binding_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "37": {
        "name": "binding_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding_I2"
          }
        ]
      },
      "38": {
        "name": "binding_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "COLONCOLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "39": {
        "name": "fun-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "FUN"
          },
          {
            "type": "Nonterm",
            "name": "fun-header"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "40": {
        "name": "fun-header",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          }
        ]
      },
      "41": {
        "name": "ty-params",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params_I0_opt"
          }
        ]
      },
      "42": {
        "name": "ty-params_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "43": {
        "name": "ty-params_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params_I0"
          }
        ]
      },
      "44": {
        "name": "ty-params_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LT"
          },
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1_star"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "45": {
        "name": "ty-params_I0_I1_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "46": {
        "name": "ty-params_I0_I1_star",
        "action": "Rule.ListCons(\"ty-params_I0_I1\", \"ty-params_I0_I1_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1"
          },
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1_star"
          }
        ]
      },
      "47": {
        "name": "ty-params_I0_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-ty-param"
          }
        ]
      },
      "48": {
        "name": "list-ty-param",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "49": {
        "name": "args",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I0"
          },
          {
            "type": "Nonterm",
            "name": "args_I1_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "50": {
        "name": "args_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "51": {
        "name": "args_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "52": {
        "name": "args_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "53": {
        "name": "args_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I1"
          }
        ]
      },
      "54": {
        "name": "args_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          }
        ]
      },
      "55": {
        "name": "args_I1_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "56": {
        "name": "args_I1_I0_star",
        "action": "Rule.ListCons(\"args_I1_I0\", \"args_I1_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "args_I1_I0_star"
          }
        ]
      },
      "57": {
        "name": "args_I1_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-arg-elt"
          }
        ]
      },
      "58": {
        "name": "list-arg-elt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "59": {
        "name": "return-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "return-ann_I0_opt"
          }
        ]
      },
      "60": {
        "name": "return-ann_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "61": {
        "name": "return-ann_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "return-ann_I0"
          }
        ]
      },
      "62": {
        "name": "return-ann_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "THINARROW"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "63": {
        "name": "doc-string",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "doc-string_I0_opt"
          }
        ]
      },
      "64": {
        "name": "doc-string_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "65": {
        "name": "doc-string_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "doc-string_I0"
          }
        ]
      },
      "66": {
        "name": "doc-string_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "DOC"
          },
          {
            "type": "Token",
            "name": "STRING"
          }
        ]
      },
      "67": {
        "name": "where-clause",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "where-clause_I0_opt"
          }
        ]
      },
      "68": {
        "name": "where-clause_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "69": {
        "name": "where-clause_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "where-clause_I0"
          }
        ]
      },
      "70": {
        "name": "where-clause_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "WHERE"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "71": {
        "name": "check-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "CHECK"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "72": {
        "name": "check-test",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Nonterm",
            "name": "check-op"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "73": {
        "name": "check-test",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "74": {
        "name": "data-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "DATA"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Nonterm",
            "name": "data-mixins"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "data-expr_I5_opt"
          },
          {
            "type": "Nonterm",
            "name": "data-expr_I6_star"
          },
          {
            "type": "Nonterm",
            "name": "data-sharing"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "75": {
        "name": "data-expr_I5_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "76": {
        "name": "data-expr_I5_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-expr_I5"
          }
        ]
      },
      "77": {
        "name": "data-expr_I5",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "first-data-variant"
          }
        ]
      },
      "78": {
        "name": "data-expr_I6_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "79": {
        "name": "data-expr_I6_star",
        "action": "Rule.ListCons(\"data-expr_I6\", \"data-expr_I6_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-expr_I6"
          },
          {
            "type": "Nonterm",
            "name": "data-expr_I6_star"
          }
        ]
      },
      "80": {
        "name": "data-expr_I6",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-variant"
          }
        ]
      },
      "81": {
        "name": "data-mixins",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-mixins_I0_opt"
          }
        ]
      },
      "82": {
        "name": "data-mixins_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "83": {
        "name": "data-mixins_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-mixins_I0"
          }
        ]
      },
      "84": {
        "name": "data-mixins_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "DERIVING"
          },
          {
            "type": "Nonterm",
            "name": "mixins"
          }
        ]
      },
      "85": {
        "name": "first-data-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "86": {
        "name": "first-data-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "87": {
        "name": "data-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "88": {
        "name": "data-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "89": {
        "name": "variant-members",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I0"
          },
          {
            "type": "Nonterm",
            "name": "variant-members_I1_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "90": {
        "name": "variant-members_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "91": {
        "name": "variant-members_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "92": {
        "name": "variant-members_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "93": {
        "name": "variant-members_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I1"
          }
        ]
      },
      "94": {
        "name": "variant-members_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "variant-member"
          }
        ]
      },
      "95": {
        "name": "variant-members_I1_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "96": {
        "name": "variant-members_I1_I0_star",
        "action": "Rule.ListCons(\"variant-members_I1_I0\", \"variant-members_I1_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0_star"
          }
        ]
      },
      "97": {
        "name": "variant-members_I1_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-variant-member"
          }
        ]
      },
      "98": {
        "name": "list-variant-member",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-member"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "99": {
        "name": "variant-member",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-member_I0_opt"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          }
        ]
      },
      "100": {
        "name": "variant-member_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "101": {
        "name": "variant-member_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-member_I0"
          }
        ]
      },
      "102": {
        "name": "variant-member_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "MUTABLE"
          }
        ]
      },
      "103": {
        "name": "variant-member_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "CYCLIC"
          }
        ]
      },
      "104": {
        "name": "data-with",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-with_I0_opt"
          }
        ]
      },
      "105": {
        "name": "data-with_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "106": {
        "name": "data-with_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-with_I0"
          }
        ]
      },
      "107": {
        "name": "data-with_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "WITH"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          }
        ]
      },
      "108": {
        "name": "data-sharing",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-sharing_I0_opt"
          }
        ]
      },
      "109": {
        "name": "data-sharing_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "110": {
        "name": "data-sharing_I0_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-sharing_I0"
          }
        ]
      },
      "111": {
        "name": "data-sharing_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "SHARING"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          }
        ]
      },
      "112": {
        "name": "mixins",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "mixins_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "113": {
        "name": "mixins_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "114": {
        "name": "mixins_I0_star",
        "action": "Rule.ListCons(\"mixins_I0\", \"mixins_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "mixins_I0"
          },
          {
            "type": "Nonterm",
            "name": "mixins_I0_star"
          }
        ]
      },
      "115": {
        "name": "mixins_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-mixin"
          }
        ]
      },
      "116": {
        "name": "list-mixin",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "117": {
        "name": "datatype-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "DATATYPE"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "datatype-expr_I4_opt"
          },
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5_star"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "118": {
        "name": "datatype-expr_I4_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "119": {
        "name": "datatype-expr_I4_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-expr_I4"
          }
        ]
      },
      "120": {
        "name": "datatype-expr_I4",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "first-datatype-variant"
          }
        ]
      },
      "121": {
        "name": "datatype-expr_I5_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "122": {
        "name": "datatype-expr_I5_star",
        "action": "Rule.ListCons(\"datatype-expr_I5\", \"datatype-expr_I5_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5"
          },
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5_star"
          }
        ]
      },
      "123": {
        "name": "datatype-expr_I5",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-variant"
          }
        ]
      },
      "124": {
        "name": "first-datatype-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "125": {
        "name": "first-datatype-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "126": {
        "name": "datatype-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "127": {
        "name": "datatype-variant",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "128": {
        "name": "constructor-clause",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "WITHCONSTRUCTOR"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause_I1"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "129": {
        "name": "constructor-clause_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "130": {
        "name": "constructor-clause_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "131": {
        "name": "var-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "VAR"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "EQUALS"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "132": {
        "name": "assign-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COLONEQUALS"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "133": {
        "name": "graph-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "GRAPH"
          },
          {
            "type": "Nonterm",
            "name": "graph-expr_I1_star"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "134": {
        "name": "graph-expr_I1_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "135": {
        "name": "graph-expr_I1_star",
        "action": "Rule.ListCons(\"graph-expr_I1\", \"graph-expr_I1_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "graph-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "graph-expr_I1_star"
          }
        ]
      },
      "136": {
        "name": "graph-expr_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "let-expr"
          }
        ]
      },
      "137": {
        "name": "when-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "WHEN"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "138": {
        "name": "binop-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-clause"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr_I1_star"
          }
        ]
      },
      "139": {
        "name": "binop-expr_I1_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "140": {
        "name": "binop-expr_I1_star",
        "action": "Rule.ListCons(\"binop-expr_I1\", \"binop-expr_I1_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr_I1_star"
          }
        ]
      },
      "141": {
        "name": "binop-expr_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop"
          },
          {
            "type": "Nonterm",
            "name": "binop-clause"
          }
        ]
      },
      "142": {
        "name": "binop-clause",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "not-expr"
          }
        ]
      },
      "143": {
        "name": "binop-clause",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          }
        ]
      },
      "144": {
        "name": "not-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NOT"
          },
          {
            "type": "Nonterm",
            "name": "expr"
          }
        ]
      },
      "145": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PLUS"
          }
        ]
      },
      "146": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "DASH"
          }
        ]
      },
      "147": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "STAR"
          }
        ]
      },
      "148": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "SLASH"
          }
        ]
      },
      "149": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LEQ"
          }
        ]
      },
      "150": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "GEQ"
          }
        ]
      },
      "151": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "EQUALEQUAL"
          }
        ]
      },
      "152": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NEQ"
          }
        ]
      },
      "153": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LT"
          }
        ]
      },
      "154": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "155": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "AND"
          }
        ]
      },
      "156": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "OR"
          }
        ]
      },
      "157": {
        "name": "check-op",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "IS"
          }
        ]
      },
      "158": {
        "name": "check-op",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "RAISES"
          }
        ]
      },
      "159": {
        "name": "check-op",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "SATISFIES"
          }
        ]
      },
      "160": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "paren-expr"
          }
        ]
      },
      "161": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "id-expr"
          }
        ]
      },
      "162": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prim-expr"
          }
        ]
      },
      "163": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "lambda-expr"
          }
        ]
      },
      "164": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "method-expr"
          }
        ]
      },
      "165": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-expr"
          }
        ]
      },
      "166": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "left-app-expr"
          }
        ]
      },
      "167": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-expr"
          }
        ]
      },
      "168": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr"
          }
        ]
      },
      "169": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "dot-expr"
          }
        ]
      },
      "170": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "bracket-expr"
          }
        ]
      },
      "171": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "colon-expr"
          }
        ]
      },
      "172": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "colon-bracket-expr"
          }
        ]
      },
      "173": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "get-bang-expr"
          }
        ]
      },
      "174": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "update-expr"
          }
        ]
      },
      "175": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "extend-expr"
          }
        ]
      },
      "176": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "if-expr"
          }
        ]
      },
      "177": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-expr"
          }
        ]
      },
      "178": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr"
          }
        ]
      },
      "179": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "try-expr"
          }
        ]
      },
      "180": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "user-block-expr"
          }
        ]
      },
      "181": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "inst-expr"
          }
        ]
      },
      "182": {
        "name": "paren-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "183": {
        "name": "id-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "184": {
        "name": "prim-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "num-expr"
          }
        ]
      },
      "185": {
        "name": "prim-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "bool-expr"
          }
        ]
      },
      "186": {
        "name": "prim-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "string-expr"
          }
        ]
      },
      "187": {
        "name": "num-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NUMBER"
          }
        ]
      },
      "188": {
        "name": "num-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "DASH"
          },
          {
            "type": "Token",
            "name": "NUMBER"
          }
        ]
      },
      "189": {
        "name": "bool-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "TRUE"
          }
        ]
      },
      "190": {
        "name": "bool-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "FALSE"
          }
        ]
      },
      "191": {
        "name": "string-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "STRING"
          }
        ]
      },
      "192": {
        "name": "lambda-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "FUN"
          },
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Nonterm",
            "name": "lambda-expr_I2_opt"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "193": {
        "name": "lambda-expr_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "194": {
        "name": "lambda-expr_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "lambda-expr_I2"
          }
        ]
      },
      "195": {
        "name": "lambda-expr_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args"
          }
        ]
      },
      "196": {
        "name": "method-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "METHOD"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "197": {
        "name": "app-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Nonterm",
            "name": "app-args"
          }
        ]
      },
      "198": {
        "name": "app-args",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          },
          {
            "type": "Nonterm",
            "name": "app-args_I1_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "199": {
        "name": "app-args_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "200": {
        "name": "app-args_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-args_I1"
          }
        ]
      },
      "201": {
        "name": "app-args_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "202": {
        "name": "app-args_I1_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "203": {
        "name": "app-args_I1_I0_star",
        "action": "Rule.ListCons(\"app-args_I1_I0\", \"app-args_I1_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0_star"
          }
        ]
      },
      "204": {
        "name": "app-args_I1_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-arg-elt"
          }
        ]
      },
      "205": {
        "name": "app-arg-elt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "206": {
        "name": "left-app-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "CARET"
          },
          {
            "type": "Nonterm",
            "name": "left-app-fun-expr"
          },
          {
            "type": "Nonterm",
            "name": "app-args"
          }
        ]
      },
      "207": {
        "name": "left-app-fun-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "id-expr"
          }
        ]
      },
      "208": {
        "name": "left-app-fun-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "id-expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "209": {
        "name": "inst-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "LT"
          },
          {
            "type": "Nonterm",
            "name": "inst-expr_I2_star"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "210": {
        "name": "inst-expr_I2_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "211": {
        "name": "inst-expr_I2_star",
        "action": "Rule.ListCons(\"inst-expr_I2\", \"inst-expr_I2_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "inst-expr_I2"
          },
          {
            "type": "Nonterm",
            "name": "inst-expr_I2_star"
          }
        ]
      },
      "212": {
        "name": "inst-expr_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "inst-elt"
          }
        ]
      },
      "213": {
        "name": "inst-elt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "214": {
        "name": "obj-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "215": {
        "name": "obj-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "216": {
        "name": "obj-fields",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "obj-field"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields_I2_opt"
          }
        ]
      },
      "217": {
        "name": "obj-fields_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "218": {
        "name": "obj-fields_I0_star",
        "action": "Rule.ListCons(\"obj-fields_I0\", \"obj-fields_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I0"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields_I0_star"
          }
        ]
      },
      "219": {
        "name": "obj-fields_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-obj-field"
          }
        ]
      },
      "220": {
        "name": "obj-fields_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "221": {
        "name": "obj-fields_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I2"
          }
        ]
      },
      "222": {
        "name": "obj-fields_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "223": {
        "name": "list-obj-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-field"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "224": {
        "name": "obj-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "225": {
        "name": "obj-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "MUTABLE"
          },
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Nonterm",
            "name": "obj-field_A1_I2_opt"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "226": {
        "name": "obj-field_A1_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "227": {
        "name": "obj-field_A1_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-field_A1_I2"
          }
        ]
      },
      "228": {
        "name": "obj-field_A1_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "COLONCOLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "229": {
        "name": "obj-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "230": {
        "name": "fields",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "field"
          },
          {
            "type": "Nonterm",
            "name": "fields_I2_opt"
          }
        ]
      },
      "231": {
        "name": "fields_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "232": {
        "name": "fields_I0_star",
        "action": "Rule.ListCons(\"fields_I0\", \"fields_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I0"
          },
          {
            "type": "Nonterm",
            "name": "fields_I0_star"
          }
        ]
      },
      "233": {
        "name": "fields_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-field"
          }
        ]
      },
      "234": {
        "name": "fields_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "235": {
        "name": "fields_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I2"
          }
        ]
      },
      "236": {
        "name": "fields_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "237": {
        "name": "list-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "field"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "238": {
        "name": "field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "239": {
        "name": "field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "240": {
        "name": "key",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "241": {
        "name": "key",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "242": {
        "name": "list-elt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "243": {
        "name": "list-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "list-expr_I1_opt"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "244": {
        "name": "list-expr_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "245": {
        "name": "list-expr_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr_I1"
          }
        ]
      },
      "246": {
        "name": "list-expr_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "247": {
        "name": "list-expr_I1_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "248": {
        "name": "list-expr_I1_I0_star",
        "action": "Rule.ListCons(\"list-expr_I1_I0\", \"list-expr_I1_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0_star"
          }
        ]
      },
      "249": {
        "name": "list-expr_I1_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-elt"
          }
        ]
      },
      "250": {
        "name": "dot-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "251": {
        "name": "bracket-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "252": {
        "name": "get-bang-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "BANG"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "253": {
        "name": "colon-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "254": {
        "name": "colon-bracket-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "255": {
        "name": "extend-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "256": {
        "name": "update-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "BANG"
          },
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "257": {
        "name": "if-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "IF"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "if-expr_I4_star"
          },
          {
            "type": "Nonterm",
            "name": "if-expr_I5_opt"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "258": {
        "name": "if-expr_I4_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "259": {
        "name": "if-expr_I4_star",
        "action": "Rule.ListCons(\"if-expr_I4\", \"if-expr_I4_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "if-expr_I4"
          },
          {
            "type": "Nonterm",
            "name": "if-expr_I4_star"
          }
        ]
      },
      "260": {
        "name": "if-expr_I4",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "else-if"
          }
        ]
      },
      "261": {
        "name": "if-expr_I5_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "262": {
        "name": "if-expr_I5_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "if-expr_I5"
          }
        ]
      },
      "263": {
        "name": "if-expr_I5",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "ELSE"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "264": {
        "name": "else-if",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "ELSEIF"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "265": {
        "name": "cases-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "CASES"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I6_star"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I7_opt"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "266": {
        "name": "cases-expr_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "267": {
        "name": "cases-expr_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "268": {
        "name": "cases-expr_I6_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "269": {
        "name": "cases-expr_I6_star",
        "action": "Rule.ListCons(\"cases-expr_I6\", \"cases-expr_I6_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-expr_I6"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I6_star"
          }
        ]
      },
      "270": {
        "name": "cases-expr_I6",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-branch"
          }
        ]
      },
      "271": {
        "name": "cases-expr_I7_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "272": {
        "name": "cases-expr_I7_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-expr_I7"
          }
        ]
      },
      "273": {
        "name": "cases-expr_I7",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "ELSE"
          },
          {
            "type": "Token",
            "name": "THICKARROW"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "274": {
        "name": "cases-branch",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "cases-branch_I2_opt"
          },
          {
            "type": "Token",
            "name": "THICKARROW"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "275": {
        "name": "cases-branch_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "276": {
        "name": "cases-branch_I2_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-branch_I2"
          }
        ]
      },
      "277": {
        "name": "cases-branch_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args"
          }
        ]
      },
      "278": {
        "name": "for-bind",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "FROM"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "279": {
        "name": "for-bind-elt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-bind"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "280": {
        "name": "for-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "FOR"
          },
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          },
          {
            "type": "Nonterm",
            "name": "for-expr_I3_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "281": {
        "name": "for-expr_I3_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "282": {
        "name": "for-expr_I3_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr_I3"
          }
        ]
      },
      "283": {
        "name": "for-expr_I3",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "for-bind"
          }
        ]
      },
      "284": {
        "name": "for-expr_I3_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "285": {
        "name": "for-expr_I3_I0_star",
        "action": "Rule.ListCons(\"for-expr_I3_I0\", \"for-expr_I3_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0"
          },
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0_star"
          }
        ]
      },
      "286": {
        "name": "for-expr_I3_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-bind-elt"
          }
        ]
      },
      "287": {
        "name": "try-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "TRY"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Token",
            "name": "EXCEPT"
          },
          {
            "type": "Nonterm",
            "name": "try-expr_I3"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "288": {
        "name": "try-expr_I3",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "289": {
        "name": "try-expr_I3",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "290": {
        "name": "user-block-expr",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "BLOCK"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "291": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "name-ann"
          }
        ]
      },
      "292": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann"
          }
        ]
      },
      "293": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann"
          }
        ]
      },
      "294": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann"
          }
        ]
      },
      "295": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "pred-ann"
          }
        ]
      },
      "296": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "dot-ann"
          }
        ]
      },
      "297": {
        "name": "name-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "298": {
        "name": "record-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_opt"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "299": {
        "name": "record-ann_A0_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "300": {
        "name": "record-ann_A0_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1"
          }
        ]
      },
      "301": {
        "name": "record-ann_A0_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "ann-field"
          }
        ]
      },
      "302": {
        "name": "record-ann_A0_I1_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "303": {
        "name": "record-ann_A0_I1_I0_star",
        "action": "Rule.ListCons(\"record-ann_A0_I1_I0\", \"record-ann_A0_I1_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0_star"
          }
        ]
      },
      "304": {
        "name": "record-ann_A0_I1_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-ann-field"
          }
        ]
      },
      "305": {
        "name": "record-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "306": {
        "name": "list-ann-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann-field"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "307": {
        "name": "ann-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "308": {
        "name": "ann-field",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COLONCOLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "309": {
        "name": "arrow-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I0"
          },
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_opt"
          },
          {
            "type": "Token",
            "name": "THINARROW"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "310": {
        "name": "arrow-ann_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "311": {
        "name": "arrow-ann_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "312": {
        "name": "arrow-ann_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "313": {
        "name": "arrow-ann_I1_opt",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1"
          }
        ]
      },
      "314": {
        "name": "arrow-ann_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "315": {
        "name": "arrow-ann_I1_I0_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "316": {
        "name": "arrow-ann_I1_I0_star",
        "action": "Rule.ListCons(\"arrow-ann_I1_I0\", \"arrow-ann_I1_I0_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0_star"
          }
        ]
      },
      "317": {
        "name": "arrow-ann_I1_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann-elt"
          }
        ]
      },
      "318": {
        "name": "arrow-ann-elt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "319": {
        "name": "app-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann_I0"
          },
          {
            "type": "Token",
            "name": "LT"
          },
          {
            "type": "Nonterm",
            "name": "app-ann_I2_star"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "320": {
        "name": "app-ann_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "name-ann"
          }
        ]
      },
      "321": {
        "name": "app-ann_I0",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "dot-ann"
          }
        ]
      },
      "322": {
        "name": "app-ann_I2_star",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": []
      },
      "323": {
        "name": "app-ann_I2_star",
        "action": "Rule.ListCons(\"app-ann_I2\", \"app-ann_I2_star\", true)",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann_I2"
          },
          {
            "type": "Nonterm",
            "name": "app-ann_I2_star"
          }
        ]
      },
      "324": {
        "name": "app-ann_I2",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann-elt"
          }
        ]
      },
      "325": {
        "name": "app-ann-elt",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "326": {
        "name": "pred-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Nonterm",
            "name": "pred-ann_I1"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "327": {
        "name": "pred-ann_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "328": {
        "name": "pred-ann_I1",
        "action": "Rule.Inline",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "329": {
        "name": "dot-ann",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "330": {
        "name": "START",
        "action": "Rule.defaultAction",
        "position": 0,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "program"
          }
        ]
      },
      "333": {
        "name": "program",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "334": {
        "name": "prelude",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I0_opt"
          },
          {
            "type": "Nonterm",
            "name": "prelude_I1_star"
          }
        ]
      },
      "335": {
        "name": "prelude_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I0"
          }
        ]
      },
      "336": {
        "name": "prelude_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "provide-stmt"
          }
        ]
      },
      "337": {
        "name": "prelude_I1_star",
        "action": "Rule.ListCons(\"prelude_I1\", \"prelude_I1_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I1"
          },
          {
            "type": "Nonterm",
            "name": "prelude_I1_star"
          }
        ]
      },
      "338": {
        "name": "prelude_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "import-stmt"
          }
        ]
      },
      "341": {
        "name": "id-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "342": {
        "name": "string-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "STRING"
          }
        ]
      },
      "345": {
        "name": "block_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "stmt"
          }
        ]
      },
      "346": {
        "name": "block",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "block_I0_star"
          }
        ]
      },
      "347": {
        "name": "block_I0_star",
        "action": "Rule.ListCons(\"block_I0\", \"block_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "block_I0"
          },
          {
            "type": "Nonterm",
            "name": "block_I0_star"
          }
        ]
      },
      "348": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "let-expr"
          }
        ]
      },
      "349": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fun-expr"
          }
        ]
      },
      "350": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-expr"
          }
        ]
      },
      "351": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-expr"
          }
        ]
      },
      "352": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "when-expr"
          }
        ]
      },
      "353": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "var-expr"
          }
        ]
      },
      "354": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "assign-expr"
          }
        ]
      },
      "355": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "check-test"
          }
        ]
      },
      "356": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "check-expr"
          }
        ]
      },
      "357": {
        "name": "stmt",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "graph-expr"
          }
        ]
      },
      "360": {
        "name": "check-test",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "362": {
        "name": "binding_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding_I0"
          }
        ]
      },
      "363": {
        "name": "binding_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "SHADOW"
          }
        ]
      },
      "373": {
        "name": "binop-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-clause"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr_I1_star"
          }
        ]
      },
      "374": {
        "name": "binop-clause",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "not-expr"
          }
        ]
      },
      "375": {
        "name": "binop-clause",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          }
        ]
      },
      "388": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "paren-expr"
          }
        ]
      },
      "389": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "id-expr"
          }
        ]
      },
      "390": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prim-expr"
          }
        ]
      },
      "391": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "lambda-expr"
          }
        ]
      },
      "392": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "method-expr"
          }
        ]
      },
      "393": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-expr"
          }
        ]
      },
      "394": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "left-app-expr"
          }
        ]
      },
      "395": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-expr"
          }
        ]
      },
      "396": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr"
          }
        ]
      },
      "397": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "dot-expr"
          }
        ]
      },
      "398": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "bracket-expr"
          }
        ]
      },
      "399": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "colon-expr"
          }
        ]
      },
      "400": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "colon-bracket-expr"
          }
        ]
      },
      "401": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "get-bang-expr"
          }
        ]
      },
      "402": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "update-expr"
          }
        ]
      },
      "403": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "extend-expr"
          }
        ]
      },
      "404": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "if-expr"
          }
        ]
      },
      "405": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-expr"
          }
        ]
      },
      "406": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr"
          }
        ]
      },
      "407": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "try-expr"
          }
        ]
      },
      "408": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "user-block-expr"
          }
        ]
      },
      "409": {
        "name": "expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "inst-expr"
          }
        ]
      },
      "410": {
        "name": "prim-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "num-expr"
          }
        ]
      },
      "411": {
        "name": "prim-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "bool-expr"
          }
        ]
      },
      "412": {
        "name": "prim-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "string-expr"
          }
        ]
      },
      "413": {
        "name": "num-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "NUMBER"
          }
        ]
      },
      "414": {
        "name": "bool-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "TRUE"
          }
        ]
      },
      "415": {
        "name": "bool-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "FALSE"
          }
        ]
      },
      "425": {
        "name": "program",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "426": {
        "name": "prelude",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I0_opt"
          },
          {
            "type": "Nonterm",
            "name": "prelude_I1_star"
          }
        ]
      },
      "427": {
        "name": "prelude_I1_star",
        "action": "Rule.ListCons(\"prelude_I1\", \"prelude_I1_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "prelude_I1"
          },
          {
            "type": "Nonterm",
            "name": "prelude_I1_star"
          }
        ]
      },
      "429": {
        "name": "import-name",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "430": {
        "name": "import-stmt_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "import-name"
          }
        ]
      },
      "431": {
        "name": "import-stmt_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "import-string"
          }
        ]
      },
      "432": {
        "name": "import-string",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "STRING"
          }
        ]
      },
      "435": {
        "name": "provide-stmt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "PROVIDE"
          },
          {
            "type": "Token",
            "name": "STAR"
          }
        ]
      },
      "436": {
        "name": "block_I0_star",
        "action": "Rule.ListCons(\"block_I0\", \"block_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "block_I0"
          },
          {
            "type": "Nonterm",
            "name": "block_I0_star"
          }
        ]
      },
      "439": {
        "name": "check-op",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "IS"
          }
        ]
      },
      "440": {
        "name": "check-op",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "RAISES"
          }
        ]
      },
      "441": {
        "name": "check-op",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "SATISFIES"
          }
        ]
      },
      "442": {
        "name": "binding",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding_I0_opt"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "binding_I2_opt"
          }
        ]
      },
      "446": {
        "name": "ty-params",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params_I0_opt"
          }
        ]
      },
      "447": {
        "name": "ty-params_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params_I0"
          }
        ]
      },
      "454": {
        "name": "graph-expr_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "let-expr"
          }
        ]
      },
      "456": {
        "name": "graph-expr_I1_star",
        "action": "Rule.ListCons(\"graph-expr_I1\", \"graph-expr_I1_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "graph-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "graph-expr_I1_star"
          }
        ]
      },
      "458": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "STAR"
          }
        ]
      },
      "459": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "LT"
          }
        ]
      },
      "460": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "461": {
        "name": "binop-expr",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-clause"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr_I1_star"
          }
        ]
      },
      "462": {
        "name": "binop-expr_I1_star",
        "action": "Rule.ListCons(\"binop-expr_I1\", \"binop-expr_I1_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr_I1_star"
          }
        ]
      },
      "464": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PLUS"
          }
        ]
      },
      "465": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "DASH"
          }
        ]
      },
      "466": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "SLASH"
          }
        ]
      },
      "467": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "LEQ"
          }
        ]
      },
      "468": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "GEQ"
          }
        ]
      },
      "469": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "EQUALEQUAL"
          }
        ]
      },
      "470": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "NEQ"
          }
        ]
      },
      "471": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "AND"
          }
        ]
      },
      "472": {
        "name": "binop",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "OR"
          }
        ]
      },
      "477": {
        "name": "app-expr",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Nonterm",
            "name": "app-args"
          }
        ]
      },
      "484": {
        "name": "not-expr",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "NOT"
          },
          {
            "type": "Nonterm",
            "name": "expr"
          }
        ]
      },
      "485": {
        "name": "num-expr",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "DASH"
          },
          {
            "type": "Token",
            "name": "NUMBER"
          }
        ]
      },
      "488": {
        "name": "args_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "489": {
        "name": "args_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "490": {
        "name": "key",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "493": {
        "name": "obj-expr",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "496": {
        "name": "obj-fields_I0_star",
        "action": "Rule.ListCons(\"obj-fields_I0\", \"obj-fields_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I0"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields_I0_star"
          }
        ]
      },
      "497": {
        "name": "obj-fields_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-obj-field"
          }
        ]
      },
      "502": {
        "name": "list-expr_I1_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-elt"
          }
        ]
      },
      "504": {
        "name": "list-expr_I1_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr_I1"
          }
        ]
      },
      "506": {
        "name": "list-expr_I1_I0_star",
        "action": "Rule.ListCons(\"list-expr_I1_I0\", \"list-expr_I1_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0_star"
          }
        ]
      },
      "508": {
        "name": "cases-expr_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "509": {
        "name": "cases-expr_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "515": {
        "name": "assign-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COLONEQUALS"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "516": {
        "name": "provide-stmt",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "PROVIDE"
          },
          {
            "type": "Nonterm",
            "name": "stmt"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "517": {
        "name": "end",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "END"
          }
        ]
      },
      "518": {
        "name": "end",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "SEMI"
          }
        ]
      },
      "519": {
        "name": "let-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "EQUALS"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "520": {
        "name": "check-test",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Nonterm",
            "name": "check-op"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "521": {
        "name": "binding",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding_I0_opt"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "binding_I2_opt"
          }
        ]
      },
      "522": {
        "name": "binding_I2_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding_I2"
          }
        ]
      },
      "526": {
        "name": "lambda-expr_I2",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args"
          }
        ]
      },
      "528": {
        "name": "lambda-expr_I2_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "lambda-expr_I2"
          }
        ]
      },
      "531": {
        "name": "ty-params_I0_I1_star",
        "action": "Rule.ListCons(\"ty-params_I0_I1\", \"ty-params_I0_I1_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1"
          },
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1_star"
          }
        ]
      },
      "532": {
        "name": "ty-params_I0_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-ty-param"
          }
        ]
      },
      "533": {
        "name": "paren-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "534": {
        "name": "check-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "CHECK"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "538": {
        "name": "graph-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "GRAPH"
          },
          {
            "type": "Nonterm",
            "name": "graph-expr_I1_star"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "539": {
        "name": "graph-expr_I1_star",
        "action": "Rule.ListCons(\"graph-expr_I1\", \"graph-expr_I1_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "graph-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "graph-expr_I1_star"
          }
        ]
      },
      "541": {
        "name": "binop-expr_I1_star",
        "action": "Rule.ListCons(\"binop-expr_I1\", \"binop-expr_I1_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr_I1_star"
          }
        ]
      },
      "542": {
        "name": "binop-expr_I1",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop"
          },
          {
            "type": "Nonterm",
            "name": "binop-clause"
          }
        ]
      },
      "543": {
        "name": "colon-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "545": {
        "name": "name-ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "549": {
        "name": "arrow-ann_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "550": {
        "name": "arrow-ann_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "552": {
        "name": "inst-expr_I2_star",
        "action": "Rule.ListCons(\"inst-expr_I2\", \"inst-expr_I2_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "inst-expr_I2"
          },
          {
            "type": "Nonterm",
            "name": "inst-expr_I2_star"
          }
        ]
      },
      "553": {
        "name": "inst-expr_I2",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "inst-elt"
          }
        ]
      },
      "556": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "name-ann"
          }
        ]
      },
      "557": {
        "name": "app-ann_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "name-ann"
          }
        ]
      },
      "558": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann"
          }
        ]
      },
      "559": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann"
          }
        ]
      },
      "560": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann"
          }
        ]
      },
      "561": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "pred-ann"
          }
        ]
      },
      "562": {
        "name": "ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "dot-ann"
          }
        ]
      },
      "563": {
        "name": "app-ann_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "dot-ann"
          }
        ]
      },
      "568": {
        "name": "app-args_I1_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-args_I1"
          }
        ]
      },
      "570": {
        "name": "app-args_I1_I0_star",
        "action": "Rule.ListCons(\"app-args_I1_I0\", \"app-args_I1_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0_star"
          }
        ]
      },
      "571": {
        "name": "app-args_I1_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-arg-elt"
          }
        ]
      },
      "572": {
        "name": "left-app-fun-expr",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "id-expr"
          }
        ]
      },
      "575": {
        "name": "dot-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "578": {
        "name": "get-bang-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "BANG"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "581": {
        "name": "return-ann",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "return-ann_I0_opt"
          }
        ]
      },
      "582": {
        "name": "return-ann_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "return-ann_I0"
          }
        ]
      },
      "586": {
        "name": "args_I1_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I1"
          }
        ]
      },
      "588": {
        "name": "args_I1_I0_star",
        "action": "Rule.ListCons(\"args_I1_I0\", \"args_I1_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "args_I1_I0_star"
          }
        ]
      },
      "589": {
        "name": "args_I1_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-arg-elt"
          }
        ]
      },
      "591": {
        "name": "obj-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "592": {
        "name": "obj-fields",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "obj-field"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields_I2_opt"
          }
        ]
      },
      "593": {
        "name": "list-obj-field",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-field"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "594": {
        "name": "obj-fields_I0_star",
        "action": "Rule.ListCons(\"obj-fields_I0\", \"obj-fields_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I0"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields_I0_star"
          }
        ]
      },
      "598": {
        "name": "list-elt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "599": {
        "name": "list-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "list-expr_I1_opt"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "600": {
        "name": "list-expr_I1",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "601": {
        "name": "list-expr_I1_I0_star",
        "action": "Rule.ListCons(\"list-expr_I1_I0\", \"list-expr_I1_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "list-expr_I1_I0_star"
          }
        ]
      },
      "606": {
        "name": "user-block-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "BLOCK"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "607": {
        "name": "import-stmt",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "IMPORT"
          },
          {
            "type": "Nonterm",
            "name": "import-stmt_I1"
          },
          {
            "type": "Token",
            "name": "AS"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "608": {
        "name": "binding_I2",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "COLONCOLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "610": {
        "name": "doc-string",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "doc-string_I0_opt"
          }
        ]
      },
      "611": {
        "name": "doc-string_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "doc-string_I0"
          }
        ]
      },
      "613": {
        "name": "fun-header",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          }
        ]
      },
      "615": {
        "name": "list-ty-param",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "617": {
        "name": "ty-params_I0_I1_star",
        "action": "Rule.ListCons(\"ty-params_I0_I1\", \"ty-params_I0_I1_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1"
          },
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1_star"
          }
        ]
      },
      "619": {
        "name": "data-mixins",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-mixins_I0_opt"
          }
        ]
      },
      "620": {
        "name": "data-mixins_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-mixins_I0"
          }
        ]
      },
      "623": {
        "name": "var-expr",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "VAR"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "EQUALS"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "627": {
        "name": "inst-elt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "628": {
        "name": "pred-ann_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "629": {
        "name": "pred-ann_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "632": {
        "name": "inst-expr_I2_star",
        "action": "Rule.ListCons(\"inst-expr_I2\", \"inst-expr_I2_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "inst-expr_I2"
          },
          {
            "type": "Nonterm",
            "name": "inst-expr_I2_star"
          }
        ]
      },
      "635": {
        "name": "record-ann",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "637": {
        "name": "record-ann_A0_I1_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1"
          }
        ]
      },
      "640": {
        "name": "record-ann_A0_I1_I0_star",
        "action": "Rule.ListCons(\"record-ann_A0_I1_I0\", \"record-ann_A0_I1_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0_star"
          }
        ]
      },
      "641": {
        "name": "record-ann_A0_I1_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-ann-field"
          }
        ]
      },
      "644": {
        "name": "arrow-ann_I1_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1"
          }
        ]
      },
      "646": {
        "name": "arrow-ann_I1_I0_star",
        "action": "Rule.ListCons(\"arrow-ann_I1_I0\", \"arrow-ann_I1_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0_star"
          }
        ]
      },
      "647": {
        "name": "arrow-ann_I1_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann-elt"
          }
        ]
      },
      "649": {
        "name": "app-arg-elt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "650": {
        "name": "app-args",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          },
          {
            "type": "Nonterm",
            "name": "app-args_I1_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "651": {
        "name": "app-args_I1",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "652": {
        "name": "app-args_I1_I0_star",
        "action": "Rule.ListCons(\"app-args_I1_I0\", \"app-args_I1_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "app-args_I1_I0_star"
          }
        ]
      },
      "654": {
        "name": "left-app-expr",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "CARET"
          },
          {
            "type": "Nonterm",
            "name": "left-app-fun-expr"
          },
          {
            "type": "Nonterm",
            "name": "app-args"
          }
        ]
      },
      "660": {
        "name": "fields_I0_star",
        "action": "Rule.ListCons(\"fields_I0\", \"fields_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I0"
          },
          {
            "type": "Nonterm",
            "name": "fields_I0_star"
          }
        ]
      },
      "661": {
        "name": "fields_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-field"
          }
        ]
      },
      "665": {
        "name": "return-ann_I0",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "THINARROW"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "666": {
        "name": "list-arg-elt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "667": {
        "name": "args",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I0"
          },
          {
            "type": "Nonterm",
            "name": "args_I1_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "668": {
        "name": "args_I1",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          }
        ]
      },
      "669": {
        "name": "args_I1_I0_star",
        "action": "Rule.ListCons(\"args_I1_I0\", \"args_I1_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "args_I1_I0_star"
          }
        ]
      },
      "672": {
        "name": "obj-field_A1_I2_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-field_A1_I2"
          }
        ]
      },
      "673": {
        "name": "obj-fields_I2",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "674": {
        "name": "obj-fields",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "obj-field"
          },
          {
            "type": "Nonterm",
            "name": "obj-fields_I2_opt"
          }
        ]
      },
      "675": {
        "name": "obj-fields_I2_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "obj-fields_I2"
          }
        ]
      },
      "676": {
        "name": "obj-field",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "678": {
        "name": "key",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "683": {
        "name": "for-expr_I3_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-bind-elt"
          }
        ]
      },
      "685": {
        "name": "for-expr_I3_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr_I3"
          }
        ]
      },
      "687": {
        "name": "for-expr_I3_I0_star",
        "action": "Rule.ListCons(\"for-expr_I3_I0\", \"for-expr_I3_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0"
          },
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0_star"
          }
        ]
      },
      "688": {
        "name": "try-expr_I3",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "689": {
        "name": "try-expr_I3",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "692": {
        "name": "doc-string_I0",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "DOC"
          },
          {
            "type": "Token",
            "name": "STRING"
          }
        ]
      },
      "693": {
        "name": "fun-header",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          }
        ]
      },
      "695": {
        "name": "ty-params_I0",
        "action": "Rule.Inline",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "LT"
          },
          {
            "type": "Nonterm",
            "name": "ty-params_I0_I1_star"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "698": {
        "name": "data-mixins_I0",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "DERIVING"
          },
          {
            "type": "Nonterm",
            "name": "mixins"
          }
        ]
      },
      "700": {
        "name": "mixins_I0_star",
        "action": "Rule.ListCons(\"mixins_I0\", \"mixins_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "mixins_I0"
          },
          {
            "type": "Nonterm",
            "name": "mixins_I0_star"
          }
        ]
      },
      "701": {
        "name": "mixins_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-mixin"
          }
        ]
      },
      "705": {
        "name": "datatype-expr_I4_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-expr_I4"
          }
        ]
      },
      "706": {
        "name": "datatype-expr_I4",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "first-datatype-variant"
          }
        ]
      },
      "707": {
        "name": "when-expr",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Token",
            "name": "WHEN"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "708": {
        "name": "colon-bracket-expr",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "709": {
        "name": "dot-ann",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "711": {
        "name": "inst-expr",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "LT"
          },
          {
            "type": "Nonterm",
            "name": "inst-expr_I2_star"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "714": {
        "name": "record-ann",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_opt"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "715": {
        "name": "record-ann_A0_I1",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "ann-field"
          }
        ]
      },
      "716": {
        "name": "list-ann-field",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann-field"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "717": {
        "name": "record-ann_A0_I1_I0_star",
        "action": "Rule.ListCons(\"record-ann_A0_I1_I0\", \"record-ann_A0_I1_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "record-ann_A0_I1_I0_star"
          }
        ]
      },
      "718": {
        "name": "arrow-ann-elt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "720": {
        "name": "arrow-ann_I1",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "721": {
        "name": "arrow-ann_I1_I0_star",
        "action": "Rule.ListCons(\"arrow-ann_I1_I0\", \"arrow-ann_I1_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_I0_star"
          }
        ]
      },
      "724": {
        "name": "app-ann_I2_star",
        "action": "Rule.ListCons(\"app-ann_I2\", \"app-ann_I2_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann_I2"
          },
          {
            "type": "Nonterm",
            "name": "app-ann_I2_star"
          }
        ]
      },
      "725": {
        "name": "app-ann_I2",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann-elt"
          }
        ]
      },
      "726": {
        "name": "left-app-fun-expr",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "id-expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "NAME"
          }
        ]
      },
      "727": {
        "name": "extend-expr",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "730": {
        "name": "fields",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "field"
          },
          {
            "type": "Nonterm",
            "name": "fields_I2_opt"
          }
        ]
      },
      "731": {
        "name": "list-field",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "field"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "732": {
        "name": "fields_I0_star",
        "action": "Rule.ListCons(\"fields_I0\", \"fields_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I0"
          },
          {
            "type": "Nonterm",
            "name": "fields_I0_star"
          }
        ]
      },
      "733": {
        "name": "bracket-expr",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "DOT"
          },
          {
            "type": "Token",
            "name": "LBRACK"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RBRACK"
          }
        ]
      },
      "734": {
        "name": "update-expr",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "BANG"
          },
          {
            "type": "Token",
            "name": "LBRACE"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          },
          {
            "type": "Token",
            "name": "RBRACE"
          }
        ]
      },
      "736": {
        "name": "obj-field_A1_I2",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "COLONCOLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "740": {
        "name": "if-expr_I4_star",
        "action": "Rule.ListCons(\"if-expr_I4\", \"if-expr_I4_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "if-expr_I4"
          },
          {
            "type": "Nonterm",
            "name": "if-expr_I4_star"
          }
        ]
      },
      "741": {
        "name": "if-expr_I4",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "else-if"
          }
        ]
      },
      "745": {
        "name": "for-bind-elt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-bind"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "747": {
        "name": "for-expr_I3",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "for-bind"
          }
        ]
      },
      "748": {
        "name": "for-expr_I3_I0_star",
        "action": "Rule.ListCons(\"for-expr_I3_I0\", \"for-expr_I3_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0"
          },
          {
            "type": "Nonterm",
            "name": "for-expr_I3_I0_star"
          }
        ]
      },
      "751": {
        "name": "where-clause",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "where-clause_I0_opt"
          }
        ]
      },
      "752": {
        "name": "where-clause_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "where-clause_I0"
          }
        ]
      },
      "753": {
        "name": "where-clause_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "WHERE"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "756": {
        "name": "first-data-variant",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "758": {
        "name": "data-expr_I5_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-expr_I5"
          }
        ]
      },
      "759": {
        "name": "data-expr_I5",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "first-data-variant"
          }
        ]
      },
      "760": {
        "name": "list-mixin",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "761": {
        "name": "mixins",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "mixins_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "762": {
        "name": "mixins_I0_star",
        "action": "Rule.ListCons(\"mixins_I0\", \"mixins_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "mixins_I0"
          },
          {
            "type": "Nonterm",
            "name": "mixins_I0_star"
          }
        ]
      },
      "763": {
        "name": "variant-members_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "764": {
        "name": "variant-members_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "767": {
        "name": "first-datatype-variant",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "772": {
        "name": "datatype-expr_I5_star",
        "action": "Rule.ListCons(\"datatype-expr_I5\", \"datatype-expr_I5_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5"
          },
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5_star"
          }
        ]
      },
      "773": {
        "name": "datatype-expr_I5",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-variant"
          }
        ]
      },
      "774": {
        "name": "pred-ann",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Nonterm",
            "name": "pred-ann_I1"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "775": {
        "name": "ann-field",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COLONCOLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "776": {
        "name": "ann-field",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          }
        ]
      },
      "778": {
        "name": "app-ann-elt",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "780": {
        "name": "app-ann_I2_star",
        "action": "Rule.ListCons(\"app-ann_I2\", \"app-ann_I2_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann_I2"
          },
          {
            "type": "Nonterm",
            "name": "app-ann_I2_star"
          }
        ]
      },
      "781": {
        "name": "field",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "783": {
        "name": "fields_I2",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "784": {
        "name": "fields",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "field"
          },
          {
            "type": "Nonterm",
            "name": "fields_I2_opt"
          }
        ]
      },
      "785": {
        "name": "fields_I2_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "fields_I2"
          }
        ]
      },
      "787": {
        "name": "obj-field",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Token",
            "name": "MUTABLE"
          },
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Nonterm",
            "name": "obj-field_A1_I2_opt"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "790": {
        "name": "if-expr_I5_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "if-expr_I5"
          }
        ]
      },
      "791": {
        "name": "if-expr_I5",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "ELSE"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "792": {
        "name": "if-expr_I4_star",
        "action": "Rule.ListCons(\"if-expr_I4\", \"if-expr_I4_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "if-expr_I4"
          },
          {
            "type": "Nonterm",
            "name": "if-expr_I4_star"
          }
        ]
      },
      "795": {
        "name": "for-bind",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "FROM"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          }
        ]
      },
      "798": {
        "name": "fun-expr",
        "action": "Rule.defaultAction",
        "position": 7,
        "symbols": [
          {
            "type": "Token",
            "name": "FUN"
          },
          {
            "type": "Nonterm",
            "name": "fun-header"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "799": {
        "name": "where-clause_I0",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "WHERE"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "801": {
        "name": "first-data-variant",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "802": {
        "name": "first-data-variant",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "803": {
        "name": "data-with",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-with_I0_opt"
          }
        ]
      },
      "804": {
        "name": "data-with_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-with_I0"
          }
        ]
      },
      "807": {
        "name": "data-expr_I6_star",
        "action": "Rule.ListCons(\"data-expr_I6\", \"data-expr_I6_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-expr_I6"
          },
          {
            "type": "Nonterm",
            "name": "data-expr_I6_star"
          }
        ]
      },
      "808": {
        "name": "data-expr_I6",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-variant"
          }
        ]
      },
      "811": {
        "name": "first-datatype-variant",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "813": {
        "name": "variant-members_I1_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I1"
          }
        ]
      },
      "816": {
        "name": "variant-members_I1_I0_star",
        "action": "Rule.ListCons(\"variant-members_I1_I0\", \"variant-members_I1_I0_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0_star"
          }
        ]
      },
      "817": {
        "name": "variant-members_I1_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "list-variant-member"
          }
        ]
      },
      "819": {
        "name": "variant-member_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-member_I0"
          }
        ]
      },
      "820": {
        "name": "variant-member_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "MUTABLE"
          }
        ]
      },
      "821": {
        "name": "variant-member_I0",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "CYCLIC"
          }
        ]
      },
      "822": {
        "name": "constructor-clause_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENSPACE"
          }
        ]
      },
      "823": {
        "name": "constructor-clause_I1",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          }
        ]
      },
      "828": {
        "name": "datatype-expr_I5_star",
        "action": "Rule.ListCons(\"datatype-expr_I5\", \"datatype-expr_I5_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5"
          },
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5_star"
          }
        ]
      },
      "829": {
        "name": "arrow-ann",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "arrow-ann_I0"
          },
          {
            "type": "Nonterm",
            "name": "arrow-ann_I1_opt"
          },
          {
            "type": "Token",
            "name": "THINARROW"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "830": {
        "name": "app-ann",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "app-ann_I0"
          },
          {
            "type": "Token",
            "name": "LT"
          },
          {
            "type": "Nonterm",
            "name": "app-ann_I2_star"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "GT"
          }
        ]
      },
      "834": {
        "name": "if-expr",
        "action": "Rule.defaultAction",
        "position": 7,
        "symbols": [
          {
            "type": "Token",
            "name": "IF"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "if-expr_I4_star"
          },
          {
            "type": "Nonterm",
            "name": "if-expr_I5_opt"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "835": {
        "name": "if-expr_I5",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "ELSE"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "836": {
        "name": "else-if",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "ELSEIF"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "839": {
        "name": "cases-expr_I6_star",
        "action": "Rule.ListCons(\"cases-expr_I6\", \"cases-expr_I6_star\", true)",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-expr_I6"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I6_star"
          }
        ]
      },
      "840": {
        "name": "cases-expr_I6",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-branch"
          }
        ]
      },
      "844": {
        "name": "first-data-variant",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "845": {
        "name": "data-with_I0",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "WITH"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          }
        ]
      },
      "847": {
        "name": "data-sharing",
        "action": "Rule.defaultAction",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-sharing_I0_opt"
          }
        ]
      },
      "848": {
        "name": "data-sharing_I0_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-sharing_I0"
          }
        ]
      },
      "850": {
        "name": "data-expr_I6_star",
        "action": "Rule.ListCons(\"data-expr_I6\", \"data-expr_I6_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "data-expr_I6"
          },
          {
            "type": "Nonterm",
            "name": "data-expr_I6_star"
          }
        ]
      },
      "852": {
        "name": "data-variant",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "853": {
        "name": "variant-members",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I0"
          },
          {
            "type": "Nonterm",
            "name": "variant-members_I1_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          }
        ]
      },
      "854": {
        "name": "variant-members_I1",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0_star"
          },
          {
            "type": "Nonterm",
            "name": "variant-member"
          }
        ]
      },
      "855": {
        "name": "list-variant-member",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-member"
          },
          {
            "type": "Token",
            "name": "COMMA"
          }
        ]
      },
      "856": {
        "name": "variant-members_I1_I0_star",
        "action": "Rule.ListCons(\"variant-members_I1_I0\", \"variant-members_I1_I0_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0"
          },
          {
            "type": "Nonterm",
            "name": "variant-members_I1_I0_star"
          }
        ]
      },
      "857": {
        "name": "variant-member",
        "action": "Rule.defaultAction",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "variant-member_I0_opt"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          }
        ]
      },
      "860": {
        "name": "datatype-variant",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "861": {
        "name": "datatype-expr",
        "action": "Rule.defaultAction",
        "position": 8,
        "symbols": [
          {
            "type": "Token",
            "name": "DATATYPE"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "datatype-expr_I4_opt"
          },
          {
            "type": "Nonterm",
            "name": "datatype-expr_I5_star"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "863": {
        "name": "method-expr",
        "action": "Rule.defaultAction",
        "position": 8,
        "symbols": [
          {
            "type": "Token",
            "name": "METHOD"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "865": {
        "name": "else-if",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "ELSEIF"
          },
          {
            "type": "Nonterm",
            "name": "binop-expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "869": {
        "name": "cases-expr_I7_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-expr_I7"
          }
        ]
      },
      "870": {
        "name": "cases-expr_I6_star",
        "action": "Rule.ListCons(\"cases-expr_I6\", \"cases-expr_I6_star\", true)",
        "position": 2,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-expr_I6"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I6_star"
          }
        ]
      },
      "873": {
        "name": "lambda-expr",
        "action": "Rule.defaultAction",
        "position": 9,
        "symbols": [
          {
            "type": "Token",
            "name": "FUN"
          },
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Nonterm",
            "name": "lambda-expr_I2_opt"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "875": {
        "name": "data-sharing_I0",
        "action": "Rule.Inline",
        "position": 2,
        "symbols": [
          {
            "type": "Token",
            "name": "SHARING"
          },
          {
            "type": "Nonterm",
            "name": "fields"
          }
        ]
      },
      "876": {
        "name": "data-variant",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "877": {
        "name": "data-variant",
        "action": "Rule.defaultAction",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "879": {
        "name": "datatype-variant",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause"
          }
        ]
      },
      "881": {
        "name": "obj-field",
        "action": "Rule.defaultAction",
        "position": 8,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "882": {
        "name": "cases-branch_I2",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "args"
          }
        ]
      },
      "884": {
        "name": "cases-branch_I2_opt",
        "action": "Rule.Inline",
        "position": 1,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "cases-branch_I2"
          }
        ]
      },
      "886": {
        "name": "cases-expr",
        "action": "Rule.defaultAction",
        "position": 9,
        "symbols": [
          {
            "type": "Token",
            "name": "CASES"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I1"
          },
          {
            "type": "Nonterm",
            "name": "ann"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I6_star"
          },
          {
            "type": "Nonterm",
            "name": "cases-expr_I7_opt"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "887": {
        "name": "for-expr",
        "action": "Rule.defaultAction",
        "position": 9,
        "symbols": [
          {
            "type": "Token",
            "name": "FOR"
          },
          {
            "type": "Nonterm",
            "name": "expr"
          },
          {
            "type": "Token",
            "name": "PARENNOSPACE"
          },
          {
            "type": "Nonterm",
            "name": "for-expr_I3_opt"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "888": {
        "name": "try-expr",
        "action": "Rule.defaultAction",
        "position": 9,
        "symbols": [
          {
            "type": "Token",
            "name": "TRY"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Token",
            "name": "EXCEPT"
          },
          {
            "type": "Nonterm",
            "name": "try-expr_I3"
          },
          {
            "type": "Nonterm",
            "name": "binding"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "889": {
        "name": "data-expr",
        "action": "Rule.defaultAction",
        "position": 10,
        "symbols": [
          {
            "type": "Token",
            "name": "DATA"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "ty-params"
          },
          {
            "type": "Nonterm",
            "name": "data-mixins"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "data-expr_I5_opt"
          },
          {
            "type": "Nonterm",
            "name": "data-expr_I6_star"
          },
          {
            "type": "Nonterm",
            "name": "data-sharing"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "890": {
        "name": "data-variant",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "variant-members"
          },
          {
            "type": "Nonterm",
            "name": "data-with"
          }
        ]
      },
      "893": {
        "name": "cases-branch",
        "action": "Rule.defaultAction",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "cases-branch_I2_opt"
          },
          {
            "type": "Token",
            "name": "THICKARROW"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "894": {
        "name": "cases-expr_I7",
        "action": "Rule.Inline",
        "position": 3,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "ELSE"
          },
          {
            "type": "Token",
            "name": "THICKARROW"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "896": {
        "name": "field",
        "action": "Rule.defaultAction",
        "position": 8,
        "symbols": [
          {
            "type": "Nonterm",
            "name": "key"
          },
          {
            "type": "Nonterm",
            "name": "args"
          },
          {
            "type": "Nonterm",
            "name": "return-ann"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "doc-string"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "where-clause"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "897": {
        "name": "cases-branch",
        "action": "Rule.defaultAction",
        "position": 5,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Nonterm",
            "name": "cases-branch_I2_opt"
          },
          {
            "type": "Token",
            "name": "THICKARROW"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "898": {
        "name": "cases-expr_I7",
        "action": "Rule.Inline",
        "position": 4,
        "symbols": [
          {
            "type": "Token",
            "name": "BAR"
          },
          {
            "type": "Token",
            "name": "ELSE"
          },
          {
            "type": "Token",
            "name": "THICKARROW"
          },
          {
            "type": "Nonterm",
            "name": "block"
          }
        ]
      },
      "899": {
        "name": "constructor-clause",
        "action": "Rule.defaultAction",
        "position": 7,
        "symbols": [
          {
            "type": "Token",
            "name": "WITHCONSTRUCTOR"
          },
          {
            "type": "Nonterm",
            "name": "constructor-clause_I1"
          },
          {
            "type": "Token",
            "name": "NAME"
          },
          {
            "type": "Token",
            "name": "RPAREN"
          },
          {
            "type": "Token",
            "name": "COLON"
          },
          {
            "type": "Nonterm",
            "name": "block"
          },
          {
            "type": "Nonterm",
            "name": "end"
          }
        ]
      },
      "902": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 3
      },
      "903": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 3
      },
      "904": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 3
      },
      "905": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 3
      },
      "906": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 3
      },
      "907": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 3
      },
      "908": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 3
      },
      "909": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 3
      },
      "910": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 3
      },
      "911": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 3
      },
      "912": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 3
      },
      "913": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 3
      },
      "914": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 3
      },
      "915": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 3
      },
      "916": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 3
      },
      "917": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 3
      },
      "918": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 3
      },
      "919": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 3
      },
      "920": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 3
      },
      "921": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 3
      },
      "922": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 3
      },
      "923": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 3
      },
      "924": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 3
      },
      "925": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 3
      },
      "927": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 4
      },
      "928": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 4
      },
      "931": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 4
      },
      "933": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 4
      },
      "935": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 4
      },
      "937": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 4
      },
      "939": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 4
      },
      "941": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 4
      },
      "943": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 4
      },
      "945": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 4
      },
      "947": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 4
      },
      "949": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 4
      },
      "951": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 4
      },
      "953": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 4
      },
      "955": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 4
      },
      "957": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 4
      },
      "959": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 4
      },
      "961": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 4
      },
      "963": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 4
      },
      "965": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 4
      },
      "967": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 4
      },
      "969": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 4
      },
      "971": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 4
      },
      "973": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 4
      },
      "975": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 4
      },
      "1640": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 33
      },
      "4277": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 41
      },
      "4278": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 42
      },
      "4282": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 41
      },
      "4283": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 41
      },
      "4284": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 41
      },
      "4285": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 41
      },
      "4286": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 42
      },
      "4288": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 42
      },
      "4290": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 42
      },
      "4292": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 42
      },
      "4356": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 17
      },
      "4357": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 17
      },
      "4358": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 18
      },
      "4360": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 18
      },
      "4368": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 134
      },
      "4369": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 134
      },
      "4626": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 217
      },
      "4627": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 217
      },
      "4628": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 217
      },
      "4649": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 244
      },
      "4652": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 247
      },
      "4653": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 247
      },
      "4654": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 247
      },
      "4655": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 247
      },
      "4656": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 247
      },
      "4657": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 247
      },
      "4658": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 247
      },
      "4659": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 247
      },
      "4660": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 247
      },
      "4661": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 247
      },
      "4662": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 247
      },
      "4663": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 247
      },
      "4664": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 247
      },
      "4665": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 247
      },
      "4666": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 247
      },
      "4667": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 247
      },
      "4668": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 247
      },
      "4788": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 17
      },
      "4789": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 18
      },
      "4884": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 193
      },
      "4885": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 193
      },
      "4891": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 45
      },
      "4898": {
        "lookahead": {
          "type": "Token",
          "name": "DERIVING"
        },
        "like": 41
      },
      "4899": {
        "lookahead": {
          "type": "Token",
          "name": "DERIVING"
        },
        "like": 42
      },
      "4915": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 210
      },
      "4916": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 210
      },
      "4917": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 210
      },
      "4918": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 210
      },
      "4985": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 199
      },
      "4988": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 202
      },
      "4989": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 202
      },
      "4990": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 202
      },
      "4991": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 202
      },
      "4992": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 202
      },
      "4993": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 202
      },
      "4994": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 202
      },
      "4995": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 202
      },
      "4996": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 202
      },
      "4997": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 202
      },
      "4998": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 202
      },
      "4999": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 202
      },
      "5000": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 202
      },
      "5001": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 202
      },
      "5002": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 202
      },
      "5003": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 202
      },
      "5004": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 202
      },
      "5066": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 59
      },
      "5067": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 60
      },
      "5071": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 52
      },
      "5074": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 55
      },
      "5075": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 55
      },
      "5198": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 63
      },
      "5199": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 63
      },
      "5200": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 63
      },
      "5201": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 63
      },
      "5202": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 63
      },
      "5203": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 63
      },
      "5204": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 63
      },
      "5205": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 63
      },
      "5206": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 63
      },
      "5207": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 63
      },
      "5208": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 63
      },
      "5209": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 63
      },
      "5210": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 63
      },
      "5211": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 63
      },
      "5212": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 63
      },
      "5213": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 63
      },
      "5214": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 63
      },
      "5215": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 63
      },
      "5216": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 63
      },
      "5217": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 63
      },
      "5218": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 63
      },
      "5219": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 63
      },
      "5220": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 63
      },
      "5221": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 63
      },
      "5222": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 63
      },
      "5223": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 63
      },
      "5224": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 63
      },
      "5225": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 64
      },
      "5227": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 64
      },
      "5229": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 64
      },
      "5231": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 64
      },
      "5233": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 64
      },
      "5235": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 64
      },
      "5237": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 64
      },
      "5239": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 64
      },
      "5241": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 64
      },
      "5243": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 64
      },
      "5245": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 64
      },
      "5247": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 64
      },
      "5249": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 64
      },
      "5251": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 64
      },
      "5253": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 64
      },
      "5255": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 64
      },
      "5257": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 64
      },
      "5259": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 64
      },
      "5261": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 64
      },
      "5263": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 64
      },
      "5265": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 64
      },
      "5267": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 64
      },
      "5269": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 64
      },
      "5271": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 64
      },
      "5273": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 64
      },
      "5275": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 64
      },
      "5277": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 64
      },
      "5317": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 81
      },
      "5318": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 82
      },
      "5383": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 299
      },
      "5386": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 302
      },
      "5394": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 312
      },
      "5397": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 315
      },
      "5398": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 315
      },
      "5399": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 315
      },
      "5400": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 315
      },
      "5427": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 231
      },
      "5428": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 231
      },
      "5451": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 226
      },
      "5462": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 17
      },
      "5463": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 17
      },
      "5464": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 18
      },
      "5466": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 18
      },
      "5626": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 281
      },
      "5629": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 284
      },
      "5630": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 284
      },
      "5646": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 17
      },
      "5647": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 18
      },
      "5738": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 113
      },
      "5739": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 113
      },
      "5740": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 113
      },
      "5741": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 113
      },
      "5742": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 113
      },
      "5743": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 113
      },
      "5744": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 113
      },
      "5745": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 113
      },
      "5746": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 113
      },
      "5747": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 113
      },
      "5748": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 113
      },
      "5749": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 113
      },
      "5750": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 113
      },
      "5751": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 113
      },
      "5752": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 113
      },
      "5753": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 113
      },
      "5754": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 113
      },
      "5807": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 118
      },
      "5808": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 118
      },
      "5809": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 118
      },
      "5810": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 118
      },
      "5853": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 322
      },
      "5854": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 322
      },
      "5855": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 322
      },
      "5856": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 322
      },
      "5890": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 258
      },
      "5891": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 258
      },
      "5892": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 258
      },
      "5918": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 67
      },
      "5919": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 67
      },
      "5920": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 68
      },
      "5922": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 68
      },
      "5928": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 75
      },
      "5929": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 75
      },
      "5930": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 75
      },
      "5931": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 75
      },
      "5932": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 75
      },
      "5975": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 121
      },
      "5976": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 121
      },
      "5977": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 121
      },
      "6016": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 261
      },
      "6017": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 261
      },
      "6044": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 78
      },
      "6045": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 78
      },
      "6046": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 78
      },
      "6047": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 78
      },
      "6069": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 92
      },
      "6072": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 95
      },
      "6073": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 95
      },
      "6074": {
        "lookahead": {
          "type": "Token",
          "name": "CYCLIC"
        },
        "like": 95
      },
      "6075": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 95
      },
      "6089": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 100
      },
      "6090": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 100
      },
      "6120": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 268
      },
      "6121": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 268
      },
      "6122": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 268
      },
      "6139": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 108
      },
      "6140": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 108
      },
      "6141": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 108
      },
      "6142": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 109
      },
      "6144": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 109
      },
      "6146": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 109
      },
      "6179": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 271
      },
      "6180": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 271
      },
      "6202": {
        "lookahead": {
          "type": "Token",
          "name": "THICKARROW"
        },
        "like": 275
      },
      "6222": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 333
      },
      "6223": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 334
      },
      "6224": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 334
      },
      "6225": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 334
      },
      "6226": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 334
      },
      "6227": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 334
      },
      "6228": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 334
      },
      "6229": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 334
      },
      "6230": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 334
      },
      "6231": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 334
      },
      "6232": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 334
      },
      "6233": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 334
      },
      "6234": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 334
      },
      "6235": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 334
      },
      "6236": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 334
      },
      "6237": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 334
      },
      "6238": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 334
      },
      "6239": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 334
      },
      "6240": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 334
      },
      "6241": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 334
      },
      "6242": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 334
      },
      "6243": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 334
      },
      "6244": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 334
      },
      "6245": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 334
      },
      "6246": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 334
      },
      "6247": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 334
      },
      "6248": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 335
      },
      "6249": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 335
      },
      "6250": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 335
      },
      "6251": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 335
      },
      "6252": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 335
      },
      "6253": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 335
      },
      "6254": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 335
      },
      "6255": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 335
      },
      "6256": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 335
      },
      "6257": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 335
      },
      "6258": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 335
      },
      "6259": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 335
      },
      "6260": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 335
      },
      "6261": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 335
      },
      "6262": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 335
      },
      "6263": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 335
      },
      "6264": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 335
      },
      "6265": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 335
      },
      "6266": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 335
      },
      "6267": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 335
      },
      "6268": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 335
      },
      "6269": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 335
      },
      "6270": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 335
      },
      "6271": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 335
      },
      "6272": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 335
      },
      "6273": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 335
      },
      "6274": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 336
      },
      "6275": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 336
      },
      "6276": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 336
      },
      "6277": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 336
      },
      "6278": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 336
      },
      "6279": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 336
      },
      "6280": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 336
      },
      "6281": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 336
      },
      "6282": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 336
      },
      "6283": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 336
      },
      "6284": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 336
      },
      "6285": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 336
      },
      "6286": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 336
      },
      "6287": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 336
      },
      "6288": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 336
      },
      "6289": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 336
      },
      "6290": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 336
      },
      "6291": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 336
      },
      "6292": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 336
      },
      "6293": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 336
      },
      "6294": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 336
      },
      "6295": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 336
      },
      "6296": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 336
      },
      "6297": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 336
      },
      "6298": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 336
      },
      "6299": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 336
      },
      "6300": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 337
      },
      "6301": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 337
      },
      "6302": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 337
      },
      "6303": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 337
      },
      "6304": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 337
      },
      "6305": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 337
      },
      "6306": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 337
      },
      "6307": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 337
      },
      "6308": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 337
      },
      "6309": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 337
      },
      "6310": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 337
      },
      "6311": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 337
      },
      "6312": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 337
      },
      "6313": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 337
      },
      "6314": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 337
      },
      "6315": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 337
      },
      "6316": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 337
      },
      "6317": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 337
      },
      "6318": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 337
      },
      "6319": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 337
      },
      "6320": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 337
      },
      "6321": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 337
      },
      "6322": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 337
      },
      "6323": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 337
      },
      "6324": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 337
      },
      "6325": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 338
      },
      "6326": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 338
      },
      "6327": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 338
      },
      "6328": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 338
      },
      "6329": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 338
      },
      "6330": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 338
      },
      "6331": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 338
      },
      "6332": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 338
      },
      "6333": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 338
      },
      "6334": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 338
      },
      "6335": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 338
      },
      "6336": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 338
      },
      "6337": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 338
      },
      "6338": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 338
      },
      "6339": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 338
      },
      "6340": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 338
      },
      "6341": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 338
      },
      "6342": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 338
      },
      "6343": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 338
      },
      "6344": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 338
      },
      "6345": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 338
      },
      "6346": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 338
      },
      "6347": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 338
      },
      "6348": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 338
      },
      "6349": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 338
      },
      "6350": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 338
      },
      "6409": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 341
      },
      "6410": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 341
      },
      "6411": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 341
      },
      "6412": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 341
      },
      "6413": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 341
      },
      "6414": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 341
      },
      "6415": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 341
      },
      "6416": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 341
      },
      "6417": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 341
      },
      "6418": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 341
      },
      "6419": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 341
      },
      "6420": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 341
      },
      "6421": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 341
      },
      "6422": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 341
      },
      "6423": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 341
      },
      "6424": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 341
      },
      "6425": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 341
      },
      "6426": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 341
      },
      "6427": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 341
      },
      "6428": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 341
      },
      "6429": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 341
      },
      "6430": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 341
      },
      "6431": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 341
      },
      "6432": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 341
      },
      "6433": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 341
      },
      "6434": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 341
      },
      "6435": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 341
      },
      "6436": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 341
      },
      "6437": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 341
      },
      "6438": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 341
      },
      "6439": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 341
      },
      "6440": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 341
      },
      "6441": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 341
      },
      "6442": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 341
      },
      "6443": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 341
      },
      "6444": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 341
      },
      "6445": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 341
      },
      "6446": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 341
      },
      "6447": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 341
      },
      "6448": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 341
      },
      "6449": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 341
      },
      "6450": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 341
      },
      "6451": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 341
      },
      "6452": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 341
      },
      "6453": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 341
      },
      "6454": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 341
      },
      "6455": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 341
      },
      "6456": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 341
      },
      "6457": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 341
      },
      "6458": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 341
      },
      "6459": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 341
      },
      "6460": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 342
      },
      "6461": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 342
      },
      "6462": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 342
      },
      "6463": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 342
      },
      "6464": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 342
      },
      "6465": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 342
      },
      "6466": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 342
      },
      "6467": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 342
      },
      "6468": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 342
      },
      "6469": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 342
      },
      "6470": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 342
      },
      "6471": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 342
      },
      "6472": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 342
      },
      "6473": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 342
      },
      "6474": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 342
      },
      "6475": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 342
      },
      "6476": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 342
      },
      "6477": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 342
      },
      "6478": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 342
      },
      "6479": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 342
      },
      "6480": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 342
      },
      "6481": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 342
      },
      "6482": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 342
      },
      "6483": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 342
      },
      "6484": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 342
      },
      "6485": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 342
      },
      "6486": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 342
      },
      "6487": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 342
      },
      "6488": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 342
      },
      "6489": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 342
      },
      "6490": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 342
      },
      "6491": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 342
      },
      "6492": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 342
      },
      "6493": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 342
      },
      "6494": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 342
      },
      "6495": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 342
      },
      "6496": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 342
      },
      "6497": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 342
      },
      "6498": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 342
      },
      "6499": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 342
      },
      "6500": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 342
      },
      "6501": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 342
      },
      "6502": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 342
      },
      "6503": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 342
      },
      "6504": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 342
      },
      "6505": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 342
      },
      "6506": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 342
      },
      "6507": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 342
      },
      "6508": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 342
      },
      "6509": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 342
      },
      "6510": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 342
      },
      "6511": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 342
      },
      "6512": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 342
      },
      "6513": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 342
      },
      "6514": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 342
      },
      "6515": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 342
      },
      "6568": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 345
      },
      "6569": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 345
      },
      "6570": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 345
      },
      "6571": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 345
      },
      "6572": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 345
      },
      "6573": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 345
      },
      "6574": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 345
      },
      "6575": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 345
      },
      "6576": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 345
      },
      "6577": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 345
      },
      "6578": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 345
      },
      "6579": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 345
      },
      "6580": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 345
      },
      "6581": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 345
      },
      "6582": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 345
      },
      "6583": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 345
      },
      "6584": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 345
      },
      "6585": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 345
      },
      "6586": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 345
      },
      "6587": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 345
      },
      "6588": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 345
      },
      "6589": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 345
      },
      "6590": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 345
      },
      "6591": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 345
      },
      "6592": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 345
      },
      "6593": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 345
      },
      "6594": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 345
      },
      "6595": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 345
      },
      "6596": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 345
      },
      "6597": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 345
      },
      "6598": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 345
      },
      "6599": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 345
      },
      "6600": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 346
      },
      "6601": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 346
      },
      "6602": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 346
      },
      "6603": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 346
      },
      "6604": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 346
      },
      "6605": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 346
      },
      "6606": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 346
      },
      "6607": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 346
      },
      "6608": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 347
      },
      "6609": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 347
      },
      "6610": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 347
      },
      "6611": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 347
      },
      "6612": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 347
      },
      "6613": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 347
      },
      "6614": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 347
      },
      "6615": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 347
      },
      "6616": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 348
      },
      "6617": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 348
      },
      "6618": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 348
      },
      "6619": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 348
      },
      "6620": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 348
      },
      "6621": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 348
      },
      "6622": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 348
      },
      "6623": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 348
      },
      "6624": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 348
      },
      "6625": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 348
      },
      "6626": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 348
      },
      "6627": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 348
      },
      "6628": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 348
      },
      "6629": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 348
      },
      "6630": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 348
      },
      "6631": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 348
      },
      "6632": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 348
      },
      "6633": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 348
      },
      "6634": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 348
      },
      "6635": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 348
      },
      "6636": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 348
      },
      "6637": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 348
      },
      "6638": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 348
      },
      "6639": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 348
      },
      "6640": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 348
      },
      "6641": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 348
      },
      "6642": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 348
      },
      "6643": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 348
      },
      "6644": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 348
      },
      "6645": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 348
      },
      "6646": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 348
      },
      "6647": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 348
      },
      "6648": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 349
      },
      "6649": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 349
      },
      "6650": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 349
      },
      "6651": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 349
      },
      "6652": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 349
      },
      "6653": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 349
      },
      "6654": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 349
      },
      "6655": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 349
      },
      "6656": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 349
      },
      "6657": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 349
      },
      "6658": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 349
      },
      "6659": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 349
      },
      "6660": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 349
      },
      "6661": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 349
      },
      "6662": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 349
      },
      "6663": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 349
      },
      "6664": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 349
      },
      "6665": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 349
      },
      "6666": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 349
      },
      "6667": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 349
      },
      "6668": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 349
      },
      "6669": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 349
      },
      "6670": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 349
      },
      "6671": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 349
      },
      "6672": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 349
      },
      "6673": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 349
      },
      "6674": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 349
      },
      "6675": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 349
      },
      "6676": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 349
      },
      "6677": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 349
      },
      "6678": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 349
      },
      "6679": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 349
      },
      "6680": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 350
      },
      "6681": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 350
      },
      "6682": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 350
      },
      "6683": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 350
      },
      "6684": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 350
      },
      "6685": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 350
      },
      "6686": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 350
      },
      "6687": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 350
      },
      "6688": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 350
      },
      "6689": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 350
      },
      "6690": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 350
      },
      "6691": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 350
      },
      "6692": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 350
      },
      "6693": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 350
      },
      "6694": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 350
      },
      "6695": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 350
      },
      "6696": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 350
      },
      "6697": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 350
      },
      "6698": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 350
      },
      "6699": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 350
      },
      "6700": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 350
      },
      "6701": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 350
      },
      "6702": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 350
      },
      "6703": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 350
      },
      "6704": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 350
      },
      "6705": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 350
      },
      "6706": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 350
      },
      "6707": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 350
      },
      "6708": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 350
      },
      "6709": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 350
      },
      "6710": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 350
      },
      "6711": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 350
      },
      "6712": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 351
      },
      "6713": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 351
      },
      "6714": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 351
      },
      "6715": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 351
      },
      "6716": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 351
      },
      "6717": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 351
      },
      "6718": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 351
      },
      "6719": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 351
      },
      "6720": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 351
      },
      "6721": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 351
      },
      "6722": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 351
      },
      "6723": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 351
      },
      "6724": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 351
      },
      "6725": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 351
      },
      "6726": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 351
      },
      "6727": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 351
      },
      "6728": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 351
      },
      "6729": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 351
      },
      "6730": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 351
      },
      "6731": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 351
      },
      "6732": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 351
      },
      "6733": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 351
      },
      "6734": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 351
      },
      "6735": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 351
      },
      "6736": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 351
      },
      "6737": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 351
      },
      "6738": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 351
      },
      "6739": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 351
      },
      "6740": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 351
      },
      "6741": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 351
      },
      "6742": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 351
      },
      "6743": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 351
      },
      "6744": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 352
      },
      "6745": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 352
      },
      "6746": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 352
      },
      "6747": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 352
      },
      "6748": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 352
      },
      "6749": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 352
      },
      "6750": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 352
      },
      "6751": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 352
      },
      "6752": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 352
      },
      "6753": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 352
      },
      "6754": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 352
      },
      "6755": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 352
      },
      "6756": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 352
      },
      "6757": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 352
      },
      "6758": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 352
      },
      "6759": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 352
      },
      "6760": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 352
      },
      "6761": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 352
      },
      "6762": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 352
      },
      "6763": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 352
      },
      "6764": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 352
      },
      "6765": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 352
      },
      "6766": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 352
      },
      "6767": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 352
      },
      "6768": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 352
      },
      "6769": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 352
      },
      "6770": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 352
      },
      "6771": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 352
      },
      "6772": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 352
      },
      "6773": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 352
      },
      "6774": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 352
      },
      "6775": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 352
      },
      "6776": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 353
      },
      "6777": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 353
      },
      "6778": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 353
      },
      "6779": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 353
      },
      "6780": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 353
      },
      "6781": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 353
      },
      "6782": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 353
      },
      "6783": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 353
      },
      "6784": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 353
      },
      "6785": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 353
      },
      "6786": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 353
      },
      "6787": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 353
      },
      "6788": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 353
      },
      "6789": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 353
      },
      "6790": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 353
      },
      "6791": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 353
      },
      "6792": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 353
      },
      "6793": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 353
      },
      "6794": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 353
      },
      "6795": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 353
      },
      "6796": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 353
      },
      "6797": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 353
      },
      "6798": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 353
      },
      "6799": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 353
      },
      "6800": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 353
      },
      "6801": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 353
      },
      "6802": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 353
      },
      "6803": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 353
      },
      "6804": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 353
      },
      "6805": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 353
      },
      "6806": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 353
      },
      "6807": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 353
      },
      "6808": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 354
      },
      "6809": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 354
      },
      "6810": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 354
      },
      "6811": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 354
      },
      "6812": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 354
      },
      "6813": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 354
      },
      "6814": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 354
      },
      "6815": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 354
      },
      "6816": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 354
      },
      "6817": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 354
      },
      "6818": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 354
      },
      "6819": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 354
      },
      "6820": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 354
      },
      "6821": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 354
      },
      "6822": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 354
      },
      "6823": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 354
      },
      "6824": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 354
      },
      "6825": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 354
      },
      "6826": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 354
      },
      "6827": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 354
      },
      "6828": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 354
      },
      "6829": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 354
      },
      "6830": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 354
      },
      "6831": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 354
      },
      "6832": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 354
      },
      "6833": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 354
      },
      "6834": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 354
      },
      "6835": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 354
      },
      "6836": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 354
      },
      "6837": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 354
      },
      "6838": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 354
      },
      "6839": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 354
      },
      "6840": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 355
      },
      "6841": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 355
      },
      "6842": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 355
      },
      "6843": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 355
      },
      "6844": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 355
      },
      "6845": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 355
      },
      "6846": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 355
      },
      "6847": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 355
      },
      "6848": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 355
      },
      "6849": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 355
      },
      "6850": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 355
      },
      "6851": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 355
      },
      "6852": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 355
      },
      "6853": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 355
      },
      "6854": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 355
      },
      "6855": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 355
      },
      "6856": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 355
      },
      "6857": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 355
      },
      "6858": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 355
      },
      "6859": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 355
      },
      "6860": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 355
      },
      "6861": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 355
      },
      "6862": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 355
      },
      "6863": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 355
      },
      "6864": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 355
      },
      "6865": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 355
      },
      "6866": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 355
      },
      "6867": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 355
      },
      "6868": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 355
      },
      "6869": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 355
      },
      "6870": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 355
      },
      "6871": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 355
      },
      "6872": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 356
      },
      "6873": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 356
      },
      "6874": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 356
      },
      "6875": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 356
      },
      "6876": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 356
      },
      "6877": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 356
      },
      "6878": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 356
      },
      "6879": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 356
      },
      "6880": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 356
      },
      "6881": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 356
      },
      "6882": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 356
      },
      "6883": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 356
      },
      "6884": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 356
      },
      "6885": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 356
      },
      "6886": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 356
      },
      "6887": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 356
      },
      "6888": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 356
      },
      "6889": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 356
      },
      "6890": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 356
      },
      "6891": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 356
      },
      "6892": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 356
      },
      "6893": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 356
      },
      "6894": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 356
      },
      "6895": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 356
      },
      "6896": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 356
      },
      "6897": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 356
      },
      "6898": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 356
      },
      "6899": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 356
      },
      "6900": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 356
      },
      "6901": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 356
      },
      "6902": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 356
      },
      "6903": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 356
      },
      "6904": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 357
      },
      "6905": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 357
      },
      "6906": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 357
      },
      "6907": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 357
      },
      "6908": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 357
      },
      "6909": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 357
      },
      "6910": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 357
      },
      "6911": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 357
      },
      "6912": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 357
      },
      "6913": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 357
      },
      "6914": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 357
      },
      "6915": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 357
      },
      "6916": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 357
      },
      "6917": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 357
      },
      "6918": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 357
      },
      "6919": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 357
      },
      "6920": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 357
      },
      "6921": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 357
      },
      "6922": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 357
      },
      "6923": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 357
      },
      "6924": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 357
      },
      "6925": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 357
      },
      "6926": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 357
      },
      "6927": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 357
      },
      "6928": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 357
      },
      "6929": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 357
      },
      "6930": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 357
      },
      "6931": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 357
      },
      "6932": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 357
      },
      "6933": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 357
      },
      "6934": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 357
      },
      "6935": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 357
      },
      "7000": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 360
      },
      "7001": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 360
      },
      "7002": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 360
      },
      "7003": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 360
      },
      "7004": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 360
      },
      "7005": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 360
      },
      "7006": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 360
      },
      "7007": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 360
      },
      "7008": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 360
      },
      "7009": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 360
      },
      "7010": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 360
      },
      "7011": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 360
      },
      "7012": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 360
      },
      "7013": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 360
      },
      "7014": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 360
      },
      "7015": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 360
      },
      "7016": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 360
      },
      "7017": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 360
      },
      "7018": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 360
      },
      "7019": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 360
      },
      "7020": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 360
      },
      "7021": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 360
      },
      "7022": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 360
      },
      "7023": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 360
      },
      "7024": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 360
      },
      "7025": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 360
      },
      "7026": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 360
      },
      "7027": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 360
      },
      "7028": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 360
      },
      "7029": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 360
      },
      "7030": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 360
      },
      "7031": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 360
      },
      "7036": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 362
      },
      "7037": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 363
      },
      "7369": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 373
      },
      "7370": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 373
      },
      "7371": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 373
      },
      "7372": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 373
      },
      "7373": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 373
      },
      "7374": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 373
      },
      "7375": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 373
      },
      "7376": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 373
      },
      "7377": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 373
      },
      "7378": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 373
      },
      "7379": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 373
      },
      "7380": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 373
      },
      "7381": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 373
      },
      "7382": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 373
      },
      "7383": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 373
      },
      "7384": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 373
      },
      "7385": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 373
      },
      "7386": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 373
      },
      "7387": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 373
      },
      "7388": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 373
      },
      "7389": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 373
      },
      "7390": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 373
      },
      "7391": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 373
      },
      "7392": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 373
      },
      "7393": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 373
      },
      "7394": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 373
      },
      "7395": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 373
      },
      "7396": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 373
      },
      "7397": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 373
      },
      "7398": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 373
      },
      "7399": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 373
      },
      "7400": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 373
      },
      "7401": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 373
      },
      "7402": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 373
      },
      "7403": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 373
      },
      "7404": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 373
      },
      "7405": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 373
      },
      "7406": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 373
      },
      "7407": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 373
      },
      "7408": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 373
      },
      "7409": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 373
      },
      "7410": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 374
      },
      "7411": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 374
      },
      "7412": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 374
      },
      "7413": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 374
      },
      "7414": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 374
      },
      "7415": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 374
      },
      "7416": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 374
      },
      "7417": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 374
      },
      "7418": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 374
      },
      "7419": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 374
      },
      "7420": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 374
      },
      "7421": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 374
      },
      "7422": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 374
      },
      "7423": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 374
      },
      "7424": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 374
      },
      "7425": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 374
      },
      "7426": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 374
      },
      "7427": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 374
      },
      "7428": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 374
      },
      "7429": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 374
      },
      "7430": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 374
      },
      "7431": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 374
      },
      "7432": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 374
      },
      "7433": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 374
      },
      "7434": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 374
      },
      "7435": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 374
      },
      "7436": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 374
      },
      "7437": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 374
      },
      "7438": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 374
      },
      "7439": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 374
      },
      "7440": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 374
      },
      "7441": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 374
      },
      "7442": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 374
      },
      "7443": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 374
      },
      "7444": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 374
      },
      "7445": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 374
      },
      "7446": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 374
      },
      "7447": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 374
      },
      "7448": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 374
      },
      "7449": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 374
      },
      "7450": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 374
      },
      "7451": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 374
      },
      "7452": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 374
      },
      "7453": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 374
      },
      "7454": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 374
      },
      "7455": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 374
      },
      "7456": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 374
      },
      "7457": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 374
      },
      "7458": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 374
      },
      "7459": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 374
      },
      "7460": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 374
      },
      "7461": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 374
      },
      "7462": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 375
      },
      "7463": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 375
      },
      "7464": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 375
      },
      "7465": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 375
      },
      "7466": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 375
      },
      "7467": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 375
      },
      "7468": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 375
      },
      "7469": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 375
      },
      "7470": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 375
      },
      "7471": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 375
      },
      "7472": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 375
      },
      "7473": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 375
      },
      "7474": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 375
      },
      "7475": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 375
      },
      "7476": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 375
      },
      "7477": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 375
      },
      "7478": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 375
      },
      "7479": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 375
      },
      "7480": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 375
      },
      "7481": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 375
      },
      "7482": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 375
      },
      "7483": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 375
      },
      "7484": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 375
      },
      "7485": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 375
      },
      "7486": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 375
      },
      "7487": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 375
      },
      "7488": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 375
      },
      "7489": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 375
      },
      "7490": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 375
      },
      "7491": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 375
      },
      "7492": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 375
      },
      "7493": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 375
      },
      "7494": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 375
      },
      "7495": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 375
      },
      "7496": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 375
      },
      "7497": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 375
      },
      "7498": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 375
      },
      "7499": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 375
      },
      "7500": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 375
      },
      "7501": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 375
      },
      "7502": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 375
      },
      "7503": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 375
      },
      "7504": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 375
      },
      "7505": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 375
      },
      "7506": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 375
      },
      "7507": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 375
      },
      "7508": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 375
      },
      "7509": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 375
      },
      "7510": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 375
      },
      "7511": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 375
      },
      "7512": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 375
      },
      "7513": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 375
      },
      "8182": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 388
      },
      "8183": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 388
      },
      "8184": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 388
      },
      "8185": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 388
      },
      "8186": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 388
      },
      "8187": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 388
      },
      "8188": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 388
      },
      "8189": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 388
      },
      "8190": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 388
      },
      "8191": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 388
      },
      "8192": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 388
      },
      "8193": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 388
      },
      "8194": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 388
      },
      "8195": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 388
      },
      "8196": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 388
      },
      "8197": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 388
      },
      "8198": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 388
      },
      "8199": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 388
      },
      "8200": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 388
      },
      "8201": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 388
      },
      "8202": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 388
      },
      "8203": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 388
      },
      "8204": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 388
      },
      "8205": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 388
      },
      "8206": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 388
      },
      "8207": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 388
      },
      "8208": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 388
      },
      "8209": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 388
      },
      "8210": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 388
      },
      "8211": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 388
      },
      "8212": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 388
      },
      "8213": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 388
      },
      "8214": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 388
      },
      "8215": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 388
      },
      "8216": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 388
      },
      "8217": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 388
      },
      "8218": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 388
      },
      "8219": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 388
      },
      "8220": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 388
      },
      "8221": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 388
      },
      "8222": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 388
      },
      "8223": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 388
      },
      "8224": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 388
      },
      "8225": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 388
      },
      "8226": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 388
      },
      "8227": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 388
      },
      "8228": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 388
      },
      "8229": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 388
      },
      "8230": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 388
      },
      "8231": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 388
      },
      "8232": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 388
      },
      "8233": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 388
      },
      "8234": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 388
      },
      "8235": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 388
      },
      "8236": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 388
      },
      "8237": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 388
      },
      "8238": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 389
      },
      "8239": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 389
      },
      "8240": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 389
      },
      "8241": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 389
      },
      "8242": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 389
      },
      "8243": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 389
      },
      "8244": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 389
      },
      "8245": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 389
      },
      "8246": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 389
      },
      "8247": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 389
      },
      "8248": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 389
      },
      "8249": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 389
      },
      "8250": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 389
      },
      "8251": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 389
      },
      "8252": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 389
      },
      "8253": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 389
      },
      "8254": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 389
      },
      "8255": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 389
      },
      "8256": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 389
      },
      "8257": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 389
      },
      "8258": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 389
      },
      "8259": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 389
      },
      "8260": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 389
      },
      "8261": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 389
      },
      "8262": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 389
      },
      "8263": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 389
      },
      "8264": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 389
      },
      "8265": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 389
      },
      "8266": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 389
      },
      "8267": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 389
      },
      "8268": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 389
      },
      "8269": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 389
      },
      "8270": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 389
      },
      "8271": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 389
      },
      "8272": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 389
      },
      "8273": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 389
      },
      "8274": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 389
      },
      "8275": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 389
      },
      "8276": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 389
      },
      "8277": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 389
      },
      "8278": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 389
      },
      "8279": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 389
      },
      "8280": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 389
      },
      "8281": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 389
      },
      "8282": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 389
      },
      "8283": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 389
      },
      "8284": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 389
      },
      "8285": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 389
      },
      "8286": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 389
      },
      "8287": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 389
      },
      "8288": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 389
      },
      "8289": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 389
      },
      "8290": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 389
      },
      "8291": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 389
      },
      "8292": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 389
      },
      "8293": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 389
      },
      "8294": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 390
      },
      "8295": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 390
      },
      "8296": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 390
      },
      "8297": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 390
      },
      "8298": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 390
      },
      "8299": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 390
      },
      "8300": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 390
      },
      "8301": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 390
      },
      "8302": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 390
      },
      "8303": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 390
      },
      "8304": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 390
      },
      "8305": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 390
      },
      "8306": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 390
      },
      "8307": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 390
      },
      "8308": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 390
      },
      "8309": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 390
      },
      "8310": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 390
      },
      "8311": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 390
      },
      "8312": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 390
      },
      "8313": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 390
      },
      "8314": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 390
      },
      "8315": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 390
      },
      "8316": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 390
      },
      "8317": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 390
      },
      "8318": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 390
      },
      "8319": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 390
      },
      "8320": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 390
      },
      "8321": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 390
      },
      "8322": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 390
      },
      "8323": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 390
      },
      "8324": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 390
      },
      "8325": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 390
      },
      "8326": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 390
      },
      "8327": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 390
      },
      "8328": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 390
      },
      "8329": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 390
      },
      "8330": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 390
      },
      "8331": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 390
      },
      "8332": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 390
      },
      "8333": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 390
      },
      "8334": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 390
      },
      "8335": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 390
      },
      "8336": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 390
      },
      "8337": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 390
      },
      "8338": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 390
      },
      "8339": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 390
      },
      "8340": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 390
      },
      "8341": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 390
      },
      "8342": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 390
      },
      "8343": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 390
      },
      "8344": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 390
      },
      "8345": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 390
      },
      "8346": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 390
      },
      "8347": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 390
      },
      "8348": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 390
      },
      "8349": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 390
      },
      "8350": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 391
      },
      "8351": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 391
      },
      "8352": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 391
      },
      "8353": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 391
      },
      "8354": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 391
      },
      "8355": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 391
      },
      "8356": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 391
      },
      "8357": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 391
      },
      "8358": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 391
      },
      "8359": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 391
      },
      "8360": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 391
      },
      "8361": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 391
      },
      "8362": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 391
      },
      "8363": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 391
      },
      "8364": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 391
      },
      "8365": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 391
      },
      "8366": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 391
      },
      "8367": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 391
      },
      "8368": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 391
      },
      "8369": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 391
      },
      "8370": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 391
      },
      "8371": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 391
      },
      "8372": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 391
      },
      "8373": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 391
      },
      "8374": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 391
      },
      "8375": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 391
      },
      "8376": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 391
      },
      "8377": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 391
      },
      "8378": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 391
      },
      "8379": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 391
      },
      "8380": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 391
      },
      "8381": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 391
      },
      "8382": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 391
      },
      "8383": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 391
      },
      "8384": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 391
      },
      "8385": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 391
      },
      "8386": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 391
      },
      "8387": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 391
      },
      "8388": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 391
      },
      "8389": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 391
      },
      "8390": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 391
      },
      "8391": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 391
      },
      "8392": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 391
      },
      "8393": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 391
      },
      "8394": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 391
      },
      "8395": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 391
      },
      "8396": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 391
      },
      "8397": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 391
      },
      "8398": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 391
      },
      "8399": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 391
      },
      "8400": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 391
      },
      "8401": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 391
      },
      "8402": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 391
      },
      "8403": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 391
      },
      "8404": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 391
      },
      "8405": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 391
      },
      "8406": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 392
      },
      "8407": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 392
      },
      "8408": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 392
      },
      "8409": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 392
      },
      "8410": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 392
      },
      "8411": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 392
      },
      "8412": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 392
      },
      "8413": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 392
      },
      "8414": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 392
      },
      "8415": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 392
      },
      "8416": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 392
      },
      "8417": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 392
      },
      "8418": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 392
      },
      "8419": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 392
      },
      "8420": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 392
      },
      "8421": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 392
      },
      "8422": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 392
      },
      "8423": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 392
      },
      "8424": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 392
      },
      "8425": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 392
      },
      "8426": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 392
      },
      "8427": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 392
      },
      "8428": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 392
      },
      "8429": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 392
      },
      "8430": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 392
      },
      "8431": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 392
      },
      "8432": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 392
      },
      "8433": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 392
      },
      "8434": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 392
      },
      "8435": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 392
      },
      "8436": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 392
      },
      "8437": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 392
      },
      "8438": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 392
      },
      "8439": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 392
      },
      "8440": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 392
      },
      "8441": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 392
      },
      "8442": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 392
      },
      "8443": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 392
      },
      "8444": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 392
      },
      "8445": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 392
      },
      "8446": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 392
      },
      "8447": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 392
      },
      "8448": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 392
      },
      "8449": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 392
      },
      "8450": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 392
      },
      "8451": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 392
      },
      "8452": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 392
      },
      "8453": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 392
      },
      "8454": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 392
      },
      "8455": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 392
      },
      "8456": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 392
      },
      "8457": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 392
      },
      "8458": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 392
      },
      "8459": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 392
      },
      "8460": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 392
      },
      "8461": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 392
      },
      "8462": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 393
      },
      "8463": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 393
      },
      "8464": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 393
      },
      "8465": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 393
      },
      "8466": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 393
      },
      "8467": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 393
      },
      "8468": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 393
      },
      "8469": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 393
      },
      "8470": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 393
      },
      "8471": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 393
      },
      "8472": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 393
      },
      "8473": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 393
      },
      "8474": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 393
      },
      "8475": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 393
      },
      "8476": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 393
      },
      "8477": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 393
      },
      "8478": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 393
      },
      "8479": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 393
      },
      "8480": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 393
      },
      "8481": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 393
      },
      "8482": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 393
      },
      "8483": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 393
      },
      "8484": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 393
      },
      "8485": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 393
      },
      "8486": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 393
      },
      "8487": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 393
      },
      "8488": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 393
      },
      "8489": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 393
      },
      "8490": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 393
      },
      "8491": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 393
      },
      "8492": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 393
      },
      "8493": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 393
      },
      "8494": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 393
      },
      "8495": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 393
      },
      "8496": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 393
      },
      "8497": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 393
      },
      "8498": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 393
      },
      "8499": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 393
      },
      "8500": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 393
      },
      "8501": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 393
      },
      "8502": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 393
      },
      "8503": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 393
      },
      "8504": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 393
      },
      "8505": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 393
      },
      "8506": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 393
      },
      "8507": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 393
      },
      "8508": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 393
      },
      "8509": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 393
      },
      "8510": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 393
      },
      "8511": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 393
      },
      "8512": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 393
      },
      "8513": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 393
      },
      "8514": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 393
      },
      "8515": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 393
      },
      "8516": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 393
      },
      "8517": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 393
      },
      "8518": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 394
      },
      "8519": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 394
      },
      "8520": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 394
      },
      "8521": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 394
      },
      "8522": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 394
      },
      "8523": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 394
      },
      "8524": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 394
      },
      "8525": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 394
      },
      "8526": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 394
      },
      "8527": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 394
      },
      "8528": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 394
      },
      "8529": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 394
      },
      "8530": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 394
      },
      "8531": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 394
      },
      "8532": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 394
      },
      "8533": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 394
      },
      "8534": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 394
      },
      "8535": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 394
      },
      "8536": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 394
      },
      "8537": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 394
      },
      "8538": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 394
      },
      "8539": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 394
      },
      "8540": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 394
      },
      "8541": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 394
      },
      "8542": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 394
      },
      "8543": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 394
      },
      "8544": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 394
      },
      "8545": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 394
      },
      "8546": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 394
      },
      "8547": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 394
      },
      "8548": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 394
      },
      "8549": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 394
      },
      "8550": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 394
      },
      "8551": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 394
      },
      "8552": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 394
      },
      "8553": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 394
      },
      "8554": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 394
      },
      "8555": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 394
      },
      "8556": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 394
      },
      "8557": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 394
      },
      "8558": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 394
      },
      "8559": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 394
      },
      "8560": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 394
      },
      "8561": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 394
      },
      "8562": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 394
      },
      "8563": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 394
      },
      "8564": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 394
      },
      "8565": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 394
      },
      "8566": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 394
      },
      "8567": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 394
      },
      "8568": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 394
      },
      "8569": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 394
      },
      "8570": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 394
      },
      "8571": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 394
      },
      "8572": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 394
      },
      "8573": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 394
      },
      "8574": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 395
      },
      "8575": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 395
      },
      "8576": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 395
      },
      "8577": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 395
      },
      "8578": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 395
      },
      "8579": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 395
      },
      "8580": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 395
      },
      "8581": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 395
      },
      "8582": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 395
      },
      "8583": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 395
      },
      "8584": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 395
      },
      "8585": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 395
      },
      "8586": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 395
      },
      "8587": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 395
      },
      "8588": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 395
      },
      "8589": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 395
      },
      "8590": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 395
      },
      "8591": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 395
      },
      "8592": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 395
      },
      "8593": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 395
      },
      "8594": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 395
      },
      "8595": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 395
      },
      "8596": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 395
      },
      "8597": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 395
      },
      "8598": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 395
      },
      "8599": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 395
      },
      "8600": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 395
      },
      "8601": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 395
      },
      "8602": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 395
      },
      "8603": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 395
      },
      "8604": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 395
      },
      "8605": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 395
      },
      "8606": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 395
      },
      "8607": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 395
      },
      "8608": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 395
      },
      "8609": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 395
      },
      "8610": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 395
      },
      "8611": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 395
      },
      "8612": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 395
      },
      "8613": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 395
      },
      "8614": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 395
      },
      "8615": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 395
      },
      "8616": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 395
      },
      "8617": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 395
      },
      "8618": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 395
      },
      "8619": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 395
      },
      "8620": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 395
      },
      "8621": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 395
      },
      "8622": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 395
      },
      "8623": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 395
      },
      "8624": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 395
      },
      "8625": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 395
      },
      "8626": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 395
      },
      "8627": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 395
      },
      "8628": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 395
      },
      "8629": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 395
      },
      "8630": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 396
      },
      "8631": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 396
      },
      "8632": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 396
      },
      "8633": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 396
      },
      "8634": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 396
      },
      "8635": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 396
      },
      "8636": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 396
      },
      "8637": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 396
      },
      "8638": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 396
      },
      "8639": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 396
      },
      "8640": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 396
      },
      "8641": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 396
      },
      "8642": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 396
      },
      "8643": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 396
      },
      "8644": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 396
      },
      "8645": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 396
      },
      "8646": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 396
      },
      "8647": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 396
      },
      "8648": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 396
      },
      "8649": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 396
      },
      "8650": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 396
      },
      "8651": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 396
      },
      "8652": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 396
      },
      "8653": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 396
      },
      "8654": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 396
      },
      "8655": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 396
      },
      "8656": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 396
      },
      "8657": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 396
      },
      "8658": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 396
      },
      "8659": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 396
      },
      "8660": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 396
      },
      "8661": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 396
      },
      "8662": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 396
      },
      "8663": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 396
      },
      "8664": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 396
      },
      "8665": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 396
      },
      "8666": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 396
      },
      "8667": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 396
      },
      "8668": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 396
      },
      "8669": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 396
      },
      "8670": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 396
      },
      "8671": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 396
      },
      "8672": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 396
      },
      "8673": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 396
      },
      "8674": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 396
      },
      "8675": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 396
      },
      "8676": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 396
      },
      "8677": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 396
      },
      "8678": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 396
      },
      "8679": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 396
      },
      "8680": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 396
      },
      "8681": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 396
      },
      "8682": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 396
      },
      "8683": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 396
      },
      "8684": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 396
      },
      "8685": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 396
      },
      "8686": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 397
      },
      "8687": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 397
      },
      "8688": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 397
      },
      "8689": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 397
      },
      "8690": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 397
      },
      "8691": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 397
      },
      "8692": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 397
      },
      "8693": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 397
      },
      "8694": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 397
      },
      "8695": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 397
      },
      "8696": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 397
      },
      "8697": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 397
      },
      "8698": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 397
      },
      "8699": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 397
      },
      "8700": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 397
      },
      "8701": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 397
      },
      "8702": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 397
      },
      "8703": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 397
      },
      "8704": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 397
      },
      "8705": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 397
      },
      "8706": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 397
      },
      "8707": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 397
      },
      "8708": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 397
      },
      "8709": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 397
      },
      "8710": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 397
      },
      "8711": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 397
      },
      "8712": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 397
      },
      "8713": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 397
      },
      "8714": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 397
      },
      "8715": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 397
      },
      "8716": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 397
      },
      "8717": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 397
      },
      "8718": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 397
      },
      "8719": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 397
      },
      "8720": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 397
      },
      "8721": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 397
      },
      "8722": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 397
      },
      "8723": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 397
      },
      "8724": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 397
      },
      "8725": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 397
      },
      "8726": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 397
      },
      "8727": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 397
      },
      "8728": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 397
      },
      "8729": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 397
      },
      "8730": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 397
      },
      "8731": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 397
      },
      "8732": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 397
      },
      "8733": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 397
      },
      "8734": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 397
      },
      "8735": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 397
      },
      "8736": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 397
      },
      "8737": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 397
      },
      "8738": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 397
      },
      "8739": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 397
      },
      "8740": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 397
      },
      "8741": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 397
      },
      "8742": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 398
      },
      "8743": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 398
      },
      "8744": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 398
      },
      "8745": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 398
      },
      "8746": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 398
      },
      "8747": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 398
      },
      "8748": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 398
      },
      "8749": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 398
      },
      "8750": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 398
      },
      "8751": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 398
      },
      "8752": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 398
      },
      "8753": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 398
      },
      "8754": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 398
      },
      "8755": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 398
      },
      "8756": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 398
      },
      "8757": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 398
      },
      "8758": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 398
      },
      "8759": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 398
      },
      "8760": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 398
      },
      "8761": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 398
      },
      "8762": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 398
      },
      "8763": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 398
      },
      "8764": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 398
      },
      "8765": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 398
      },
      "8766": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 398
      },
      "8767": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 398
      },
      "8768": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 398
      },
      "8769": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 398
      },
      "8770": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 398
      },
      "8771": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 398
      },
      "8772": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 398
      },
      "8773": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 398
      },
      "8774": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 398
      },
      "8775": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 398
      },
      "8776": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 398
      },
      "8777": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 398
      },
      "8778": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 398
      },
      "8779": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 398
      },
      "8780": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 398
      },
      "8781": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 398
      },
      "8782": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 398
      },
      "8783": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 398
      },
      "8784": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 398
      },
      "8785": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 398
      },
      "8786": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 398
      },
      "8787": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 398
      },
      "8788": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 398
      },
      "8789": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 398
      },
      "8790": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 398
      },
      "8791": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 398
      },
      "8792": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 398
      },
      "8793": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 398
      },
      "8794": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 398
      },
      "8795": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 398
      },
      "8796": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 398
      },
      "8797": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 398
      },
      "8798": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 399
      },
      "8799": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 399
      },
      "8800": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 399
      },
      "8801": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 399
      },
      "8802": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 399
      },
      "8803": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 399
      },
      "8804": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 399
      },
      "8805": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 399
      },
      "8806": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 399
      },
      "8807": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 399
      },
      "8808": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 399
      },
      "8809": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 399
      },
      "8810": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 399
      },
      "8811": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 399
      },
      "8812": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 399
      },
      "8813": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 399
      },
      "8814": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 399
      },
      "8815": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 399
      },
      "8816": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 399
      },
      "8817": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 399
      },
      "8818": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 399
      },
      "8819": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 399
      },
      "8820": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 399
      },
      "8821": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 399
      },
      "8822": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 399
      },
      "8823": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 399
      },
      "8824": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 399
      },
      "8825": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 399
      },
      "8826": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 399
      },
      "8827": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 399
      },
      "8828": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 399
      },
      "8829": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 399
      },
      "8830": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 399
      },
      "8831": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 399
      },
      "8832": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 399
      },
      "8833": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 399
      },
      "8834": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 399
      },
      "8835": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 399
      },
      "8836": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 399
      },
      "8837": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 399
      },
      "8838": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 399
      },
      "8839": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 399
      },
      "8840": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 399
      },
      "8841": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 399
      },
      "8842": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 399
      },
      "8843": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 399
      },
      "8844": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 399
      },
      "8845": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 399
      },
      "8846": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 399
      },
      "8847": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 399
      },
      "8848": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 399
      },
      "8849": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 399
      },
      "8850": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 399
      },
      "8851": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 399
      },
      "8852": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 399
      },
      "8853": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 399
      },
      "8854": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 400
      },
      "8855": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 400
      },
      "8856": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 400
      },
      "8857": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 400
      },
      "8858": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 400
      },
      "8859": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 400
      },
      "8860": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 400
      },
      "8861": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 400
      },
      "8862": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 400
      },
      "8863": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 400
      },
      "8864": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 400
      },
      "8865": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 400
      },
      "8866": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 400
      },
      "8867": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 400
      },
      "8868": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 400
      },
      "8869": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 400
      },
      "8870": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 400
      },
      "8871": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 400
      },
      "8872": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 400
      },
      "8873": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 400
      },
      "8874": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 400
      },
      "8875": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 400
      },
      "8876": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 400
      },
      "8877": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 400
      },
      "8878": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 400
      },
      "8879": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 400
      },
      "8880": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 400
      },
      "8881": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 400
      },
      "8882": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 400
      },
      "8883": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 400
      },
      "8884": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 400
      },
      "8885": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 400
      },
      "8886": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 400
      },
      "8887": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 400
      },
      "8888": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 400
      },
      "8889": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 400
      },
      "8890": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 400
      },
      "8891": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 400
      },
      "8892": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 400
      },
      "8893": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 400
      },
      "8894": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 400
      },
      "8895": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 400
      },
      "8896": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 400
      },
      "8897": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 400
      },
      "8898": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 400
      },
      "8899": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 400
      },
      "8900": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 400
      },
      "8901": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 400
      },
      "8902": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 400
      },
      "8903": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 400
      },
      "8904": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 400
      },
      "8905": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 400
      },
      "8906": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 400
      },
      "8907": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 400
      },
      "8908": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 400
      },
      "8909": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 400
      },
      "8910": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 401
      },
      "8911": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 401
      },
      "8912": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 401
      },
      "8913": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 401
      },
      "8914": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 401
      },
      "8915": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 401
      },
      "8916": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 401
      },
      "8917": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 401
      },
      "8918": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 401
      },
      "8919": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 401
      },
      "8920": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 401
      },
      "8921": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 401
      },
      "8922": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 401
      },
      "8923": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 401
      },
      "8924": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 401
      },
      "8925": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 401
      },
      "8926": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 401
      },
      "8927": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 401
      },
      "8928": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 401
      },
      "8929": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 401
      },
      "8930": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 401
      },
      "8931": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 401
      },
      "8932": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 401
      },
      "8933": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 401
      },
      "8934": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 401
      },
      "8935": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 401
      },
      "8936": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 401
      },
      "8937": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 401
      },
      "8938": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 401
      },
      "8939": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 401
      },
      "8940": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 401
      },
      "8941": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 401
      },
      "8942": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 401
      },
      "8943": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 401
      },
      "8944": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 401
      },
      "8945": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 401
      },
      "8946": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 401
      },
      "8947": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 401
      },
      "8948": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 401
      },
      "8949": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 401
      },
      "8950": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 401
      },
      "8951": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 401
      },
      "8952": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 401
      },
      "8953": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 401
      },
      "8954": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 401
      },
      "8955": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 401
      },
      "8956": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 401
      },
      "8957": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 401
      },
      "8958": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 401
      },
      "8959": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 401
      },
      "8960": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 401
      },
      "8961": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 401
      },
      "8962": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 401
      },
      "8963": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 401
      },
      "8964": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 401
      },
      "8965": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 401
      },
      "8966": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 402
      },
      "8967": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 402
      },
      "8968": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 402
      },
      "8969": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 402
      },
      "8970": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 402
      },
      "8971": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 402
      },
      "8972": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 402
      },
      "8973": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 402
      },
      "8974": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 402
      },
      "8975": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 402
      },
      "8976": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 402
      },
      "8977": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 402
      },
      "8978": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 402
      },
      "8979": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 402
      },
      "8980": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 402
      },
      "8981": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 402
      },
      "8982": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 402
      },
      "8983": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 402
      },
      "8984": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 402
      },
      "8985": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 402
      },
      "8986": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 402
      },
      "8987": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 402
      },
      "8988": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 402
      },
      "8989": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 402
      },
      "8990": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 402
      },
      "8991": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 402
      },
      "8992": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 402
      },
      "8993": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 402
      },
      "8994": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 402
      },
      "8995": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 402
      },
      "8996": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 402
      },
      "8997": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 402
      },
      "8998": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 402
      },
      "8999": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 402
      },
      "9000": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 402
      },
      "9001": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 402
      },
      "9002": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 402
      },
      "9003": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 402
      },
      "9004": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 402
      },
      "9005": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 402
      },
      "9006": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 402
      },
      "9007": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 402
      },
      "9008": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 402
      },
      "9009": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 402
      },
      "9010": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 402
      },
      "9011": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 402
      },
      "9012": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 402
      },
      "9013": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 402
      },
      "9014": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 402
      },
      "9015": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 402
      },
      "9016": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 402
      },
      "9017": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 402
      },
      "9018": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 402
      },
      "9019": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 402
      },
      "9020": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 402
      },
      "9021": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 402
      },
      "9022": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 403
      },
      "9023": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 403
      },
      "9024": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 403
      },
      "9025": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 403
      },
      "9026": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 403
      },
      "9027": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 403
      },
      "9028": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 403
      },
      "9029": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 403
      },
      "9030": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 403
      },
      "9031": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 403
      },
      "9032": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 403
      },
      "9033": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 403
      },
      "9034": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 403
      },
      "9035": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 403
      },
      "9036": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 403
      },
      "9037": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 403
      },
      "9038": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 403
      },
      "9039": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 403
      },
      "9040": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 403
      },
      "9041": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 403
      },
      "9042": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 403
      },
      "9043": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 403
      },
      "9044": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 403
      },
      "9045": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 403
      },
      "9046": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 403
      },
      "9047": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 403
      },
      "9048": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 403
      },
      "9049": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 403
      },
      "9050": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 403
      },
      "9051": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 403
      },
      "9052": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 403
      },
      "9053": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 403
      },
      "9054": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 403
      },
      "9055": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 403
      },
      "9056": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 403
      },
      "9057": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 403
      },
      "9058": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 403
      },
      "9059": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 403
      },
      "9060": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 403
      },
      "9061": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 403
      },
      "9062": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 403
      },
      "9063": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 403
      },
      "9064": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 403
      },
      "9065": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 403
      },
      "9066": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 403
      },
      "9067": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 403
      },
      "9068": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 403
      },
      "9069": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 403
      },
      "9070": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 403
      },
      "9071": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 403
      },
      "9072": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 403
      },
      "9073": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 403
      },
      "9074": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 403
      },
      "9075": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 403
      },
      "9076": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 403
      },
      "9077": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 403
      },
      "9078": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 404
      },
      "9079": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 404
      },
      "9080": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 404
      },
      "9081": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 404
      },
      "9082": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 404
      },
      "9083": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 404
      },
      "9084": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 404
      },
      "9085": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 404
      },
      "9086": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 404
      },
      "9087": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 404
      },
      "9088": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 404
      },
      "9089": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 404
      },
      "9090": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 404
      },
      "9091": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 404
      },
      "9092": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 404
      },
      "9093": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 404
      },
      "9094": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 404
      },
      "9095": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 404
      },
      "9096": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 404
      },
      "9097": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 404
      },
      "9098": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 404
      },
      "9099": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 404
      },
      "9100": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 404
      },
      "9101": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 404
      },
      "9102": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 404
      },
      "9103": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 404
      },
      "9104": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 404
      },
      "9105": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 404
      },
      "9106": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 404
      },
      "9107": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 404
      },
      "9108": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 404
      },
      "9109": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 404
      },
      "9110": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 404
      },
      "9111": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 404
      },
      "9112": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 404
      },
      "9113": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 404
      },
      "9114": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 404
      },
      "9115": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 404
      },
      "9116": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 404
      },
      "9117": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 404
      },
      "9118": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 404
      },
      "9119": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 404
      },
      "9120": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 404
      },
      "9121": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 404
      },
      "9122": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 404
      },
      "9123": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 404
      },
      "9124": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 404
      },
      "9125": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 404
      },
      "9126": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 404
      },
      "9127": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 404
      },
      "9128": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 404
      },
      "9129": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 404
      },
      "9130": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 404
      },
      "9131": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 404
      },
      "9132": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 404
      },
      "9133": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 404
      },
      "9134": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 405
      },
      "9135": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 405
      },
      "9136": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 405
      },
      "9137": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 405
      },
      "9138": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 405
      },
      "9139": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 405
      },
      "9140": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 405
      },
      "9141": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 405
      },
      "9142": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 405
      },
      "9143": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 405
      },
      "9144": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 405
      },
      "9145": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 405
      },
      "9146": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 405
      },
      "9147": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 405
      },
      "9148": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 405
      },
      "9149": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 405
      },
      "9150": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 405
      },
      "9151": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 405
      },
      "9152": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 405
      },
      "9153": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 405
      },
      "9154": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 405
      },
      "9155": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 405
      },
      "9156": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 405
      },
      "9157": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 405
      },
      "9158": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 405
      },
      "9159": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 405
      },
      "9160": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 405
      },
      "9161": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 405
      },
      "9162": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 405
      },
      "9163": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 405
      },
      "9164": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 405
      },
      "9165": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 405
      },
      "9166": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 405
      },
      "9167": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 405
      },
      "9168": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 405
      },
      "9169": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 405
      },
      "9170": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 405
      },
      "9171": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 405
      },
      "9172": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 405
      },
      "9173": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 405
      },
      "9174": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 405
      },
      "9175": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 405
      },
      "9176": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 405
      },
      "9177": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 405
      },
      "9178": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 405
      },
      "9179": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 405
      },
      "9180": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 405
      },
      "9181": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 405
      },
      "9182": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 405
      },
      "9183": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 405
      },
      "9184": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 405
      },
      "9185": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 405
      },
      "9186": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 405
      },
      "9187": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 405
      },
      "9188": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 405
      },
      "9189": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 405
      },
      "9190": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 406
      },
      "9191": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 406
      },
      "9192": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 406
      },
      "9193": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 406
      },
      "9194": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 406
      },
      "9195": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 406
      },
      "9196": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 406
      },
      "9197": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 406
      },
      "9198": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 406
      },
      "9199": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 406
      },
      "9200": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 406
      },
      "9201": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 406
      },
      "9202": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 406
      },
      "9203": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 406
      },
      "9204": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 406
      },
      "9205": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 406
      },
      "9206": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 406
      },
      "9207": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 406
      },
      "9208": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 406
      },
      "9209": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 406
      },
      "9210": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 406
      },
      "9211": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 406
      },
      "9212": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 406
      },
      "9213": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 406
      },
      "9214": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 406
      },
      "9215": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 406
      },
      "9216": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 406
      },
      "9217": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 406
      },
      "9218": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 406
      },
      "9219": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 406
      },
      "9220": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 406
      },
      "9221": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 406
      },
      "9222": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 406
      },
      "9223": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 406
      },
      "9224": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 406
      },
      "9225": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 406
      },
      "9226": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 406
      },
      "9227": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 406
      },
      "9228": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 406
      },
      "9229": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 406
      },
      "9230": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 406
      },
      "9231": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 406
      },
      "9232": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 406
      },
      "9233": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 406
      },
      "9234": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 406
      },
      "9235": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 406
      },
      "9236": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 406
      },
      "9237": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 406
      },
      "9238": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 406
      },
      "9239": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 406
      },
      "9240": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 406
      },
      "9241": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 406
      },
      "9242": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 406
      },
      "9243": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 406
      },
      "9244": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 406
      },
      "9245": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 406
      },
      "9246": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 407
      },
      "9247": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 407
      },
      "9248": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 407
      },
      "9249": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 407
      },
      "9250": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 407
      },
      "9251": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 407
      },
      "9252": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 407
      },
      "9253": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 407
      },
      "9254": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 407
      },
      "9255": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 407
      },
      "9256": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 407
      },
      "9257": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 407
      },
      "9258": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 407
      },
      "9259": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 407
      },
      "9260": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 407
      },
      "9261": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 407
      },
      "9262": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 407
      },
      "9263": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 407
      },
      "9264": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 407
      },
      "9265": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 407
      },
      "9266": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 407
      },
      "9267": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 407
      },
      "9268": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 407
      },
      "9269": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 407
      },
      "9270": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 407
      },
      "9271": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 407
      },
      "9272": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 407
      },
      "9273": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 407
      },
      "9274": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 407
      },
      "9275": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 407
      },
      "9276": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 407
      },
      "9277": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 407
      },
      "9278": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 407
      },
      "9279": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 407
      },
      "9280": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 407
      },
      "9281": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 407
      },
      "9282": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 407
      },
      "9283": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 407
      },
      "9284": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 407
      },
      "9285": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 407
      },
      "9286": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 407
      },
      "9287": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 407
      },
      "9288": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 407
      },
      "9289": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 407
      },
      "9290": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 407
      },
      "9291": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 407
      },
      "9292": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 407
      },
      "9293": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 407
      },
      "9294": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 407
      },
      "9295": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 407
      },
      "9296": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 407
      },
      "9297": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 407
      },
      "9298": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 407
      },
      "9299": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 407
      },
      "9300": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 407
      },
      "9301": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 407
      },
      "9302": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 408
      },
      "9303": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 408
      },
      "9304": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 408
      },
      "9305": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 408
      },
      "9306": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 408
      },
      "9307": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 408
      },
      "9308": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 408
      },
      "9309": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 408
      },
      "9310": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 408
      },
      "9311": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 408
      },
      "9312": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 408
      },
      "9313": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 408
      },
      "9314": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 408
      },
      "9315": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 408
      },
      "9316": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 408
      },
      "9317": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 408
      },
      "9318": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 408
      },
      "9319": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 408
      },
      "9320": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 408
      },
      "9321": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 408
      },
      "9322": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 408
      },
      "9323": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 408
      },
      "9324": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 408
      },
      "9325": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 408
      },
      "9326": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 408
      },
      "9327": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 408
      },
      "9328": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 408
      },
      "9329": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 408
      },
      "9330": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 408
      },
      "9331": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 408
      },
      "9332": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 408
      },
      "9333": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 408
      },
      "9334": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 408
      },
      "9335": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 408
      },
      "9336": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 408
      },
      "9337": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 408
      },
      "9338": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 408
      },
      "9339": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 408
      },
      "9340": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 408
      },
      "9341": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 408
      },
      "9342": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 408
      },
      "9343": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 408
      },
      "9344": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 408
      },
      "9345": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 408
      },
      "9346": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 408
      },
      "9347": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 408
      },
      "9348": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 408
      },
      "9349": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 408
      },
      "9350": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 408
      },
      "9351": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 408
      },
      "9352": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 408
      },
      "9353": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 408
      },
      "9354": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 408
      },
      "9355": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 408
      },
      "9356": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 408
      },
      "9357": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 408
      },
      "9358": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 409
      },
      "9359": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 409
      },
      "9360": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 409
      },
      "9361": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 409
      },
      "9362": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 409
      },
      "9363": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 409
      },
      "9364": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 409
      },
      "9365": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 409
      },
      "9366": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 409
      },
      "9367": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 409
      },
      "9368": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 409
      },
      "9369": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 409
      },
      "9370": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 409
      },
      "9371": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 409
      },
      "9372": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 409
      },
      "9373": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 409
      },
      "9374": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 409
      },
      "9375": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 409
      },
      "9376": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 409
      },
      "9377": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 409
      },
      "9378": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 409
      },
      "9379": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 409
      },
      "9380": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 409
      },
      "9381": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 409
      },
      "9382": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 409
      },
      "9383": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 409
      },
      "9384": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 409
      },
      "9385": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 409
      },
      "9386": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 409
      },
      "9387": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 409
      },
      "9388": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 409
      },
      "9389": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 409
      },
      "9390": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 409
      },
      "9391": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 409
      },
      "9392": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 409
      },
      "9393": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 409
      },
      "9394": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 409
      },
      "9395": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 409
      },
      "9396": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 409
      },
      "9397": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 409
      },
      "9398": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 409
      },
      "9399": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 409
      },
      "9400": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 409
      },
      "9401": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 409
      },
      "9402": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 409
      },
      "9403": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 409
      },
      "9404": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 409
      },
      "9405": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 409
      },
      "9406": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 409
      },
      "9407": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 409
      },
      "9408": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 409
      },
      "9409": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 409
      },
      "9410": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 409
      },
      "9411": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 409
      },
      "9412": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 409
      },
      "9413": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 409
      },
      "9414": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 410
      },
      "9415": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 410
      },
      "9416": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 410
      },
      "9417": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 410
      },
      "9418": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 410
      },
      "9419": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 410
      },
      "9420": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 410
      },
      "9421": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 410
      },
      "9422": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 410
      },
      "9423": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 410
      },
      "9424": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 410
      },
      "9425": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 410
      },
      "9426": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 410
      },
      "9427": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 410
      },
      "9428": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 410
      },
      "9429": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 410
      },
      "9430": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 410
      },
      "9431": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 410
      },
      "9432": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 410
      },
      "9433": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 410
      },
      "9434": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 410
      },
      "9435": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 410
      },
      "9436": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 410
      },
      "9437": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 410
      },
      "9438": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 410
      },
      "9439": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 410
      },
      "9440": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 410
      },
      "9441": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 410
      },
      "9442": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 410
      },
      "9443": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 410
      },
      "9444": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 410
      },
      "9445": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 410
      },
      "9446": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 410
      },
      "9447": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 410
      },
      "9448": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 410
      },
      "9449": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 410
      },
      "9450": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 410
      },
      "9451": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 410
      },
      "9452": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 410
      },
      "9453": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 410
      },
      "9454": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 410
      },
      "9455": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 410
      },
      "9456": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 410
      },
      "9457": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 410
      },
      "9458": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 410
      },
      "9459": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 410
      },
      "9460": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 410
      },
      "9461": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 410
      },
      "9462": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 410
      },
      "9463": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 410
      },
      "9464": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 410
      },
      "9465": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 410
      },
      "9466": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 410
      },
      "9467": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 410
      },
      "9468": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 410
      },
      "9469": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 410
      },
      "9470": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 411
      },
      "9471": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 411
      },
      "9472": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 411
      },
      "9473": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 411
      },
      "9474": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 411
      },
      "9475": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 411
      },
      "9476": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 411
      },
      "9477": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 411
      },
      "9478": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 411
      },
      "9479": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 411
      },
      "9480": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 411
      },
      "9481": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 411
      },
      "9482": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 411
      },
      "9483": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 411
      },
      "9484": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 411
      },
      "9485": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 411
      },
      "9486": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 411
      },
      "9487": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 411
      },
      "9488": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 411
      },
      "9489": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 411
      },
      "9490": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 411
      },
      "9491": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 411
      },
      "9492": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 411
      },
      "9493": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 411
      },
      "9494": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 411
      },
      "9495": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 411
      },
      "9496": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 411
      },
      "9497": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 411
      },
      "9498": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 411
      },
      "9499": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 411
      },
      "9500": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 411
      },
      "9501": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 411
      },
      "9502": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 411
      },
      "9503": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 411
      },
      "9504": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 411
      },
      "9505": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 411
      },
      "9506": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 411
      },
      "9507": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 411
      },
      "9508": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 411
      },
      "9509": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 411
      },
      "9510": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 411
      },
      "9511": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 411
      },
      "9512": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 411
      },
      "9513": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 411
      },
      "9514": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 411
      },
      "9515": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 411
      },
      "9516": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 411
      },
      "9517": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 411
      },
      "9518": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 411
      },
      "9519": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 411
      },
      "9520": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 411
      },
      "9521": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 411
      },
      "9522": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 411
      },
      "9523": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 411
      },
      "9524": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 411
      },
      "9525": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 411
      },
      "9526": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 412
      },
      "9527": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 412
      },
      "9528": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 412
      },
      "9529": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 412
      },
      "9530": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 412
      },
      "9531": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 412
      },
      "9532": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 412
      },
      "9533": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 412
      },
      "9534": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 412
      },
      "9535": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 412
      },
      "9536": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 412
      },
      "9537": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 412
      },
      "9538": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 412
      },
      "9539": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 412
      },
      "9540": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 412
      },
      "9541": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 412
      },
      "9542": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 412
      },
      "9543": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 412
      },
      "9544": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 412
      },
      "9545": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 412
      },
      "9546": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 412
      },
      "9547": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 412
      },
      "9548": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 412
      },
      "9549": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 412
      },
      "9550": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 412
      },
      "9551": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 412
      },
      "9552": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 412
      },
      "9553": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 412
      },
      "9554": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 412
      },
      "9555": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 412
      },
      "9556": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 412
      },
      "9557": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 412
      },
      "9558": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 412
      },
      "9559": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 412
      },
      "9560": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 412
      },
      "9561": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 412
      },
      "9562": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 412
      },
      "9563": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 412
      },
      "9564": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 412
      },
      "9565": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 412
      },
      "9566": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 412
      },
      "9567": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 412
      },
      "9568": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 412
      },
      "9569": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 412
      },
      "9570": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 412
      },
      "9571": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 412
      },
      "9572": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 412
      },
      "9573": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 412
      },
      "9574": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 412
      },
      "9575": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 412
      },
      "9576": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 412
      },
      "9577": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 412
      },
      "9578": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 412
      },
      "9579": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 412
      },
      "9580": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 412
      },
      "9581": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 412
      },
      "9582": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 413
      },
      "9583": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 413
      },
      "9584": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 413
      },
      "9585": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 413
      },
      "9586": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 413
      },
      "9587": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 413
      },
      "9588": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 413
      },
      "9589": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 413
      },
      "9590": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 413
      },
      "9591": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 413
      },
      "9592": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 413
      },
      "9593": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 413
      },
      "9594": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 413
      },
      "9595": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 413
      },
      "9596": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 413
      },
      "9597": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 413
      },
      "9598": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 413
      },
      "9599": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 413
      },
      "9600": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 413
      },
      "9601": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 413
      },
      "9602": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 413
      },
      "9603": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 413
      },
      "9604": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 413
      },
      "9605": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 413
      },
      "9606": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 413
      },
      "9607": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 413
      },
      "9608": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 413
      },
      "9609": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 413
      },
      "9610": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 413
      },
      "9611": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 413
      },
      "9612": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 413
      },
      "9613": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 413
      },
      "9614": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 413
      },
      "9615": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 413
      },
      "9616": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 413
      },
      "9617": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 413
      },
      "9618": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 413
      },
      "9619": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 413
      },
      "9620": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 413
      },
      "9621": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 413
      },
      "9622": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 413
      },
      "9623": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 413
      },
      "9624": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 413
      },
      "9625": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 413
      },
      "9626": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 413
      },
      "9627": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 413
      },
      "9628": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 413
      },
      "9629": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 413
      },
      "9630": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 413
      },
      "9631": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 413
      },
      "9632": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 413
      },
      "9633": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 413
      },
      "9634": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 413
      },
      "9635": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 413
      },
      "9636": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 413
      },
      "9637": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 413
      },
      "9638": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 414
      },
      "9639": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 414
      },
      "9640": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 414
      },
      "9641": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 414
      },
      "9642": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 414
      },
      "9643": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 414
      },
      "9644": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 414
      },
      "9645": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 414
      },
      "9646": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 414
      },
      "9647": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 414
      },
      "9648": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 414
      },
      "9649": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 414
      },
      "9650": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 414
      },
      "9651": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 414
      },
      "9652": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 414
      },
      "9653": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 414
      },
      "9654": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 414
      },
      "9655": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 414
      },
      "9656": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 414
      },
      "9657": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 414
      },
      "9658": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 414
      },
      "9659": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 414
      },
      "9660": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 414
      },
      "9661": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 414
      },
      "9662": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 414
      },
      "9663": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 414
      },
      "9664": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 414
      },
      "9665": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 414
      },
      "9666": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 414
      },
      "9667": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 414
      },
      "9668": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 414
      },
      "9669": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 414
      },
      "9670": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 414
      },
      "9671": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 414
      },
      "9672": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 414
      },
      "9673": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 414
      },
      "9674": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 414
      },
      "9675": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 414
      },
      "9676": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 414
      },
      "9677": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 414
      },
      "9678": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 414
      },
      "9679": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 414
      },
      "9680": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 414
      },
      "9681": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 414
      },
      "9682": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 414
      },
      "9683": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 414
      },
      "9684": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 414
      },
      "9685": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 414
      },
      "9686": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 414
      },
      "9687": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 414
      },
      "9688": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 414
      },
      "9689": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 414
      },
      "9690": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 414
      },
      "9691": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 414
      },
      "9692": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 414
      },
      "9693": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 414
      },
      "9694": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 415
      },
      "9695": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 415
      },
      "9696": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 415
      },
      "9697": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 415
      },
      "9698": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 415
      },
      "9699": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 415
      },
      "9700": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 415
      },
      "9701": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 415
      },
      "9702": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 415
      },
      "9703": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 415
      },
      "9704": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 415
      },
      "9705": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 415
      },
      "9706": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 415
      },
      "9707": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 415
      },
      "9708": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 415
      },
      "9709": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 415
      },
      "9710": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 415
      },
      "9711": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 415
      },
      "9712": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 415
      },
      "9713": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 415
      },
      "9714": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 415
      },
      "9715": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 415
      },
      "9716": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 415
      },
      "9717": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 415
      },
      "9718": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 415
      },
      "9719": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 415
      },
      "9720": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 415
      },
      "9721": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 415
      },
      "9722": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 415
      },
      "9723": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 415
      },
      "9724": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 415
      },
      "9725": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 415
      },
      "9726": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 415
      },
      "9727": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 415
      },
      "9728": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 415
      },
      "9729": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 415
      },
      "9730": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 415
      },
      "9731": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 415
      },
      "9732": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 415
      },
      "9733": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 415
      },
      "9734": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 415
      },
      "9735": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 415
      },
      "9736": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 415
      },
      "9737": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 415
      },
      "9738": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 415
      },
      "9739": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 415
      },
      "9740": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 415
      },
      "9741": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 415
      },
      "9742": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 415
      },
      "9743": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 415
      },
      "9744": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 415
      },
      "9745": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 415
      },
      "9746": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 415
      },
      "9747": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 415
      },
      "9748": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 415
      },
      "9749": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 415
      },
      "10254": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 425
      },
      "10255": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 426
      },
      "10256": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 426
      },
      "10257": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 426
      },
      "10258": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 426
      },
      "10259": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 426
      },
      "10260": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 426
      },
      "10261": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 426
      },
      "10262": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 426
      },
      "10263": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 426
      },
      "10264": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 426
      },
      "10265": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 426
      },
      "10266": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 426
      },
      "10267": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 426
      },
      "10268": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 426
      },
      "10269": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 426
      },
      "10270": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 426
      },
      "10271": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 426
      },
      "10272": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 426
      },
      "10273": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 426
      },
      "10274": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 426
      },
      "10275": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 426
      },
      "10276": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 426
      },
      "10277": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 426
      },
      "10278": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 426
      },
      "10279": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 426
      },
      "10280": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 427
      },
      "10281": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 427
      },
      "10282": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 427
      },
      "10283": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 427
      },
      "10284": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 427
      },
      "10285": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 427
      },
      "10286": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 427
      },
      "10287": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 427
      },
      "10288": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 427
      },
      "10289": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 427
      },
      "10290": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 427
      },
      "10291": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 427
      },
      "10292": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 427
      },
      "10293": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 427
      },
      "10294": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 427
      },
      "10295": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 427
      },
      "10296": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 427
      },
      "10297": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 427
      },
      "10298": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 427
      },
      "10299": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 427
      },
      "10300": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 427
      },
      "10301": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 427
      },
      "10302": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 427
      },
      "10303": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 427
      },
      "10304": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 427
      },
      "10331": {
        "lookahead": {
          "type": "Token",
          "name": "AS"
        },
        "like": 429
      },
      "10332": {
        "lookahead": {
          "type": "Token",
          "name": "AS"
        },
        "like": 430
      },
      "10333": {
        "lookahead": {
          "type": "Token",
          "name": "AS"
        },
        "like": 431
      },
      "10334": {
        "lookahead": {
          "type": "Token",
          "name": "AS"
        },
        "like": 432
      },
      "10393": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 435
      },
      "10394": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 435
      },
      "10395": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 435
      },
      "10396": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 435
      },
      "10397": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 435
      },
      "10398": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 435
      },
      "10399": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 435
      },
      "10400": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 435
      },
      "10401": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 435
      },
      "10402": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 435
      },
      "10403": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 435
      },
      "10404": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 435
      },
      "10405": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 435
      },
      "10406": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 435
      },
      "10407": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 435
      },
      "10408": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 435
      },
      "10409": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 435
      },
      "10410": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 435
      },
      "10411": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 435
      },
      "10412": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 435
      },
      "10413": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 435
      },
      "10414": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 435
      },
      "10415": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 435
      },
      "10416": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 435
      },
      "10417": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 435
      },
      "10418": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 435
      },
      "10419": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 436
      },
      "10420": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 436
      },
      "10421": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 436
      },
      "10422": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 436
      },
      "10423": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 436
      },
      "10424": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 436
      },
      "10425": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 436
      },
      "10426": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 436
      },
      "10491": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 439
      },
      "10492": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 439
      },
      "10493": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 439
      },
      "10494": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 439
      },
      "10495": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 439
      },
      "10496": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 439
      },
      "10497": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 439
      },
      "10498": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 439
      },
      "10499": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 439
      },
      "10500": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 439
      },
      "10501": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 439
      },
      "10502": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 439
      },
      "10503": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 439
      },
      "10504": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 439
      },
      "10505": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 439
      },
      "10506": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 439
      },
      "10507": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 439
      },
      "10508": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 440
      },
      "10509": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 440
      },
      "10510": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 440
      },
      "10511": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 440
      },
      "10512": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 440
      },
      "10513": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 440
      },
      "10514": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 440
      },
      "10515": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 440
      },
      "10516": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 440
      },
      "10517": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 440
      },
      "10518": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 440
      },
      "10519": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 440
      },
      "10520": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 440
      },
      "10521": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 440
      },
      "10522": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 440
      },
      "10523": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 440
      },
      "10524": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 440
      },
      "10525": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 441
      },
      "10526": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 441
      },
      "10527": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 441
      },
      "10528": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 441
      },
      "10529": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 441
      },
      "10530": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 441
      },
      "10531": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 441
      },
      "10532": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 441
      },
      "10533": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 441
      },
      "10534": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 441
      },
      "10535": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 441
      },
      "10536": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 441
      },
      "10537": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 441
      },
      "10538": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 441
      },
      "10539": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 441
      },
      "10540": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 441
      },
      "10541": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 441
      },
      "10542": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 442
      },
      "10543": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 442
      },
      "10544": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 442
      },
      "10545": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 442
      },
      "10630": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 446
      },
      "10631": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 446
      },
      "10632": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 446
      },
      "10633": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 446
      },
      "10634": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 446
      },
      "10635": {
        "lookahead": {
          "type": "Token",
          "name": "DERIVING"
        },
        "like": 446
      },
      "10636": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 447
      },
      "10637": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 447
      },
      "10638": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 447
      },
      "10639": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 447
      },
      "10640": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 447
      },
      "10641": {
        "lookahead": {
          "type": "Token",
          "name": "DERIVING"
        },
        "like": 447
      },
      "10648": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 341
      },
      "10649": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 341
      },
      "10650": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 341
      },
      "10651": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 341
      },
      "10652": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 341
      },
      "10842": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 454
      },
      "10843": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 454
      },
      "10844": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 454
      },
      "10845": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 454
      },
      "10878": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 456
      },
      "10879": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 456
      },
      "10912": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 458
      },
      "10913": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 458
      },
      "10914": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 458
      },
      "10915": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 458
      },
      "10916": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 458
      },
      "10917": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 458
      },
      "10918": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 458
      },
      "10919": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 458
      },
      "10920": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 458
      },
      "10921": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 458
      },
      "10922": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 458
      },
      "10923": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 458
      },
      "10924": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 458
      },
      "10925": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 458
      },
      "10926": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 458
      },
      "10927": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 458
      },
      "10928": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 458
      },
      "10929": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 459
      },
      "10930": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 459
      },
      "10931": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 459
      },
      "10932": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 459
      },
      "10933": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 459
      },
      "10934": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 459
      },
      "10935": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 459
      },
      "10936": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 459
      },
      "10937": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 459
      },
      "10938": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 459
      },
      "10939": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 459
      },
      "10940": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 459
      },
      "10941": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 459
      },
      "10942": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 459
      },
      "10943": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 459
      },
      "10944": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 459
      },
      "10945": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 459
      },
      "10946": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 460
      },
      "10947": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 460
      },
      "10948": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 460
      },
      "10949": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 460
      },
      "10950": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 460
      },
      "10951": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 460
      },
      "10952": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 460
      },
      "10953": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 460
      },
      "10954": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 460
      },
      "10955": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 460
      },
      "10956": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 460
      },
      "10957": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 460
      },
      "10958": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 460
      },
      "10959": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 460
      },
      "10960": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 460
      },
      "10961": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 460
      },
      "10962": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 460
      },
      "10963": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 461
      },
      "10964": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 461
      },
      "10965": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 461
      },
      "10966": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 461
      },
      "10967": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 461
      },
      "10968": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 461
      },
      "10969": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 461
      },
      "10970": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 461
      },
      "10971": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 461
      },
      "10972": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 461
      },
      "10973": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 461
      },
      "10974": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 461
      },
      "10975": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 461
      },
      "10976": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 461
      },
      "10977": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 461
      },
      "10978": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 461
      },
      "10979": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 461
      },
      "10980": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 461
      },
      "10981": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 461
      },
      "10982": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 461
      },
      "10983": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 461
      },
      "10984": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 461
      },
      "10985": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 461
      },
      "10986": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 461
      },
      "10987": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 461
      },
      "10988": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 461
      },
      "10989": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 461
      },
      "10990": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 461
      },
      "10991": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 461
      },
      "10992": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 461
      },
      "10993": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 461
      },
      "10994": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 461
      },
      "10995": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 461
      },
      "10996": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 461
      },
      "10997": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 461
      },
      "10998": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 461
      },
      "10999": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 461
      },
      "11000": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 461
      },
      "11001": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 461
      },
      "11002": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 461
      },
      "11003": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 461
      },
      "11004": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 462
      },
      "11005": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 462
      },
      "11006": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 462
      },
      "11007": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 462
      },
      "11008": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 462
      },
      "11009": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 462
      },
      "11010": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 462
      },
      "11011": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 462
      },
      "11012": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 462
      },
      "11013": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 462
      },
      "11014": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 462
      },
      "11015": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 462
      },
      "11016": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 462
      },
      "11017": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 462
      },
      "11018": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 462
      },
      "11019": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 462
      },
      "11020": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 462
      },
      "11021": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 462
      },
      "11022": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 462
      },
      "11023": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 462
      },
      "11024": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 462
      },
      "11025": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 462
      },
      "11026": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 462
      },
      "11027": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 462
      },
      "11028": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 462
      },
      "11029": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 462
      },
      "11030": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 462
      },
      "11031": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 462
      },
      "11032": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 462
      },
      "11033": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 462
      },
      "11034": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 462
      },
      "11035": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 462
      },
      "11036": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 462
      },
      "11037": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 462
      },
      "11038": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 462
      },
      "11039": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 462
      },
      "11040": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 462
      },
      "11041": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 462
      },
      "11042": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 462
      },
      "11043": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 462
      },
      "11044": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 462
      },
      "11097": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 464
      },
      "11098": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 464
      },
      "11099": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 464
      },
      "11100": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 464
      },
      "11101": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 464
      },
      "11102": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 464
      },
      "11103": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 464
      },
      "11104": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 464
      },
      "11105": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 464
      },
      "11106": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 464
      },
      "11107": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 464
      },
      "11108": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 464
      },
      "11109": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 464
      },
      "11110": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 464
      },
      "11111": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 464
      },
      "11112": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 464
      },
      "11113": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 464
      },
      "11114": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 465
      },
      "11115": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 465
      },
      "11116": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 465
      },
      "11117": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 465
      },
      "11118": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 465
      },
      "11119": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 465
      },
      "11120": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 465
      },
      "11121": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 465
      },
      "11122": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 465
      },
      "11123": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 465
      },
      "11124": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 465
      },
      "11125": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 465
      },
      "11126": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 465
      },
      "11127": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 465
      },
      "11128": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 465
      },
      "11129": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 465
      },
      "11130": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 465
      },
      "11131": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 466
      },
      "11132": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 466
      },
      "11133": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 466
      },
      "11134": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 466
      },
      "11135": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 466
      },
      "11136": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 466
      },
      "11137": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 466
      },
      "11138": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 466
      },
      "11139": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 466
      },
      "11140": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 466
      },
      "11141": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 466
      },
      "11142": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 466
      },
      "11143": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 466
      },
      "11144": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 466
      },
      "11145": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 466
      },
      "11146": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 466
      },
      "11147": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 466
      },
      "11148": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 467
      },
      "11149": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 467
      },
      "11150": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 467
      },
      "11151": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 467
      },
      "11152": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 467
      },
      "11153": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 467
      },
      "11154": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 467
      },
      "11155": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 467
      },
      "11156": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 467
      },
      "11157": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 467
      },
      "11158": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 467
      },
      "11159": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 467
      },
      "11160": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 467
      },
      "11161": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 467
      },
      "11162": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 467
      },
      "11163": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 467
      },
      "11164": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 467
      },
      "11165": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 468
      },
      "11166": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 468
      },
      "11167": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 468
      },
      "11168": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 468
      },
      "11169": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 468
      },
      "11170": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 468
      },
      "11171": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 468
      },
      "11172": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 468
      },
      "11173": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 468
      },
      "11174": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 468
      },
      "11175": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 468
      },
      "11176": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 468
      },
      "11177": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 468
      },
      "11178": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 468
      },
      "11179": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 468
      },
      "11180": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 468
      },
      "11181": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 468
      },
      "11182": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 469
      },
      "11183": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 469
      },
      "11184": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 469
      },
      "11185": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 469
      },
      "11186": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 469
      },
      "11187": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 469
      },
      "11188": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 469
      },
      "11189": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 469
      },
      "11190": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 469
      },
      "11191": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 469
      },
      "11192": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 469
      },
      "11193": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 469
      },
      "11194": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 469
      },
      "11195": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 469
      },
      "11196": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 469
      },
      "11197": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 469
      },
      "11198": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 469
      },
      "11199": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 470
      },
      "11200": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 470
      },
      "11201": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 470
      },
      "11202": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 470
      },
      "11203": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 470
      },
      "11204": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 470
      },
      "11205": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 470
      },
      "11206": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 470
      },
      "11207": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 470
      },
      "11208": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 470
      },
      "11209": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 470
      },
      "11210": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 470
      },
      "11211": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 470
      },
      "11212": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 470
      },
      "11213": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 470
      },
      "11214": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 470
      },
      "11215": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 470
      },
      "11216": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 471
      },
      "11217": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 471
      },
      "11218": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 471
      },
      "11219": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 471
      },
      "11220": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 471
      },
      "11221": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 471
      },
      "11222": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 471
      },
      "11223": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 471
      },
      "11224": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 471
      },
      "11225": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 471
      },
      "11226": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 471
      },
      "11227": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 471
      },
      "11228": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 471
      },
      "11229": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 471
      },
      "11230": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 471
      },
      "11231": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 471
      },
      "11232": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 471
      },
      "11233": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 472
      },
      "11234": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 472
      },
      "11235": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 472
      },
      "11236": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 472
      },
      "11237": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 472
      },
      "11238": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 472
      },
      "11239": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 472
      },
      "11240": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 472
      },
      "11241": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 472
      },
      "11242": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 472
      },
      "11243": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 472
      },
      "11244": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 472
      },
      "11245": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 472
      },
      "11246": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 472
      },
      "11247": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 472
      },
      "11248": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 472
      },
      "11249": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 472
      },
      "11474": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 477
      },
      "11475": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 477
      },
      "11476": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 477
      },
      "11477": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 477
      },
      "11478": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 477
      },
      "11479": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 477
      },
      "11480": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 477
      },
      "11481": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 477
      },
      "11482": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 477
      },
      "11483": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 477
      },
      "11484": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 477
      },
      "11485": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 477
      },
      "11486": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 477
      },
      "11487": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 477
      },
      "11488": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 477
      },
      "11489": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 477
      },
      "11490": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 477
      },
      "11491": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 477
      },
      "11492": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 477
      },
      "11493": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 477
      },
      "11494": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 477
      },
      "11495": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 477
      },
      "11496": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 477
      },
      "11497": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 477
      },
      "11498": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 477
      },
      "11499": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 477
      },
      "11500": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 477
      },
      "11501": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 477
      },
      "11502": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 477
      },
      "11503": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 477
      },
      "11504": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 477
      },
      "11505": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 477
      },
      "11506": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 477
      },
      "11507": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 477
      },
      "11508": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 477
      },
      "11509": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 477
      },
      "11510": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 477
      },
      "11511": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 477
      },
      "11512": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 477
      },
      "11513": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 477
      },
      "11514": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 477
      },
      "11515": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 477
      },
      "11516": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 477
      },
      "11517": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 477
      },
      "11518": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 477
      },
      "11519": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 477
      },
      "11520": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 477
      },
      "11521": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 477
      },
      "11522": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 477
      },
      "11523": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 477
      },
      "11524": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 477
      },
      "11525": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 477
      },
      "11526": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 477
      },
      "11527": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 477
      },
      "11528": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 477
      },
      "11529": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 477
      },
      "11866": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 484
      },
      "11867": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 484
      },
      "11868": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 484
      },
      "11869": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 484
      },
      "11870": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 484
      },
      "11871": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 484
      },
      "11872": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 484
      },
      "11873": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 484
      },
      "11874": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 484
      },
      "11875": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 484
      },
      "11876": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 484
      },
      "11877": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 484
      },
      "11878": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 484
      },
      "11879": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 484
      },
      "11880": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 484
      },
      "11881": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 484
      },
      "11882": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 484
      },
      "11883": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 484
      },
      "11884": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 484
      },
      "11885": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 484
      },
      "11886": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 484
      },
      "11887": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 484
      },
      "11888": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 484
      },
      "11889": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 484
      },
      "11890": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 484
      },
      "11891": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 484
      },
      "11892": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 484
      },
      "11893": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 484
      },
      "11894": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 484
      },
      "11895": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 484
      },
      "11896": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 484
      },
      "11897": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 484
      },
      "11898": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 484
      },
      "11899": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 484
      },
      "11900": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 484
      },
      "11901": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 484
      },
      "11902": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 484
      },
      "11903": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 484
      },
      "11904": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 484
      },
      "11905": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 484
      },
      "11906": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 484
      },
      "11907": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 484
      },
      "11908": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 484
      },
      "11909": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 484
      },
      "11910": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 484
      },
      "11911": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 484
      },
      "11912": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 484
      },
      "11913": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 484
      },
      "11914": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 484
      },
      "11915": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 484
      },
      "11916": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 484
      },
      "11917": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 484
      },
      "11918": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 485
      },
      "11919": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 485
      },
      "11920": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 485
      },
      "11921": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 485
      },
      "11922": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 485
      },
      "11923": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 485
      },
      "11924": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 485
      },
      "11925": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 485
      },
      "11926": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 485
      },
      "11927": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 485
      },
      "11928": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 485
      },
      "11929": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 485
      },
      "11930": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 485
      },
      "11931": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 485
      },
      "11932": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 485
      },
      "11933": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 485
      },
      "11934": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 485
      },
      "11935": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 485
      },
      "11936": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 485
      },
      "11937": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 485
      },
      "11938": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 485
      },
      "11939": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 485
      },
      "11940": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 485
      },
      "11941": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 485
      },
      "11942": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 485
      },
      "11943": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 485
      },
      "11944": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 485
      },
      "11945": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 485
      },
      "11946": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 485
      },
      "11947": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 485
      },
      "11948": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 485
      },
      "11949": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 485
      },
      "11950": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 485
      },
      "11951": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 485
      },
      "11952": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 485
      },
      "11953": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 485
      },
      "11954": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 485
      },
      "11955": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 485
      },
      "11956": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 485
      },
      "11957": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 485
      },
      "11958": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 485
      },
      "11959": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 485
      },
      "11960": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 485
      },
      "11961": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 485
      },
      "11962": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 485
      },
      "11963": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 485
      },
      "11964": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 485
      },
      "11965": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 485
      },
      "11966": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 485
      },
      "11967": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 485
      },
      "11968": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 485
      },
      "11969": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 485
      },
      "11970": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 485
      },
      "11971": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 485
      },
      "11972": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 485
      },
      "11973": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 485
      },
      "12033": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 488
      },
      "12034": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 488
      },
      "12035": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 488
      },
      "12036": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 489
      },
      "12037": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 489
      },
      "12038": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 489
      },
      "12039": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 490
      },
      "12040": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 490
      },
      "12041": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 490
      },
      "12042": {
        "lookahead": {
          "type": "Token",
          "name": "COLONCOLON"
        },
        "like": 490
      },
      "12101": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 493
      },
      "12102": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 493
      },
      "12103": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 493
      },
      "12104": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 493
      },
      "12105": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 493
      },
      "12106": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 493
      },
      "12107": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 493
      },
      "12108": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 493
      },
      "12109": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 493
      },
      "12110": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 493
      },
      "12111": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 493
      },
      "12112": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 493
      },
      "12113": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 493
      },
      "12114": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 493
      },
      "12115": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 493
      },
      "12116": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 493
      },
      "12117": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 493
      },
      "12118": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 493
      },
      "12119": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 493
      },
      "12120": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 493
      },
      "12121": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 493
      },
      "12122": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 493
      },
      "12123": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 493
      },
      "12124": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 493
      },
      "12125": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 493
      },
      "12126": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 493
      },
      "12127": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 493
      },
      "12128": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 493
      },
      "12129": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 493
      },
      "12130": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 493
      },
      "12131": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 493
      },
      "12132": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 493
      },
      "12133": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 493
      },
      "12134": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 493
      },
      "12135": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 493
      },
      "12136": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 493
      },
      "12137": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 493
      },
      "12138": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 493
      },
      "12139": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 493
      },
      "12140": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 493
      },
      "12141": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 493
      },
      "12142": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 493
      },
      "12143": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 493
      },
      "12144": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 493
      },
      "12145": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 493
      },
      "12146": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 493
      },
      "12147": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 493
      },
      "12148": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 493
      },
      "12149": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 493
      },
      "12150": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 493
      },
      "12151": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 493
      },
      "12152": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 493
      },
      "12153": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 493
      },
      "12154": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 493
      },
      "12155": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 493
      },
      "12156": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 493
      },
      "12161": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 496
      },
      "12162": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 496
      },
      "12163": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 496
      },
      "12164": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 497
      },
      "12165": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 497
      },
      "12166": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 497
      },
      "12192": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 502
      },
      "12193": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 502
      },
      "12194": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 502
      },
      "12195": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 502
      },
      "12196": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 502
      },
      "12197": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 502
      },
      "12198": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 502
      },
      "12199": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 502
      },
      "12200": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 502
      },
      "12201": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 502
      },
      "12202": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 502
      },
      "12203": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 502
      },
      "12204": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 502
      },
      "12205": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 502
      },
      "12206": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 502
      },
      "12207": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 502
      },
      "12208": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 502
      },
      "12265": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 504
      },
      "12267": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 506
      },
      "12268": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 506
      },
      "12269": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 506
      },
      "12270": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 506
      },
      "12271": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 506
      },
      "12272": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 506
      },
      "12273": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 506
      },
      "12274": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 506
      },
      "12275": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 506
      },
      "12276": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 506
      },
      "12277": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 506
      },
      "12278": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 506
      },
      "12279": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 506
      },
      "12280": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 506
      },
      "12281": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 506
      },
      "12282": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 506
      },
      "12283": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 506
      },
      "12340": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 508
      },
      "12341": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 508
      },
      "12342": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 508
      },
      "12343": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 508
      },
      "12344": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 509
      },
      "12345": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 509
      },
      "12346": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 509
      },
      "12347": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 509
      },
      "12598": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 515
      },
      "12599": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 515
      },
      "12600": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 515
      },
      "12601": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 515
      },
      "12602": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 515
      },
      "12603": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 515
      },
      "12604": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 515
      },
      "12605": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 515
      },
      "12606": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 515
      },
      "12607": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 515
      },
      "12608": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 515
      },
      "12609": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 515
      },
      "12610": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 515
      },
      "12611": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 515
      },
      "12612": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 515
      },
      "12613": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 515
      },
      "12614": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 515
      },
      "12615": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 515
      },
      "12616": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 515
      },
      "12617": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 515
      },
      "12618": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 515
      },
      "12619": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 515
      },
      "12620": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 515
      },
      "12621": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 515
      },
      "12622": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 515
      },
      "12623": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 515
      },
      "12624": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 515
      },
      "12625": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 515
      },
      "12626": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 515
      },
      "12627": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 515
      },
      "12628": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 515
      },
      "12629": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 515
      },
      "12630": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 516
      },
      "12631": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 516
      },
      "12632": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 516
      },
      "12633": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 516
      },
      "12634": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 516
      },
      "12635": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 516
      },
      "12636": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 516
      },
      "12637": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 516
      },
      "12638": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 516
      },
      "12639": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 516
      },
      "12640": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 516
      },
      "12641": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 516
      },
      "12642": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 516
      },
      "12643": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 516
      },
      "12644": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 516
      },
      "12645": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 516
      },
      "12646": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 516
      },
      "12647": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 516
      },
      "12648": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 516
      },
      "12649": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 516
      },
      "12650": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 516
      },
      "12651": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 516
      },
      "12652": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 516
      },
      "12653": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 516
      },
      "12654": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 516
      },
      "12655": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 516
      },
      "12656": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 517
      },
      "12657": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 517
      },
      "12658": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 517
      },
      "12659": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 517
      },
      "12660": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 517
      },
      "12661": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 517
      },
      "12662": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 517
      },
      "12663": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 517
      },
      "12664": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 517
      },
      "12665": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 517
      },
      "12666": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 517
      },
      "12667": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 517
      },
      "12668": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 517
      },
      "12669": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 517
      },
      "12670": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 517
      },
      "12671": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 517
      },
      "12672": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 517
      },
      "12673": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 517
      },
      "12674": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 517
      },
      "12675": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 517
      },
      "12676": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 517
      },
      "12677": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 517
      },
      "12678": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 517
      },
      "12679": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 517
      },
      "12680": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 517
      },
      "12681": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 517
      },
      "12682": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 517
      },
      "12683": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 517
      },
      "12684": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 517
      },
      "12685": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 517
      },
      "12686": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 517
      },
      "12687": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 517
      },
      "12688": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 517
      },
      "12689": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 517
      },
      "12690": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 517
      },
      "12691": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 517
      },
      "12692": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 517
      },
      "12693": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 517
      },
      "12694": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 517
      },
      "12695": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 517
      },
      "12696": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 517
      },
      "12697": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 517
      },
      "12698": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 517
      },
      "12699": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 517
      },
      "12700": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 517
      },
      "12701": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 517
      },
      "12702": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 517
      },
      "12703": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 517
      },
      "12704": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 517
      },
      "12705": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 517
      },
      "12706": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 517
      },
      "12707": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 517
      },
      "12708": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 517
      },
      "12709": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 517
      },
      "12710": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 517
      },
      "12711": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 517
      },
      "12712": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 517
      },
      "12713": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 518
      },
      "12714": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 518
      },
      "12715": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 518
      },
      "12716": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 518
      },
      "12717": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 518
      },
      "12718": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 518
      },
      "12719": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 518
      },
      "12720": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 518
      },
      "12721": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 518
      },
      "12722": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 518
      },
      "12723": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 518
      },
      "12724": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 518
      },
      "12725": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 518
      },
      "12726": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 518
      },
      "12727": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 518
      },
      "12728": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 518
      },
      "12729": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 518
      },
      "12730": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 518
      },
      "12731": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 518
      },
      "12732": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 518
      },
      "12733": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 518
      },
      "12734": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 518
      },
      "12735": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 518
      },
      "12736": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 518
      },
      "12737": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 518
      },
      "12738": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 518
      },
      "12739": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 518
      },
      "12740": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 518
      },
      "12741": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 518
      },
      "12742": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 518
      },
      "12743": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 518
      },
      "12744": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 518
      },
      "12745": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 518
      },
      "12746": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 518
      },
      "12747": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 518
      },
      "12748": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 518
      },
      "12749": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 518
      },
      "12750": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 518
      },
      "12751": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 518
      },
      "12752": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 518
      },
      "12753": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 518
      },
      "12754": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 518
      },
      "12755": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 518
      },
      "12756": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 518
      },
      "12757": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 518
      },
      "12758": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 518
      },
      "12759": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 518
      },
      "12760": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 518
      },
      "12761": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 518
      },
      "12762": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 518
      },
      "12763": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 518
      },
      "12764": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 518
      },
      "12765": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 518
      },
      "12766": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 518
      },
      "12767": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 518
      },
      "12768": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 518
      },
      "12769": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 518
      },
      "12770": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 519
      },
      "12771": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 519
      },
      "12772": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 519
      },
      "12773": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 519
      },
      "12774": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 519
      },
      "12775": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 519
      },
      "12776": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 519
      },
      "12777": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 519
      },
      "12778": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 519
      },
      "12779": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 519
      },
      "12780": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 519
      },
      "12781": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 519
      },
      "12782": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 519
      },
      "12783": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 519
      },
      "12784": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 519
      },
      "12785": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 519
      },
      "12786": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 519
      },
      "12787": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 519
      },
      "12788": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 519
      },
      "12789": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 519
      },
      "12790": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 519
      },
      "12791": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 519
      },
      "12792": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 519
      },
      "12793": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 519
      },
      "12794": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 519
      },
      "12795": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 519
      },
      "12796": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 519
      },
      "12797": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 519
      },
      "12798": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 519
      },
      "12799": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 519
      },
      "12800": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 519
      },
      "12801": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 519
      },
      "12802": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 520
      },
      "12803": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 520
      },
      "12804": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 520
      },
      "12805": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 520
      },
      "12806": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 520
      },
      "12807": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 520
      },
      "12808": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 520
      },
      "12809": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 520
      },
      "12810": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 520
      },
      "12811": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 520
      },
      "12812": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 520
      },
      "12813": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 520
      },
      "12814": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 520
      },
      "12815": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 520
      },
      "12816": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 520
      },
      "12817": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 520
      },
      "12818": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 520
      },
      "12819": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 520
      },
      "12820": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 520
      },
      "12821": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 520
      },
      "12822": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 520
      },
      "12823": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 520
      },
      "12824": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 520
      },
      "12825": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 520
      },
      "12826": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 520
      },
      "12827": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 520
      },
      "12828": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 520
      },
      "12829": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 520
      },
      "12830": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 520
      },
      "12831": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 520
      },
      "12832": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 520
      },
      "12833": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 520
      },
      "12834": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 521
      },
      "12835": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 521
      },
      "12836": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 521
      },
      "12837": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 521
      },
      "12838": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 522
      },
      "12839": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 522
      },
      "12840": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 522
      },
      "12841": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 522
      },
      "12879": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 526
      },
      "12880": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 526
      },
      "12937": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 528
      },
      "12938": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 528
      },
      "12946": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 531
      },
      "12947": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 532
      },
      "12948": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 533
      },
      "12949": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 533
      },
      "12950": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 533
      },
      "12951": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 533
      },
      "12952": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 533
      },
      "12953": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 533
      },
      "12954": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 533
      },
      "12955": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 533
      },
      "12956": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 533
      },
      "12957": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 533
      },
      "12958": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 533
      },
      "12959": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 533
      },
      "12960": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 533
      },
      "12961": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 533
      },
      "12962": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 533
      },
      "12963": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 533
      },
      "12964": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 533
      },
      "12965": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 533
      },
      "12966": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 533
      },
      "12967": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 533
      },
      "12968": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 533
      },
      "12969": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 533
      },
      "12970": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 533
      },
      "12971": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 533
      },
      "12972": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 533
      },
      "12973": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 533
      },
      "12974": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 533
      },
      "12975": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 533
      },
      "12976": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 533
      },
      "12977": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 533
      },
      "12978": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 533
      },
      "12979": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 533
      },
      "12980": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 533
      },
      "12981": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 533
      },
      "12982": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 533
      },
      "12983": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 533
      },
      "12984": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 533
      },
      "12985": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 533
      },
      "12986": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 533
      },
      "12987": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 533
      },
      "12988": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 533
      },
      "12989": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 533
      },
      "12990": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 533
      },
      "12991": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 533
      },
      "12992": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 533
      },
      "12993": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 533
      },
      "12994": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 533
      },
      "12995": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 533
      },
      "12996": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 533
      },
      "12997": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 533
      },
      "12998": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 533
      },
      "12999": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 533
      },
      "13000": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 533
      },
      "13001": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 533
      },
      "13002": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 533
      },
      "13003": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 533
      },
      "13009": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 534
      },
      "13010": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 534
      },
      "13011": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 534
      },
      "13012": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 534
      },
      "13013": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 534
      },
      "13014": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 534
      },
      "13015": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 534
      },
      "13016": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 534
      },
      "13017": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 534
      },
      "13018": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 534
      },
      "13019": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 534
      },
      "13020": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 534
      },
      "13021": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 534
      },
      "13022": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 534
      },
      "13023": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 534
      },
      "13024": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 534
      },
      "13025": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 534
      },
      "13026": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 534
      },
      "13027": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 534
      },
      "13028": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 534
      },
      "13029": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 534
      },
      "13030": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 534
      },
      "13031": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 534
      },
      "13032": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 534
      },
      "13033": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 534
      },
      "13034": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 534
      },
      "13035": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 534
      },
      "13036": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 534
      },
      "13037": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 534
      },
      "13038": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 534
      },
      "13039": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 534
      },
      "13040": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 534
      },
      "13137": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 538
      },
      "13138": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 538
      },
      "13139": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 538
      },
      "13140": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 538
      },
      "13141": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 538
      },
      "13142": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 538
      },
      "13143": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 538
      },
      "13144": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 538
      },
      "13145": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 538
      },
      "13146": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 538
      },
      "13147": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 538
      },
      "13148": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 538
      },
      "13149": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 538
      },
      "13150": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 538
      },
      "13151": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 538
      },
      "13152": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 538
      },
      "13153": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 538
      },
      "13154": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 538
      },
      "13155": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 538
      },
      "13156": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 538
      },
      "13157": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 538
      },
      "13158": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 538
      },
      "13159": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 538
      },
      "13160": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 538
      },
      "13161": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 538
      },
      "13162": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 538
      },
      "13163": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 538
      },
      "13164": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 538
      },
      "13165": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 538
      },
      "13166": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 538
      },
      "13167": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 538
      },
      "13168": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 538
      },
      "13169": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 539
      },
      "13170": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 539
      },
      "13203": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 541
      },
      "13204": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 541
      },
      "13205": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 541
      },
      "13206": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 541
      },
      "13207": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 541
      },
      "13208": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 541
      },
      "13209": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 541
      },
      "13210": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 541
      },
      "13211": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 541
      },
      "13212": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 541
      },
      "13213": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 541
      },
      "13214": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 541
      },
      "13215": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 541
      },
      "13216": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 541
      },
      "13217": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 541
      },
      "13218": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 541
      },
      "13219": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 541
      },
      "13220": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 541
      },
      "13221": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 541
      },
      "13222": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 541
      },
      "13223": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 541
      },
      "13224": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 541
      },
      "13225": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 541
      },
      "13226": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 541
      },
      "13227": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 541
      },
      "13228": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 541
      },
      "13229": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 541
      },
      "13230": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 541
      },
      "13231": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 541
      },
      "13232": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 541
      },
      "13233": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 541
      },
      "13234": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 541
      },
      "13235": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 541
      },
      "13236": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 541
      },
      "13237": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 541
      },
      "13238": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 541
      },
      "13239": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 541
      },
      "13240": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 541
      },
      "13241": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 541
      },
      "13242": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 541
      },
      "13243": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 541
      },
      "13244": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 542
      },
      "13245": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 542
      },
      "13246": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 542
      },
      "13247": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 542
      },
      "13248": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 542
      },
      "13249": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 542
      },
      "13250": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 542
      },
      "13251": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 542
      },
      "13252": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 542
      },
      "13253": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 542
      },
      "13254": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 542
      },
      "13255": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 542
      },
      "13256": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 542
      },
      "13257": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 542
      },
      "13258": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 542
      },
      "13259": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 542
      },
      "13260": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 542
      },
      "13261": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 542
      },
      "13262": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 542
      },
      "13263": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 542
      },
      "13264": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 542
      },
      "13265": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 542
      },
      "13266": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 542
      },
      "13267": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 542
      },
      "13268": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 542
      },
      "13269": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 542
      },
      "13270": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 542
      },
      "13271": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 542
      },
      "13272": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 542
      },
      "13273": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 542
      },
      "13274": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 542
      },
      "13275": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 542
      },
      "13276": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 542
      },
      "13277": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 542
      },
      "13278": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 542
      },
      "13279": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 542
      },
      "13280": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 542
      },
      "13281": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 542
      },
      "13282": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 542
      },
      "13283": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 542
      },
      "13284": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 542
      },
      "13285": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 542
      },
      "13286": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 542
      },
      "13287": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 542
      },
      "13288": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 542
      },
      "13289": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 542
      },
      "13290": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 542
      },
      "13291": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 542
      },
      "13292": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 542
      },
      "13293": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 542
      },
      "13294": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 542
      },
      "13295": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 542
      },
      "13296": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 543
      },
      "13297": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 543
      },
      "13298": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 543
      },
      "13299": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 543
      },
      "13300": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 543
      },
      "13301": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 543
      },
      "13302": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 543
      },
      "13303": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 543
      },
      "13304": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 543
      },
      "13305": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 543
      },
      "13306": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 543
      },
      "13307": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 543
      },
      "13308": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 543
      },
      "13309": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 543
      },
      "13310": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 543
      },
      "13311": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 543
      },
      "13312": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 543
      },
      "13313": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 543
      },
      "13314": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 543
      },
      "13315": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 543
      },
      "13316": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 543
      },
      "13317": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 543
      },
      "13318": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 543
      },
      "13319": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 543
      },
      "13320": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 543
      },
      "13321": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 543
      },
      "13322": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 543
      },
      "13323": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 543
      },
      "13324": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 543
      },
      "13325": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 543
      },
      "13326": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 543
      },
      "13327": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 543
      },
      "13328": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 543
      },
      "13329": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 543
      },
      "13330": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 543
      },
      "13331": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 543
      },
      "13332": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 543
      },
      "13333": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 543
      },
      "13334": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 543
      },
      "13335": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 543
      },
      "13336": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 543
      },
      "13337": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 543
      },
      "13338": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 543
      },
      "13339": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 543
      },
      "13340": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 543
      },
      "13341": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 543
      },
      "13342": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 543
      },
      "13343": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 543
      },
      "13344": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 543
      },
      "13345": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 543
      },
      "13346": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 543
      },
      "13347": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 543
      },
      "13348": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 543
      },
      "13349": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 543
      },
      "13350": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 543
      },
      "13351": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 543
      },
      "13408": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 545
      },
      "13409": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 545
      },
      "13410": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 545
      },
      "13411": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 545
      },
      "13412": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 545
      },
      "13413": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 545
      },
      "13414": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 545
      },
      "13415": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 545
      },
      "13416": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 545
      },
      "13417": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 545
      },
      "13418": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 545
      },
      "13437": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 549
      },
      "13438": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 549
      },
      "13439": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 549
      },
      "13440": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 549
      },
      "13441": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 549
      },
      "13442": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 550
      },
      "13443": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 550
      },
      "13444": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 550
      },
      "13445": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 550
      },
      "13446": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 550
      },
      "13503": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 552
      },
      "13504": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 552
      },
      "13505": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 552
      },
      "13506": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 552
      },
      "13507": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 553
      },
      "13508": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 553
      },
      "13509": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 553
      },
      "13510": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 553
      },
      "13531": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 556
      },
      "13532": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 556
      },
      "13533": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 556
      },
      "13534": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 556
      },
      "13535": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 556
      },
      "13536": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 556
      },
      "13537": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 556
      },
      "13538": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 556
      },
      "13539": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 556
      },
      "13540": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 556
      },
      "13541": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 557
      },
      "13542": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 558
      },
      "13543": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 558
      },
      "13544": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 558
      },
      "13545": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 558
      },
      "13546": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 558
      },
      "13547": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 558
      },
      "13548": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 558
      },
      "13549": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 558
      },
      "13550": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 558
      },
      "13551": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 558
      },
      "13552": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 559
      },
      "13553": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 559
      },
      "13554": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 559
      },
      "13555": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 559
      },
      "13556": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 559
      },
      "13557": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 559
      },
      "13558": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 559
      },
      "13559": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 559
      },
      "13560": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 559
      },
      "13561": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 559
      },
      "13562": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 560
      },
      "13563": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 560
      },
      "13564": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 560
      },
      "13565": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 560
      },
      "13566": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 560
      },
      "13567": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 560
      },
      "13568": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 560
      },
      "13569": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 560
      },
      "13570": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 560
      },
      "13571": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 560
      },
      "13572": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 561
      },
      "13573": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 561
      },
      "13574": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 561
      },
      "13575": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 561
      },
      "13576": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 561
      },
      "13577": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 561
      },
      "13578": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 561
      },
      "13579": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 561
      },
      "13580": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 561
      },
      "13581": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 561
      },
      "13582": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 562
      },
      "13583": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 562
      },
      "13584": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 562
      },
      "13585": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 562
      },
      "13586": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 562
      },
      "13587": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 562
      },
      "13588": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 562
      },
      "13589": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 562
      },
      "13590": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 562
      },
      "13591": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 562
      },
      "13592": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 563
      },
      "13686": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 568
      },
      "13688": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 570
      },
      "13689": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 570
      },
      "13690": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 570
      },
      "13691": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 570
      },
      "13692": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 570
      },
      "13693": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 570
      },
      "13694": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 570
      },
      "13695": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 570
      },
      "13696": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 570
      },
      "13697": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 570
      },
      "13698": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 570
      },
      "13699": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 570
      },
      "13700": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 570
      },
      "13701": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 570
      },
      "13702": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 570
      },
      "13703": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 570
      },
      "13704": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 570
      },
      "13705": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 571
      },
      "13706": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 571
      },
      "13707": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 571
      },
      "13708": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 571
      },
      "13709": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 571
      },
      "13710": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 571
      },
      "13711": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 571
      },
      "13712": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 571
      },
      "13713": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 571
      },
      "13714": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 571
      },
      "13715": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 571
      },
      "13716": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 571
      },
      "13717": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 571
      },
      "13718": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 571
      },
      "13719": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 571
      },
      "13720": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 571
      },
      "13721": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 571
      },
      "13722": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 572
      },
      "13780": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 575
      },
      "13781": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 575
      },
      "13782": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 575
      },
      "13783": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 575
      },
      "13784": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 575
      },
      "13785": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 575
      },
      "13786": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 575
      },
      "13787": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 575
      },
      "13788": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 575
      },
      "13789": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 575
      },
      "13790": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 575
      },
      "13791": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 575
      },
      "13792": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 575
      },
      "13793": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 575
      },
      "13794": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 575
      },
      "13795": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 575
      },
      "13796": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 575
      },
      "13797": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 575
      },
      "13798": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 575
      },
      "13799": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 575
      },
      "13800": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 575
      },
      "13801": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 575
      },
      "13802": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 575
      },
      "13803": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 575
      },
      "13804": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 575
      },
      "13805": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 575
      },
      "13806": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 575
      },
      "13807": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 575
      },
      "13808": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 575
      },
      "13809": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 575
      },
      "13810": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 575
      },
      "13811": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 575
      },
      "13812": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 575
      },
      "13813": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 575
      },
      "13814": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 575
      },
      "13815": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 575
      },
      "13816": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 575
      },
      "13817": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 575
      },
      "13818": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 575
      },
      "13819": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 575
      },
      "13820": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 575
      },
      "13821": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 575
      },
      "13822": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 575
      },
      "13823": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 575
      },
      "13824": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 575
      },
      "13825": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 575
      },
      "13826": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 575
      },
      "13827": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 575
      },
      "13828": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 575
      },
      "13829": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 575
      },
      "13830": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 575
      },
      "13831": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 575
      },
      "13832": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 575
      },
      "13833": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 575
      },
      "13834": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 575
      },
      "13835": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 575
      },
      "13948": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 578
      },
      "13949": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 578
      },
      "13950": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 578
      },
      "13951": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 578
      },
      "13952": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 578
      },
      "13953": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 578
      },
      "13954": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 578
      },
      "13955": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 578
      },
      "13956": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 578
      },
      "13957": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 578
      },
      "13958": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 578
      },
      "13959": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 578
      },
      "13960": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 578
      },
      "13961": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 578
      },
      "13962": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 578
      },
      "13963": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 578
      },
      "13964": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 578
      },
      "13965": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 578
      },
      "13966": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 578
      },
      "13967": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 578
      },
      "13968": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 578
      },
      "13969": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 578
      },
      "13970": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 578
      },
      "13971": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 578
      },
      "13972": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 578
      },
      "13973": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 578
      },
      "13974": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 578
      },
      "13975": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 578
      },
      "13976": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 578
      },
      "13977": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 578
      },
      "13978": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 578
      },
      "13979": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 578
      },
      "13980": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 578
      },
      "13981": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 578
      },
      "13982": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 578
      },
      "13983": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 578
      },
      "13984": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 578
      },
      "13985": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 578
      },
      "13986": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 578
      },
      "13987": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 578
      },
      "13988": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 578
      },
      "13989": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 578
      },
      "13990": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 578
      },
      "13991": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 578
      },
      "13992": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 578
      },
      "13993": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 578
      },
      "13994": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 578
      },
      "13995": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 578
      },
      "13996": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 578
      },
      "13997": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 578
      },
      "13998": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 578
      },
      "13999": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 578
      },
      "14000": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 578
      },
      "14001": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 578
      },
      "14002": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 578
      },
      "14003": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 578
      },
      "14116": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 581
      },
      "14117": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 582
      },
      "14124": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 586
      },
      "14126": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 588
      },
      "14127": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 588
      },
      "14128": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 589
      },
      "14129": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 589
      },
      "14132": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 591
      },
      "14133": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 591
      },
      "14134": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 591
      },
      "14135": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 591
      },
      "14136": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 591
      },
      "14137": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 591
      },
      "14138": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 591
      },
      "14139": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 591
      },
      "14140": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 591
      },
      "14141": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 591
      },
      "14142": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 591
      },
      "14143": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 591
      },
      "14144": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 591
      },
      "14145": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 591
      },
      "14146": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 591
      },
      "14147": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 591
      },
      "14148": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 591
      },
      "14149": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 591
      },
      "14150": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 591
      },
      "14151": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 591
      },
      "14152": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 591
      },
      "14153": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 591
      },
      "14154": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 591
      },
      "14155": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 591
      },
      "14156": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 591
      },
      "14157": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 591
      },
      "14158": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 591
      },
      "14159": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 591
      },
      "14160": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 591
      },
      "14161": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 591
      },
      "14162": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 591
      },
      "14163": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 591
      },
      "14164": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 591
      },
      "14165": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 591
      },
      "14166": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 591
      },
      "14167": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 591
      },
      "14168": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 591
      },
      "14169": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 591
      },
      "14170": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 591
      },
      "14171": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 591
      },
      "14172": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 591
      },
      "14173": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 591
      },
      "14174": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 591
      },
      "14175": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 591
      },
      "14176": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 591
      },
      "14177": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 591
      },
      "14178": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 591
      },
      "14179": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 591
      },
      "14180": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 591
      },
      "14181": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 591
      },
      "14182": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 591
      },
      "14183": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 591
      },
      "14184": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 591
      },
      "14185": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 591
      },
      "14186": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 591
      },
      "14187": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 591
      },
      "14188": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 592
      },
      "14189": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 593
      },
      "14190": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 593
      },
      "14191": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 593
      },
      "14192": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 594
      },
      "14193": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 594
      },
      "14194": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 594
      },
      "14203": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 598
      },
      "14204": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 598
      },
      "14205": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 598
      },
      "14206": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 598
      },
      "14207": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 598
      },
      "14208": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 598
      },
      "14209": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 598
      },
      "14210": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 598
      },
      "14211": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 598
      },
      "14212": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 598
      },
      "14213": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 598
      },
      "14214": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 598
      },
      "14215": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 598
      },
      "14216": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 598
      },
      "14217": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 598
      },
      "14218": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 598
      },
      "14219": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 598
      },
      "14220": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 599
      },
      "14221": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 599
      },
      "14222": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 599
      },
      "14223": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 599
      },
      "14224": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 599
      },
      "14225": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 599
      },
      "14226": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 599
      },
      "14227": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 599
      },
      "14228": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 599
      },
      "14229": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 599
      },
      "14230": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 599
      },
      "14231": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 599
      },
      "14232": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 599
      },
      "14233": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 599
      },
      "14234": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 599
      },
      "14235": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 599
      },
      "14236": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 599
      },
      "14237": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 599
      },
      "14238": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 599
      },
      "14239": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 599
      },
      "14240": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 599
      },
      "14241": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 599
      },
      "14242": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 599
      },
      "14243": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 599
      },
      "14244": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 599
      },
      "14245": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 599
      },
      "14246": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 599
      },
      "14247": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 599
      },
      "14248": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 599
      },
      "14249": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 599
      },
      "14250": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 599
      },
      "14251": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 599
      },
      "14252": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 599
      },
      "14253": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 599
      },
      "14254": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 599
      },
      "14255": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 599
      },
      "14256": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 599
      },
      "14257": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 599
      },
      "14258": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 599
      },
      "14259": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 599
      },
      "14260": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 599
      },
      "14261": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 599
      },
      "14262": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 599
      },
      "14263": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 599
      },
      "14264": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 599
      },
      "14265": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 599
      },
      "14266": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 599
      },
      "14267": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 599
      },
      "14268": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 599
      },
      "14269": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 599
      },
      "14270": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 599
      },
      "14271": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 599
      },
      "14272": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 599
      },
      "14273": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 599
      },
      "14274": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 599
      },
      "14275": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 599
      },
      "14276": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 600
      },
      "14277": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 601
      },
      "14278": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 601
      },
      "14279": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 601
      },
      "14280": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 601
      },
      "14281": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 601
      },
      "14282": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 601
      },
      "14283": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 601
      },
      "14284": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 601
      },
      "14285": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 601
      },
      "14286": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 601
      },
      "14287": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 601
      },
      "14288": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 601
      },
      "14289": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 601
      },
      "14290": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 601
      },
      "14291": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 601
      },
      "14292": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 601
      },
      "14293": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 601
      },
      "14519": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 606
      },
      "14520": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 606
      },
      "14521": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 606
      },
      "14522": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 606
      },
      "14523": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 606
      },
      "14524": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 606
      },
      "14525": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 606
      },
      "14526": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 606
      },
      "14527": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 606
      },
      "14528": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 606
      },
      "14529": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 606
      },
      "14530": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 606
      },
      "14531": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 606
      },
      "14532": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 606
      },
      "14533": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 606
      },
      "14534": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 606
      },
      "14535": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 606
      },
      "14536": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 606
      },
      "14537": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 606
      },
      "14538": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 606
      },
      "14539": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 606
      },
      "14540": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 606
      },
      "14541": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 606
      },
      "14542": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 606
      },
      "14543": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 606
      },
      "14544": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 606
      },
      "14545": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 606
      },
      "14546": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 606
      },
      "14547": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 606
      },
      "14548": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 606
      },
      "14549": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 606
      },
      "14550": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 606
      },
      "14551": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 606
      },
      "14552": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 606
      },
      "14553": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 606
      },
      "14554": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 606
      },
      "14555": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 606
      },
      "14556": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 606
      },
      "14557": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 606
      },
      "14558": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 606
      },
      "14559": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 606
      },
      "14560": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 606
      },
      "14561": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 606
      },
      "14562": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 606
      },
      "14563": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 606
      },
      "14564": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 606
      },
      "14565": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 606
      },
      "14566": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 606
      },
      "14567": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 606
      },
      "14568": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 606
      },
      "14569": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 606
      },
      "14570": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 606
      },
      "14571": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 606
      },
      "14572": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 606
      },
      "14573": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 606
      },
      "14574": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 606
      },
      "14575": {
        "lookahead": {
          "type": "Token",
          "name": "IMPORT"
        },
        "like": 607
      },
      "14576": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 607
      },
      "14577": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 607
      },
      "14578": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 607
      },
      "14579": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 607
      },
      "14580": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 607
      },
      "14581": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 607
      },
      "14582": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 607
      },
      "14583": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 607
      },
      "14584": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 607
      },
      "14585": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 607
      },
      "14586": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 607
      },
      "14587": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 607
      },
      "14588": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 607
      },
      "14589": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 607
      },
      "14590": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 607
      },
      "14591": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 607
      },
      "14592": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 607
      },
      "14593": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 607
      },
      "14594": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 607
      },
      "14595": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 607
      },
      "14596": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 607
      },
      "14597": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 607
      },
      "14598": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 607
      },
      "14599": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 607
      },
      "14600": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 607
      },
      "14601": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 608
      },
      "14602": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 608
      },
      "14603": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 608
      },
      "14604": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 608
      },
      "14639": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 610
      },
      "14640": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 610
      },
      "14641": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 610
      },
      "14642": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 610
      },
      "14643": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 610
      },
      "14644": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 610
      },
      "14645": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 610
      },
      "14646": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 610
      },
      "14647": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 610
      },
      "14648": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 610
      },
      "14649": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 610
      },
      "14650": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 610
      },
      "14651": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 610
      },
      "14652": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 610
      },
      "14653": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 610
      },
      "14654": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 610
      },
      "14655": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 610
      },
      "14656": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 610
      },
      "14657": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 610
      },
      "14658": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 610
      },
      "14659": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 610
      },
      "14660": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 610
      },
      "14661": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 610
      },
      "14662": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 610
      },
      "14663": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 610
      },
      "14664": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 610
      },
      "14665": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 610
      },
      "14666": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 611
      },
      "14667": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 611
      },
      "14668": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 611
      },
      "14669": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 611
      },
      "14670": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 611
      },
      "14671": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 611
      },
      "14672": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 611
      },
      "14673": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 611
      },
      "14674": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 611
      },
      "14675": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 611
      },
      "14676": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 611
      },
      "14677": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 611
      },
      "14678": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 611
      },
      "14679": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 611
      },
      "14680": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 611
      },
      "14681": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 611
      },
      "14682": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 611
      },
      "14683": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 611
      },
      "14684": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 611
      },
      "14685": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 611
      },
      "14686": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 611
      },
      "14687": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 611
      },
      "14688": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 611
      },
      "14689": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 611
      },
      "14690": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 611
      },
      "14691": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 611
      },
      "14692": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 611
      },
      "14720": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 613
      },
      "14777": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 615
      },
      "14784": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 617
      },
      "14817": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 619
      },
      "14818": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 620
      },
      "14852": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 623
      },
      "14853": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 623
      },
      "14854": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 623
      },
      "14855": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 623
      },
      "14856": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 623
      },
      "14857": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 623
      },
      "14858": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 623
      },
      "14859": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 623
      },
      "14860": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 623
      },
      "14861": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 623
      },
      "14862": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 623
      },
      "14863": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 623
      },
      "14864": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 623
      },
      "14865": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 623
      },
      "14866": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 623
      },
      "14867": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 623
      },
      "14868": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 623
      },
      "14869": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 623
      },
      "14870": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 623
      },
      "14871": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 623
      },
      "14872": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 623
      },
      "14873": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 623
      },
      "14874": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 623
      },
      "14875": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 623
      },
      "14876": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 623
      },
      "14877": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 623
      },
      "14878": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 623
      },
      "14879": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 623
      },
      "14880": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 623
      },
      "14881": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 623
      },
      "14882": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 623
      },
      "14883": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 623
      },
      "14983": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 627
      },
      "14984": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 627
      },
      "14985": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 627
      },
      "14986": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 627
      },
      "14987": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 628
      },
      "14988": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 628
      },
      "14989": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 628
      },
      "14990": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 628
      },
      "14991": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 628
      },
      "14992": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 628
      },
      "14993": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 628
      },
      "14994": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 628
      },
      "14995": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 628
      },
      "14996": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 628
      },
      "14997": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 628
      },
      "14998": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 628
      },
      "14999": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 628
      },
      "15000": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 628
      },
      "15001": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 628
      },
      "15002": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 628
      },
      "15003": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 628
      },
      "15004": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 629
      },
      "15005": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 629
      },
      "15006": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 629
      },
      "15007": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 629
      },
      "15008": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 629
      },
      "15009": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 629
      },
      "15010": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 629
      },
      "15011": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 629
      },
      "15012": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 629
      },
      "15013": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 629
      },
      "15014": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 629
      },
      "15015": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 629
      },
      "15016": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 629
      },
      "15017": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 629
      },
      "15018": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 629
      },
      "15019": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 629
      },
      "15020": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 629
      },
      "15088": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 632
      },
      "15089": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 632
      },
      "15090": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 632
      },
      "15091": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 632
      },
      "15096": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 635
      },
      "15097": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 635
      },
      "15098": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 635
      },
      "15099": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 635
      },
      "15100": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 635
      },
      "15101": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 635
      },
      "15102": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 635
      },
      "15103": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 635
      },
      "15104": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 635
      },
      "15105": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 635
      },
      "15116": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 637
      },
      "15119": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 640
      },
      "15120": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 641
      },
      "15135": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 644
      },
      "15137": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 646
      },
      "15138": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 646
      },
      "15139": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 646
      },
      "15140": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 646
      },
      "15141": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 647
      },
      "15142": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 647
      },
      "15143": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 647
      },
      "15144": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 647
      },
      "15155": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 649
      },
      "15156": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 649
      },
      "15157": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 649
      },
      "15158": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 649
      },
      "15159": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 649
      },
      "15160": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 649
      },
      "15161": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 649
      },
      "15162": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 649
      },
      "15163": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 649
      },
      "15164": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 649
      },
      "15165": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 649
      },
      "15166": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 649
      },
      "15167": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 649
      },
      "15168": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 649
      },
      "15169": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 649
      },
      "15170": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 649
      },
      "15171": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 649
      },
      "15172": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 650
      },
      "15173": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 650
      },
      "15174": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 650
      },
      "15175": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 650
      },
      "15176": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 650
      },
      "15177": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 650
      },
      "15178": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 650
      },
      "15179": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 650
      },
      "15180": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 650
      },
      "15181": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 650
      },
      "15182": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 650
      },
      "15183": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 650
      },
      "15184": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 650
      },
      "15185": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 650
      },
      "15186": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 650
      },
      "15187": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 650
      },
      "15188": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 650
      },
      "15189": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 650
      },
      "15190": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 650
      },
      "15191": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 650
      },
      "15192": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 650
      },
      "15193": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 650
      },
      "15194": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 650
      },
      "15195": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 650
      },
      "15196": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 650
      },
      "15197": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 650
      },
      "15198": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 650
      },
      "15199": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 650
      },
      "15200": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 650
      },
      "15201": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 650
      },
      "15202": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 650
      },
      "15203": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 650
      },
      "15204": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 650
      },
      "15205": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 650
      },
      "15206": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 650
      },
      "15207": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 650
      },
      "15208": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 650
      },
      "15209": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 650
      },
      "15210": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 650
      },
      "15211": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 650
      },
      "15212": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 650
      },
      "15213": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 650
      },
      "15214": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 650
      },
      "15215": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 650
      },
      "15216": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 650
      },
      "15217": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 650
      },
      "15218": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 650
      },
      "15219": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 650
      },
      "15220": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 650
      },
      "15221": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 650
      },
      "15222": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 650
      },
      "15223": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 650
      },
      "15224": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 650
      },
      "15225": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 650
      },
      "15226": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 650
      },
      "15227": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 650
      },
      "15228": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 651
      },
      "15229": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 652
      },
      "15230": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 652
      },
      "15231": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 652
      },
      "15232": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 652
      },
      "15233": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 652
      },
      "15234": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 652
      },
      "15235": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 652
      },
      "15236": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 652
      },
      "15237": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 652
      },
      "15238": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 652
      },
      "15239": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 652
      },
      "15240": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 652
      },
      "15241": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 652
      },
      "15242": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 652
      },
      "15243": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 652
      },
      "15244": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 652
      },
      "15245": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 652
      },
      "15247": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 654
      },
      "15248": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 654
      },
      "15249": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 654
      },
      "15250": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 654
      },
      "15251": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 654
      },
      "15252": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 654
      },
      "15253": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 654
      },
      "15254": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 654
      },
      "15255": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 654
      },
      "15256": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 654
      },
      "15257": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 654
      },
      "15258": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 654
      },
      "15259": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 654
      },
      "15260": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 654
      },
      "15261": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 654
      },
      "15262": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 654
      },
      "15263": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 654
      },
      "15264": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 654
      },
      "15265": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 654
      },
      "15266": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 654
      },
      "15267": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 654
      },
      "15268": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 654
      },
      "15269": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 654
      },
      "15270": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 654
      },
      "15271": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 654
      },
      "15272": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 654
      },
      "15273": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 654
      },
      "15274": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 654
      },
      "15275": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 654
      },
      "15276": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 654
      },
      "15277": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 654
      },
      "15278": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 654
      },
      "15279": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 654
      },
      "15280": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 654
      },
      "15281": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 654
      },
      "15282": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 654
      },
      "15283": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 654
      },
      "15284": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 654
      },
      "15285": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 654
      },
      "15286": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 654
      },
      "15287": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 654
      },
      "15288": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 654
      },
      "15289": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 654
      },
      "15290": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 654
      },
      "15291": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 654
      },
      "15292": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 654
      },
      "15293": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 654
      },
      "15294": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 654
      },
      "15295": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 654
      },
      "15296": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 654
      },
      "15297": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 654
      },
      "15298": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 654
      },
      "15299": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 654
      },
      "15300": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 654
      },
      "15301": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 654
      },
      "15302": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 654
      },
      "15381": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 660
      },
      "15382": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 660
      },
      "15383": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 661
      },
      "15384": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 661
      },
      "15553": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 665
      },
      "15555": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 666
      },
      "15556": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 666
      },
      "15557": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 667
      },
      "15558": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 667
      },
      "15559": {
        "lookahead": {
          "type": "Token",
          "name": "THICKARROW"
        },
        "like": 667
      },
      "15560": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 668
      },
      "15561": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 669
      },
      "15562": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 669
      },
      "15566": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 672
      },
      "15567": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 673
      },
      "15568": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 674
      },
      "15569": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 675
      },
      "15570": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 676
      },
      "15571": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 676
      },
      "15574": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 678
      },
      "15575": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 678
      },
      "15576": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 678
      },
      "15577": {
        "lookahead": {
          "type": "Token",
          "name": "COLONCOLON"
        },
        "like": 678
      },
      "15694": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 683
      },
      "15695": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 683
      },
      "15752": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 685
      },
      "15754": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 687
      },
      "15755": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 687
      },
      "15756": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 688
      },
      "15757": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 688
      },
      "15758": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 689
      },
      "15759": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 689
      },
      "15848": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 692
      },
      "15849": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 692
      },
      "15850": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 692
      },
      "15851": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 692
      },
      "15852": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 692
      },
      "15853": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 692
      },
      "15854": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 692
      },
      "15855": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 692
      },
      "15856": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 692
      },
      "15857": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 692
      },
      "15858": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 692
      },
      "15859": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 692
      },
      "15860": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 692
      },
      "15861": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 692
      },
      "15862": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 692
      },
      "15863": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 692
      },
      "15864": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 692
      },
      "15865": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 692
      },
      "15866": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 692
      },
      "15867": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 692
      },
      "15868": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 692
      },
      "15869": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 692
      },
      "15870": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 692
      },
      "15871": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 692
      },
      "15872": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 692
      },
      "15873": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 692
      },
      "15874": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 692
      },
      "15875": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 693
      },
      "15932": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 695
      },
      "15933": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 695
      },
      "15934": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 695
      },
      "15935": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 695
      },
      "15936": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 695
      },
      "15937": {
        "lookahead": {
          "type": "Token",
          "name": "DERIVING"
        },
        "like": 695
      },
      "15987": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 698
      },
      "15989": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 700
      },
      "15990": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 700
      },
      "15991": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 700
      },
      "15992": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 700
      },
      "15993": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 700
      },
      "15994": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 700
      },
      "15995": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 700
      },
      "15996": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 700
      },
      "15997": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 700
      },
      "15998": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 700
      },
      "15999": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 700
      },
      "16000": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 700
      },
      "16001": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 700
      },
      "16002": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 700
      },
      "16003": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 700
      },
      "16004": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 700
      },
      "16005": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 700
      },
      "16006": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 701
      },
      "16007": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 701
      },
      "16008": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 701
      },
      "16009": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 701
      },
      "16010": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 701
      },
      "16011": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 701
      },
      "16012": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 701
      },
      "16013": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 701
      },
      "16014": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 701
      },
      "16015": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 701
      },
      "16016": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 701
      },
      "16017": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 701
      },
      "16018": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 701
      },
      "16019": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 701
      },
      "16020": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 701
      },
      "16021": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 701
      },
      "16022": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 701
      },
      "16063": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 705
      },
      "16064": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 705
      },
      "16065": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 705
      },
      "16066": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 705
      },
      "16067": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 706
      },
      "16068": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 706
      },
      "16069": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 706
      },
      "16070": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 706
      },
      "16071": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 707
      },
      "16072": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 707
      },
      "16073": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 707
      },
      "16074": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 707
      },
      "16075": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 707
      },
      "16076": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 707
      },
      "16077": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 707
      },
      "16078": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 707
      },
      "16079": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 707
      },
      "16080": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 707
      },
      "16081": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 707
      },
      "16082": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 707
      },
      "16083": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 707
      },
      "16084": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 707
      },
      "16085": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 707
      },
      "16086": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 707
      },
      "16087": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 707
      },
      "16088": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 707
      },
      "16089": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 707
      },
      "16090": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 707
      },
      "16091": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 707
      },
      "16092": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 707
      },
      "16093": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 707
      },
      "16094": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 707
      },
      "16095": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 707
      },
      "16096": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 707
      },
      "16097": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 707
      },
      "16098": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 707
      },
      "16099": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 707
      },
      "16100": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 707
      },
      "16101": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 707
      },
      "16102": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 707
      },
      "16103": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 708
      },
      "16104": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 708
      },
      "16105": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 708
      },
      "16106": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 708
      },
      "16107": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 708
      },
      "16108": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 708
      },
      "16109": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 708
      },
      "16110": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 708
      },
      "16111": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 708
      },
      "16112": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 708
      },
      "16113": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 708
      },
      "16114": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 708
      },
      "16115": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 708
      },
      "16116": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 708
      },
      "16117": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 708
      },
      "16118": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 708
      },
      "16119": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 708
      },
      "16120": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 708
      },
      "16121": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 708
      },
      "16122": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 708
      },
      "16123": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 708
      },
      "16124": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 708
      },
      "16125": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 708
      },
      "16126": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 708
      },
      "16127": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 708
      },
      "16128": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 708
      },
      "16129": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 708
      },
      "16130": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 708
      },
      "16131": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 708
      },
      "16132": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 708
      },
      "16133": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 708
      },
      "16134": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 708
      },
      "16135": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 708
      },
      "16136": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 708
      },
      "16137": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 708
      },
      "16138": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 708
      },
      "16139": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 708
      },
      "16140": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 708
      },
      "16141": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 708
      },
      "16142": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 708
      },
      "16143": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 708
      },
      "16144": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 708
      },
      "16145": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 708
      },
      "16146": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 708
      },
      "16147": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 708
      },
      "16148": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 708
      },
      "16149": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 708
      },
      "16150": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 708
      },
      "16151": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 708
      },
      "16152": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 708
      },
      "16153": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 708
      },
      "16154": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 708
      },
      "16155": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 708
      },
      "16156": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 708
      },
      "16157": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 708
      },
      "16158": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 708
      },
      "16159": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 709
      },
      "16160": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 709
      },
      "16161": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 709
      },
      "16162": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 709
      },
      "16163": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 709
      },
      "16164": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 709
      },
      "16165": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 709
      },
      "16166": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 709
      },
      "16167": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 709
      },
      "16168": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 709
      },
      "16169": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 709
      },
      "16180": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 711
      },
      "16181": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 711
      },
      "16182": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 711
      },
      "16183": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 711
      },
      "16184": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 711
      },
      "16185": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 711
      },
      "16186": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 711
      },
      "16187": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 711
      },
      "16188": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 711
      },
      "16189": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 711
      },
      "16190": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 711
      },
      "16191": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 711
      },
      "16192": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 711
      },
      "16193": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 711
      },
      "16194": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 711
      },
      "16195": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 711
      },
      "16196": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 711
      },
      "16197": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 711
      },
      "16198": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 711
      },
      "16199": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 711
      },
      "16200": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 711
      },
      "16201": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 711
      },
      "16202": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 711
      },
      "16203": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 711
      },
      "16204": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 711
      },
      "16205": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 711
      },
      "16206": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 711
      },
      "16207": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 711
      },
      "16208": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 711
      },
      "16209": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 711
      },
      "16210": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 711
      },
      "16211": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 711
      },
      "16212": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 711
      },
      "16213": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 711
      },
      "16214": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 711
      },
      "16215": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 711
      },
      "16216": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 711
      },
      "16217": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 711
      },
      "16218": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 711
      },
      "16219": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 711
      },
      "16220": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 711
      },
      "16221": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 711
      },
      "16222": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 711
      },
      "16223": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 711
      },
      "16224": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 711
      },
      "16225": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 711
      },
      "16226": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 711
      },
      "16227": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 711
      },
      "16228": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 711
      },
      "16229": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 711
      },
      "16230": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 711
      },
      "16231": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 711
      },
      "16232": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 711
      },
      "16233": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 711
      },
      "16234": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 711
      },
      "16235": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 711
      },
      "16240": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 714
      },
      "16241": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 714
      },
      "16242": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 714
      },
      "16243": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 714
      },
      "16244": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 714
      },
      "16245": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 714
      },
      "16246": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 714
      },
      "16247": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 714
      },
      "16248": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 714
      },
      "16249": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 714
      },
      "16250": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 715
      },
      "16251": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 716
      },
      "16252": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 717
      },
      "16253": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 718
      },
      "16254": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 718
      },
      "16255": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 718
      },
      "16256": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 718
      },
      "16267": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 720
      },
      "16269": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 721
      },
      "16270": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 721
      },
      "16271": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 721
      },
      "16272": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 721
      },
      "16287": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 724
      },
      "16288": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 724
      },
      "16289": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 724
      },
      "16290": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 724
      },
      "16291": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 725
      },
      "16292": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 725
      },
      "16293": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 725
      },
      "16294": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 725
      },
      "16295": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 726
      },
      "16296": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 727
      },
      "16297": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 727
      },
      "16298": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 727
      },
      "16299": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 727
      },
      "16300": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 727
      },
      "16301": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 727
      },
      "16302": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 727
      },
      "16303": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 727
      },
      "16304": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 727
      },
      "16305": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 727
      },
      "16306": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 727
      },
      "16307": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 727
      },
      "16308": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 727
      },
      "16309": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 727
      },
      "16310": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 727
      },
      "16311": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 727
      },
      "16312": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 727
      },
      "16313": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 727
      },
      "16314": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 727
      },
      "16315": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 727
      },
      "16316": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 727
      },
      "16317": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 727
      },
      "16318": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 727
      },
      "16319": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 727
      },
      "16320": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 727
      },
      "16321": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 727
      },
      "16322": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 727
      },
      "16323": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 727
      },
      "16324": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 727
      },
      "16325": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 727
      },
      "16326": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 727
      },
      "16327": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 727
      },
      "16328": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 727
      },
      "16329": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 727
      },
      "16330": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 727
      },
      "16331": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 727
      },
      "16332": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 727
      },
      "16333": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 727
      },
      "16334": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 727
      },
      "16335": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 727
      },
      "16336": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 727
      },
      "16337": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 727
      },
      "16338": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 727
      },
      "16339": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 727
      },
      "16340": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 727
      },
      "16341": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 727
      },
      "16342": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 727
      },
      "16343": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 727
      },
      "16344": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 727
      },
      "16345": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 727
      },
      "16346": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 727
      },
      "16347": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 727
      },
      "16348": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 727
      },
      "16349": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 727
      },
      "16350": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 727
      },
      "16351": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 727
      },
      "16366": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 730
      },
      "16367": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 730
      },
      "16368": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 730
      },
      "16369": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 730
      },
      "16370": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 730
      },
      "16371": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 730
      },
      "16372": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 731
      },
      "16373": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 731
      },
      "16374": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 732
      },
      "16375": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 732
      },
      "16376": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 733
      },
      "16377": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 733
      },
      "16378": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 733
      },
      "16379": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 733
      },
      "16380": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 733
      },
      "16381": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 733
      },
      "16382": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 733
      },
      "16383": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 733
      },
      "16384": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 733
      },
      "16385": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 733
      },
      "16386": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 733
      },
      "16387": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 733
      },
      "16388": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 733
      },
      "16389": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 733
      },
      "16390": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 733
      },
      "16391": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 733
      },
      "16392": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 733
      },
      "16393": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 733
      },
      "16394": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 733
      },
      "16395": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 733
      },
      "16396": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 733
      },
      "16397": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 733
      },
      "16398": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 733
      },
      "16399": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 733
      },
      "16400": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 733
      },
      "16401": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 733
      },
      "16402": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 733
      },
      "16403": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 733
      },
      "16404": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 733
      },
      "16405": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 733
      },
      "16406": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 733
      },
      "16407": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 733
      },
      "16408": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 733
      },
      "16409": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 733
      },
      "16410": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 733
      },
      "16411": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 733
      },
      "16412": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 733
      },
      "16413": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 733
      },
      "16414": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 733
      },
      "16415": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 733
      },
      "16416": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 733
      },
      "16417": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 733
      },
      "16418": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 733
      },
      "16419": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 733
      },
      "16420": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 733
      },
      "16421": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 733
      },
      "16422": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 733
      },
      "16423": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 733
      },
      "16424": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 733
      },
      "16425": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 733
      },
      "16426": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 733
      },
      "16427": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 733
      },
      "16428": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 733
      },
      "16429": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 733
      },
      "16430": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 733
      },
      "16431": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 733
      },
      "16432": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 734
      },
      "16433": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 734
      },
      "16434": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 734
      },
      "16435": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 734
      },
      "16436": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 734
      },
      "16437": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 734
      },
      "16438": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 734
      },
      "16439": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 734
      },
      "16440": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 734
      },
      "16441": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 734
      },
      "16442": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 734
      },
      "16443": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 734
      },
      "16444": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 734
      },
      "16445": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 734
      },
      "16446": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 734
      },
      "16447": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 734
      },
      "16448": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 734
      },
      "16449": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 734
      },
      "16450": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 734
      },
      "16451": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 734
      },
      "16452": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 734
      },
      "16453": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 734
      },
      "16454": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 734
      },
      "16455": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 734
      },
      "16456": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 734
      },
      "16457": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 734
      },
      "16458": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 734
      },
      "16459": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 734
      },
      "16460": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 734
      },
      "16461": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 734
      },
      "16462": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 734
      },
      "16463": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 734
      },
      "16464": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 734
      },
      "16465": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 734
      },
      "16466": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 734
      },
      "16467": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 734
      },
      "16468": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 734
      },
      "16469": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 734
      },
      "16470": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 734
      },
      "16471": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 734
      },
      "16472": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 734
      },
      "16473": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 734
      },
      "16474": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 734
      },
      "16475": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 734
      },
      "16476": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 734
      },
      "16477": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 734
      },
      "16478": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 734
      },
      "16479": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 734
      },
      "16480": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 734
      },
      "16481": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 734
      },
      "16482": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 734
      },
      "16483": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 734
      },
      "16484": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 734
      },
      "16485": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 734
      },
      "16486": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 734
      },
      "16487": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 734
      },
      "16544": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 736
      },
      "16605": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 740
      },
      "16606": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 740
      },
      "16607": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 740
      },
      "16608": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 741
      },
      "16609": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 741
      },
      "16610": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 741
      },
      "16611": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 741
      },
      "16674": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 745
      },
      "16675": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 745
      },
      "16732": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 747
      },
      "16733": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 748
      },
      "16734": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 748
      },
      "16823": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 751
      },
      "16824": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 751
      },
      "16825": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 752
      },
      "16826": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 752
      },
      "16827": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 753
      },
      "16828": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 753
      },
      "16890": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 756
      },
      "16891": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 756
      },
      "16892": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 756
      },
      "16893": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 756
      },
      "16894": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 756
      },
      "16927": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 758
      },
      "16928": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 758
      },
      "16929": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 758
      },
      "16930": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 758
      },
      "16931": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 758
      },
      "16932": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 759
      },
      "16933": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 759
      },
      "16934": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 759
      },
      "16935": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 759
      },
      "16936": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 759
      },
      "16937": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 760
      },
      "16938": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 760
      },
      "16939": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 760
      },
      "16940": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 760
      },
      "16941": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 760
      },
      "16942": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 760
      },
      "16943": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 760
      },
      "16944": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 760
      },
      "16945": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 760
      },
      "16946": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 760
      },
      "16947": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 760
      },
      "16948": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 760
      },
      "16949": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 760
      },
      "16950": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 760
      },
      "16951": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 760
      },
      "16952": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 760
      },
      "16953": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 760
      },
      "16954": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 761
      },
      "16955": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 762
      },
      "16956": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 762
      },
      "16957": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 762
      },
      "16958": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 762
      },
      "16959": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 762
      },
      "16960": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 762
      },
      "16961": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 762
      },
      "16962": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 762
      },
      "16963": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 762
      },
      "16964": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 762
      },
      "16965": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 762
      },
      "16966": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 762
      },
      "16967": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 762
      },
      "16968": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 762
      },
      "16969": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 762
      },
      "16970": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 762
      },
      "16971": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 762
      },
      "16972": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 763
      },
      "16973": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 763
      },
      "16974": {
        "lookahead": {
          "type": "Token",
          "name": "CYCLIC"
        },
        "like": 763
      },
      "16975": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 763
      },
      "16976": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 763
      },
      "16977": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 764
      },
      "16978": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 764
      },
      "16979": {
        "lookahead": {
          "type": "Token",
          "name": "CYCLIC"
        },
        "like": 764
      },
      "16980": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 764
      },
      "16981": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 764
      },
      "16993": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 767
      },
      "16994": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 767
      },
      "16995": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 767
      },
      "16996": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 767
      },
      "17041": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 772
      },
      "17042": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 772
      },
      "17043": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 772
      },
      "17044": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 773
      },
      "17045": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 773
      },
      "17046": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 773
      },
      "17047": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 773
      },
      "17048": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 774
      },
      "17049": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 774
      },
      "17050": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 774
      },
      "17051": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 774
      },
      "17052": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 774
      },
      "17053": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 774
      },
      "17054": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 774
      },
      "17055": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 774
      },
      "17056": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 774
      },
      "17057": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 774
      },
      "17058": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 775
      },
      "17059": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 775
      },
      "17061": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 776
      },
      "17062": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 776
      },
      "17073": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 778
      },
      "17074": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 778
      },
      "17075": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 778
      },
      "17076": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 778
      },
      "17087": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 780
      },
      "17088": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 780
      },
      "17089": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 780
      },
      "17090": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 780
      },
      "17091": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 781
      },
      "17092": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 781
      },
      "17093": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 781
      },
      "17094": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 781
      },
      "17095": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 781
      },
      "17096": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 781
      },
      "17097": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 781
      },
      "17105": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 783
      },
      "17106": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 783
      },
      "17107": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 783
      },
      "17108": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 783
      },
      "17109": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 783
      },
      "17110": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 783
      },
      "17111": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 784
      },
      "17112": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 784
      },
      "17113": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 784
      },
      "17114": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 784
      },
      "17115": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 784
      },
      "17116": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 784
      },
      "17117": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 785
      },
      "17118": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 785
      },
      "17119": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 785
      },
      "17120": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 785
      },
      "17121": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 785
      },
      "17122": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 785
      },
      "17179": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 787
      },
      "17180": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 787
      },
      "17239": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 790
      },
      "17240": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 790
      },
      "17241": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 791
      },
      "17242": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 791
      },
      "17243": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 792
      },
      "17244": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 792
      },
      "17245": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 792
      },
      "17306": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 795
      },
      "17307": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 795
      },
      "17420": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 798
      },
      "17421": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 798
      },
      "17422": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 798
      },
      "17423": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 798
      },
      "17424": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 798
      },
      "17425": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 798
      },
      "17426": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 798
      },
      "17427": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 798
      },
      "17428": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 798
      },
      "17429": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 798
      },
      "17430": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 798
      },
      "17431": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 798
      },
      "17432": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 798
      },
      "17433": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 798
      },
      "17434": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 798
      },
      "17435": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 798
      },
      "17436": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 798
      },
      "17437": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 798
      },
      "17438": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 798
      },
      "17439": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 798
      },
      "17440": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 798
      },
      "17441": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 798
      },
      "17442": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 798
      },
      "17443": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 798
      },
      "17444": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 798
      },
      "17445": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 798
      },
      "17446": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 798
      },
      "17447": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 798
      },
      "17448": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 798
      },
      "17449": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 798
      },
      "17450": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 798
      },
      "17451": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 798
      },
      "17452": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 799
      },
      "17453": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 799
      },
      "17510": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 801
      },
      "17511": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 801
      },
      "17512": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 801
      },
      "17513": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 801
      },
      "17514": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 801
      },
      "17515": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 802
      },
      "17516": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 802
      },
      "17517": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 802
      },
      "17518": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 802
      },
      "17519": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 802
      },
      "17520": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 803
      },
      "17521": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 803
      },
      "17522": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 803
      },
      "17523": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 803
      },
      "17524": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 803
      },
      "17525": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 804
      },
      "17526": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 804
      },
      "17527": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 804
      },
      "17528": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 804
      },
      "17529": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 804
      },
      "17567": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 807
      },
      "17568": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 807
      },
      "17569": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 807
      },
      "17570": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 807
      },
      "17571": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 808
      },
      "17572": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 808
      },
      "17573": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 808
      },
      "17574": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 808
      },
      "17575": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 808
      },
      "17586": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 811
      },
      "17587": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 811
      },
      "17588": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 811
      },
      "17589": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 811
      },
      "17597": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 813
      },
      "17603": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 816
      },
      "17604": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 816
      },
      "17605": {
        "lookahead": {
          "type": "Token",
          "name": "CYCLIC"
        },
        "like": 816
      },
      "17606": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 816
      },
      "17607": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 817
      },
      "17608": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 817
      },
      "17609": {
        "lookahead": {
          "type": "Token",
          "name": "CYCLIC"
        },
        "like": 817
      },
      "17610": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 817
      },
      "17613": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 819
      },
      "17614": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 819
      },
      "17615": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 820
      },
      "17616": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 820
      },
      "17617": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 821
      },
      "17618": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 821
      },
      "17619": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 822
      },
      "17620": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 823
      },
      "17665": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 828
      },
      "17666": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 828
      },
      "17667": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 828
      },
      "17668": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 829
      },
      "17669": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 829
      },
      "17670": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 829
      },
      "17671": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 829
      },
      "17672": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 829
      },
      "17673": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 829
      },
      "17674": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 829
      },
      "17675": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 829
      },
      "17676": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 829
      },
      "17677": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 829
      },
      "17678": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 830
      },
      "17679": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 830
      },
      "17680": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 830
      },
      "17681": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 830
      },
      "17682": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 830
      },
      "17683": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALS"
        },
        "like": 830
      },
      "17684": {
        "lookahead": {
          "type": "Token",
          "name": "FROM"
        },
        "like": 830
      },
      "17685": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 830
      },
      "17686": {
        "lookahead": {
          "type": "Token",
          "name": "THINARROW"
        },
        "like": 830
      },
      "17687": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 830
      },
      "17753": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 834
      },
      "17754": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 834
      },
      "17755": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 834
      },
      "17756": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 834
      },
      "17757": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 834
      },
      "17758": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 834
      },
      "17759": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 834
      },
      "17760": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 834
      },
      "17761": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 834
      },
      "17762": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 834
      },
      "17763": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 834
      },
      "17764": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 834
      },
      "17765": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 834
      },
      "17766": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 834
      },
      "17767": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 834
      },
      "17768": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 834
      },
      "17769": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 834
      },
      "17770": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 834
      },
      "17771": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 834
      },
      "17772": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 834
      },
      "17773": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 834
      },
      "17774": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 834
      },
      "17775": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 834
      },
      "17776": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 834
      },
      "17777": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 834
      },
      "17778": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 834
      },
      "17779": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 834
      },
      "17780": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 834
      },
      "17781": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 834
      },
      "17782": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 834
      },
      "17783": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 834
      },
      "17784": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 834
      },
      "17785": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 834
      },
      "17786": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 834
      },
      "17787": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 834
      },
      "17788": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 834
      },
      "17789": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 834
      },
      "17790": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 834
      },
      "17791": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 834
      },
      "17792": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 834
      },
      "17793": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 834
      },
      "17794": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 834
      },
      "17795": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 834
      },
      "17796": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 834
      },
      "17797": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 834
      },
      "17798": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 834
      },
      "17799": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 834
      },
      "17800": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 834
      },
      "17801": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 834
      },
      "17802": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 834
      },
      "17803": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 834
      },
      "17804": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 834
      },
      "17805": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 834
      },
      "17806": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 834
      },
      "17807": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 834
      },
      "17808": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 834
      },
      "17809": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 835
      },
      "17810": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 835
      },
      "17811": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 836
      },
      "17812": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 836
      },
      "17813": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 836
      },
      "17814": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 836
      },
      "17874": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 839
      },
      "17875": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 839
      },
      "17876": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 839
      },
      "17877": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 840
      },
      "17878": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 840
      },
      "17879": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 840
      },
      "18048": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 844
      },
      "18049": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 844
      },
      "18050": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 844
      },
      "18051": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 844
      },
      "18052": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 844
      },
      "18053": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 845
      },
      "18054": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 845
      },
      "18055": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 845
      },
      "18056": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 845
      },
      "18057": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 845
      },
      "18090": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 847
      },
      "18091": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 847
      },
      "18092": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 847
      },
      "18093": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 848
      },
      "18094": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 848
      },
      "18095": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 848
      },
      "18099": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 850
      },
      "18100": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 850
      },
      "18101": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 850
      },
      "18102": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 850
      },
      "18108": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 852
      },
      "18109": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 852
      },
      "18110": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 852
      },
      "18111": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 852
      },
      "18112": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 852
      },
      "18113": {
        "lookahead": {
          "type": "Token",
          "name": "WITHCONSTRUCTOR"
        },
        "like": 853
      },
      "18114": {
        "lookahead": {
          "type": "Token",
          "name": "WITH"
        },
        "like": 853
      },
      "18115": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 853
      },
      "18116": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 853
      },
      "18117": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 853
      },
      "18118": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 853
      },
      "18119": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 853
      },
      "18120": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 854
      },
      "18121": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 855
      },
      "18122": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 855
      },
      "18123": {
        "lookahead": {
          "type": "Token",
          "name": "CYCLIC"
        },
        "like": 855
      },
      "18124": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 855
      },
      "18125": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 856
      },
      "18126": {
        "lookahead": {
          "type": "Token",
          "name": "MUTABLE"
        },
        "like": 856
      },
      "18127": {
        "lookahead": {
          "type": "Token",
          "name": "CYCLIC"
        },
        "like": 856
      },
      "18128": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 856
      },
      "18129": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 857
      },
      "18130": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 857
      },
      "18139": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 860
      },
      "18140": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 860
      },
      "18141": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 860
      },
      "18142": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 860
      },
      "18143": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 861
      },
      "18144": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 861
      },
      "18145": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 861
      },
      "18146": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 861
      },
      "18147": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 861
      },
      "18148": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 861
      },
      "18149": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 861
      },
      "18150": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 861
      },
      "18151": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 861
      },
      "18152": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 861
      },
      "18153": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 861
      },
      "18154": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 861
      },
      "18155": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 861
      },
      "18156": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 861
      },
      "18157": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 861
      },
      "18158": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 861
      },
      "18159": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 861
      },
      "18160": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 861
      },
      "18161": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 861
      },
      "18162": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 861
      },
      "18163": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 861
      },
      "18164": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 861
      },
      "18165": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 861
      },
      "18166": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 861
      },
      "18167": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 861
      },
      "18168": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 861
      },
      "18169": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 861
      },
      "18170": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 861
      },
      "18171": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 861
      },
      "18172": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 861
      },
      "18173": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 861
      },
      "18174": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 861
      },
      "18182": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 863
      },
      "18183": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 863
      },
      "18184": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 863
      },
      "18185": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 863
      },
      "18186": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 863
      },
      "18187": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 863
      },
      "18188": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 863
      },
      "18189": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 863
      },
      "18190": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 863
      },
      "18191": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 863
      },
      "18192": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 863
      },
      "18193": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 863
      },
      "18194": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 863
      },
      "18195": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 863
      },
      "18196": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 863
      },
      "18197": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 863
      },
      "18198": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 863
      },
      "18199": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 863
      },
      "18200": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 863
      },
      "18201": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 863
      },
      "18202": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 863
      },
      "18203": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 863
      },
      "18204": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 863
      },
      "18205": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 863
      },
      "18206": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 863
      },
      "18207": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 863
      },
      "18208": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 863
      },
      "18209": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 863
      },
      "18210": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 863
      },
      "18211": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 863
      },
      "18212": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 863
      },
      "18213": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 863
      },
      "18214": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 863
      },
      "18215": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 863
      },
      "18216": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 863
      },
      "18217": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 863
      },
      "18218": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 863
      },
      "18219": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 863
      },
      "18220": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 863
      },
      "18221": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 863
      },
      "18222": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 863
      },
      "18223": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 863
      },
      "18224": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 863
      },
      "18225": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 863
      },
      "18226": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 863
      },
      "18227": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 863
      },
      "18228": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 863
      },
      "18229": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 863
      },
      "18230": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 863
      },
      "18231": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 863
      },
      "18232": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 863
      },
      "18233": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 863
      },
      "18234": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 863
      },
      "18235": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 863
      },
      "18236": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 863
      },
      "18237": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 863
      },
      "18240": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 865
      },
      "18241": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 865
      },
      "18242": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 865
      },
      "18243": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 865
      },
      "18305": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 869
      },
      "18306": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 869
      },
      "18307": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 870
      },
      "18308": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 870
      },
      "18309": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 870
      },
      "18422": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 873
      },
      "18423": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 873
      },
      "18424": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 873
      },
      "18425": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 873
      },
      "18426": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 873
      },
      "18427": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 873
      },
      "18428": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 873
      },
      "18429": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 873
      },
      "18430": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 873
      },
      "18431": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 873
      },
      "18432": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 873
      },
      "18433": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 873
      },
      "18434": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 873
      },
      "18435": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 873
      },
      "18436": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 873
      },
      "18437": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 873
      },
      "18438": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 873
      },
      "18439": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 873
      },
      "18440": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 873
      },
      "18441": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 873
      },
      "18442": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 873
      },
      "18443": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 873
      },
      "18444": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 873
      },
      "18445": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 873
      },
      "18446": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 873
      },
      "18447": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 873
      },
      "18448": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 873
      },
      "18449": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 873
      },
      "18450": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 873
      },
      "18451": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 873
      },
      "18452": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 873
      },
      "18453": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 873
      },
      "18454": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 873
      },
      "18455": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 873
      },
      "18456": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 873
      },
      "18457": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 873
      },
      "18458": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 873
      },
      "18459": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 873
      },
      "18460": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 873
      },
      "18461": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 873
      },
      "18462": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 873
      },
      "18463": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 873
      },
      "18464": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 873
      },
      "18465": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 873
      },
      "18466": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 873
      },
      "18467": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 873
      },
      "18468": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 873
      },
      "18469": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 873
      },
      "18470": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 873
      },
      "18471": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 873
      },
      "18472": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 873
      },
      "18473": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 873
      },
      "18474": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 873
      },
      "18475": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 873
      },
      "18476": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 873
      },
      "18477": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 873
      },
      "18510": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 875
      },
      "18511": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 875
      },
      "18512": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 875
      },
      "18513": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 876
      },
      "18514": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 876
      },
      "18515": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 876
      },
      "18516": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 876
      },
      "18517": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 876
      },
      "18518": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 877
      },
      "18519": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 877
      },
      "18520": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 877
      },
      "18521": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 877
      },
      "18522": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 877
      },
      "18527": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 879
      },
      "18528": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 879
      },
      "18529": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 879
      },
      "18530": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 879
      },
      "18538": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 881
      },
      "18539": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 881
      },
      "18540": {
        "lookahead": {
          "type": "Token",
          "name": "THICKARROW"
        },
        "like": 882
      },
      "18544": {
        "lookahead": {
          "type": "Token",
          "name": "THICKARROW"
        },
        "like": 884
      },
      "18547": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 886
      },
      "18548": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 886
      },
      "18549": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 886
      },
      "18550": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 886
      },
      "18551": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 886
      },
      "18552": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 886
      },
      "18553": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 886
      },
      "18554": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 886
      },
      "18555": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 886
      },
      "18556": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 886
      },
      "18557": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 886
      },
      "18558": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 886
      },
      "18559": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 886
      },
      "18560": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 886
      },
      "18561": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 886
      },
      "18562": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 886
      },
      "18563": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 886
      },
      "18564": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 886
      },
      "18565": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 886
      },
      "18566": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 886
      },
      "18567": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 886
      },
      "18568": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 886
      },
      "18569": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 886
      },
      "18570": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 886
      },
      "18571": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 886
      },
      "18572": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 886
      },
      "18573": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 886
      },
      "18574": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 886
      },
      "18575": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 886
      },
      "18576": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 886
      },
      "18577": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 886
      },
      "18578": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 886
      },
      "18579": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 886
      },
      "18580": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 886
      },
      "18581": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 886
      },
      "18582": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 886
      },
      "18583": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 886
      },
      "18584": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 886
      },
      "18585": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 886
      },
      "18586": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 886
      },
      "18587": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 886
      },
      "18588": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 886
      },
      "18589": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 886
      },
      "18590": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 886
      },
      "18591": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 886
      },
      "18592": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 886
      },
      "18593": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 886
      },
      "18594": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 886
      },
      "18595": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 886
      },
      "18596": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 886
      },
      "18597": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 886
      },
      "18598": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 886
      },
      "18599": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 886
      },
      "18600": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 886
      },
      "18601": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 886
      },
      "18602": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 886
      },
      "18603": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 887
      },
      "18604": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 887
      },
      "18605": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 887
      },
      "18606": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 887
      },
      "18607": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 887
      },
      "18608": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 887
      },
      "18609": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 887
      },
      "18610": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 887
      },
      "18611": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 887
      },
      "18612": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 887
      },
      "18613": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 887
      },
      "18614": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 887
      },
      "18615": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 887
      },
      "18616": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 887
      },
      "18617": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 887
      },
      "18618": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 887
      },
      "18619": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 887
      },
      "18620": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 887
      },
      "18621": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 887
      },
      "18622": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 887
      },
      "18623": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 887
      },
      "18624": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 887
      },
      "18625": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 887
      },
      "18626": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 887
      },
      "18627": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 887
      },
      "18628": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 887
      },
      "18629": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 887
      },
      "18630": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 887
      },
      "18631": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 887
      },
      "18632": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 887
      },
      "18633": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 887
      },
      "18634": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 887
      },
      "18635": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 887
      },
      "18636": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 887
      },
      "18637": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 887
      },
      "18638": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 887
      },
      "18639": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 887
      },
      "18640": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 887
      },
      "18641": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 887
      },
      "18642": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 887
      },
      "18643": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 887
      },
      "18644": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 887
      },
      "18645": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 887
      },
      "18646": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 887
      },
      "18647": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 887
      },
      "18648": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 887
      },
      "18649": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 887
      },
      "18650": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 887
      },
      "18651": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 887
      },
      "18652": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 887
      },
      "18653": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 887
      },
      "18654": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 887
      },
      "18655": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 887
      },
      "18656": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 887
      },
      "18657": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 887
      },
      "18658": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 887
      },
      "18659": {
        "lookahead": {
          "type": "Token",
          "name": "PLUS"
        },
        "like": 888
      },
      "18660": {
        "lookahead": {
          "type": "Token",
          "name": "DASH"
        },
        "like": 888
      },
      "18661": {
        "lookahead": {
          "type": "Token",
          "name": "STAR"
        },
        "like": 888
      },
      "18662": {
        "lookahead": {
          "type": "Token",
          "name": "SLASH"
        },
        "like": 888
      },
      "18663": {
        "lookahead": {
          "type": "Token",
          "name": "LEQ"
        },
        "like": 888
      },
      "18664": {
        "lookahead": {
          "type": "Token",
          "name": "GEQ"
        },
        "like": 888
      },
      "18665": {
        "lookahead": {
          "type": "Token",
          "name": "EQUALEQUAL"
        },
        "like": 888
      },
      "18666": {
        "lookahead": {
          "type": "Token",
          "name": "NEQ"
        },
        "like": 888
      },
      "18667": {
        "lookahead": {
          "type": "Token",
          "name": "LT"
        },
        "like": 888
      },
      "18668": {
        "lookahead": {
          "type": "Token",
          "name": "GT"
        },
        "like": 888
      },
      "18669": {
        "lookahead": {
          "type": "Token",
          "name": "AND"
        },
        "like": 888
      },
      "18670": {
        "lookahead": {
          "type": "Token",
          "name": "OR"
        },
        "like": 888
      },
      "18671": {
        "lookahead": {
          "type": "Token",
          "name": "IS"
        },
        "like": 888
      },
      "18672": {
        "lookahead": {
          "type": "Token",
          "name": "RAISES"
        },
        "like": 888
      },
      "18673": {
        "lookahead": {
          "type": "Token",
          "name": "SATISFIES"
        },
        "like": 888
      },
      "18674": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 888
      },
      "18675": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 888
      },
      "18676": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 888
      },
      "18677": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 888
      },
      "18678": {
        "lookahead": {
          "type": "Token",
          "name": "VAR"
        },
        "like": 888
      },
      "18679": {
        "lookahead": {
          "type": "Token",
          "name": "NAME"
        },
        "like": 888
      },
      "18680": {
        "lookahead": {
          "type": "Token",
          "name": "CHECK"
        },
        "like": 888
      },
      "18681": {
        "lookahead": {
          "type": "Token",
          "name": "GRAPH"
        },
        "like": 888
      },
      "18682": {
        "lookahead": {
          "type": "Token",
          "name": "SHADOW"
        },
        "like": 888
      },
      "18683": {
        "lookahead": {
          "type": "Token",
          "name": "NOT"
        },
        "like": 888
      },
      "18684": {
        "lookahead": {
          "type": "Token",
          "name": "PARENSPACE"
        },
        "like": 888
      },
      "18685": {
        "lookahead": {
          "type": "Token",
          "name": "METHOD"
        },
        "like": 888
      },
      "18686": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACE"
        },
        "like": 888
      },
      "18687": {
        "lookahead": {
          "type": "Token",
          "name": "LBRACK"
        },
        "like": 888
      },
      "18688": {
        "lookahead": {
          "type": "Token",
          "name": "IF"
        },
        "like": 888
      },
      "18689": {
        "lookahead": {
          "type": "Token",
          "name": "CASES"
        },
        "like": 888
      },
      "18690": {
        "lookahead": {
          "type": "Token",
          "name": "FOR"
        },
        "like": 888
      },
      "18691": {
        "lookahead": {
          "type": "Token",
          "name": "TRY"
        },
        "like": 888
      },
      "18692": {
        "lookahead": {
          "type": "Token",
          "name": "BLOCK"
        },
        "like": 888
      },
      "18693": {
        "lookahead": {
          "type": "Token",
          "name": "NUMBER"
        },
        "like": 888
      },
      "18694": {
        "lookahead": {
          "type": "Token",
          "name": "TRUE"
        },
        "like": 888
      },
      "18695": {
        "lookahead": {
          "type": "Token",
          "name": "FALSE"
        },
        "like": 888
      },
      "18696": {
        "lookahead": {
          "type": "Token",
          "name": "STRING"
        },
        "like": 888
      },
      "18697": {
        "lookahead": {
          "type": "Token",
          "name": "PARENNOSPACE"
        },
        "like": 888
      },
      "18698": {
        "lookahead": {
          "type": "Token",
          "name": "CARET"
        },
        "like": 888
      },
      "18699": {
        "lookahead": {
          "type": "Token",
          "name": "DOT"
        },
        "like": 888
      },
      "18700": {
        "lookahead": {
          "type": "Token",
          "name": "COLON"
        },
        "like": 888
      },
      "18701": {
        "lookahead": {
          "type": "Token",
          "name": "BANG"
        },
        "like": 888
      },
      "18702": {
        "lookahead": {
          "type": "Token",
          "name": "END"
        },
        "like": 888
      },
      "18703": {
        "lookahead": {
          "type": "Token",
          "name": "SEMI"
        },
        "like": 888
      },
      "18704": {
        "lookahead": {
          "type": "Token",
          "name": "RPAREN"
        },
        "like": 888
      },
      "18705": {
        "lookahead": {
          "type": "Token",
          "name": "COMMA"
        },
        "like": 888
      },
      "18706": {
        "lookahead": {
          "type": "Token",
          "name": "EXCEPT"
        },
        "like": 888
      },
      "18707": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACK"
        },
        "like": 888
      },
      "18708": {
        "lookahead": {
          "type": "Token",
          "name": "ELSEIF"
        },
        "like": 888
      },
      "18709": {
        "lookahead": {
          "type": "Token",
          "name": "ELSE"
        },
        "like": 888
      },
      "18710": {
        "lookahead": {
          "type": "Token",
          "name": "WHERE"
        },
        "like": 888
      },
      "18711": {
        "lookahead": {
          "type": "EOF"
        },
        "like": 888
      },
      "18712": {
        "lookahead": {
          "type": "Token",
          "name": "RBRACE"
        },
        "like": 888
      },
      "18713": {
        "lookahead": {
          "type": "Token",
          "name": "BAR"
        },
        "like": 888
      },
      "18714": {
        "lookahead": {
          "type": "Token",
          "name": "SHARING"
        },
        "like": 888
      },
      "18715": {
        "lookahead": {
          "type": "Token",
          "name": "FUN"
        },
        "like": 889
      },
      "18716": {
        "lookahead": {
          "type": "Token",
          "name": "DATA"
        },
        "like": 889
      },
      "18717": {
        "lookahead": {
          "type": "Token",
          "name": "DATATYPE"
        },
        "like": 889
      },
      "18718": {
        "lookahead": {
          "type": "Token",
          "name": "WHEN"
        },
        "like": 889
      },
      "18719": {
        "lookahead": {
        },
      },