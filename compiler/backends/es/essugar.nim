# esLet.decl(exported=false, ident("i", "int"), lit(1)) # let i /*int*/ = 1;
import esast, esstmt, esexpr
proc decl*(kind: ESVarKind, exported:bool, ident, val: ESNode): ESNode =
  newVarDecl(
    kind, exported, 
    newVarDeclarator(
      ident, val, typ
    )
  )
# esFunc.decl(false, ident("sum"), @[ident("x", "int"),ident("y", "int")), body)
proc decl*(kind: ESNodeKind, exported: bool, name: ESNode, params: seq[ESNode], body: ESNode): ESNode =
  assert kind == ekFunctionDeclaration
  newFuncDecl(
    name,
    body,
    params,
    exported
  )