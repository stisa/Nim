import esast

proc treerepr*(n:ESNode):string =
  proc traverse(res: var string, level: int, n: ESNode) =
    if n.isNil: 
      res = "//nil node"
      return
    if not n.loc.isNil:
      if n.typ == ekAssignmentExpression: add res, "\n"
      for i in 0..level-1: res.add "  "
      add res, "// source:" & n.loc.source & " line: " & $n.loc.starts.line & ", col: " & $n.loc.starts.col & "\n"
    for i in 0..level-1: res.add "  "
    add res, $n.typ & ": " 
    case n.typ
    of ekIdentifier: add res, n.name
    of ekStrLit: add res, "\""&n.strval&"\""
    of ekBoolLit: add res, $n.bval
    of ekNullLit: add res, "nil"
    of ekIntLit: add res, $n.ival
    of ekFloatLit: add res, $n.fval
    of ekRegExpLiteral: add res, $n.rval & " " & $n.regex
    of ekProgram:
      for j in 0..n.pbody.len-1:
        res.add "\n"
        traverse(res, level + 1, n.pbody[j])
    of ekFunction,ekFunctionDeclaration,ekFunctionExpression:
      res.add "\n"
      traverse(res, level+1, n.id)
      for j in 0..n.params.len-1:
        res.add "\n"
        traverse(res, level + 1, n.params[j])
      res.add "\n"
      traverse(res,level+1,n.body)
    of ekExpressionStatement: traverse(res,level+1,n.expression)
    of ekBlockStatement:
      for j in 0..n.bbody.len-1:
        res.add "\n"
        traverse(res, level + 1, n.bbody[j])
    of ekEmptyStatement: add res, "nil"
    of ekDebuggerStatement: add res, "debugger"
    of ekWithStatement:
      res.add "\n"
      traverse(res, level + 1, n.obj)
      res.add "\n"
      traverse(res, level + 1, n.body)
    of ekReturnStatement:
      res.add "\n"
      traverse(res, level + 1, n.argument)
    of ekLabeledStatement:
      res.add "\n"
      traverse(res, level + 1, n.llabel)
      res.add "\n"
      traverse(res, level + 1, n.body)
    of ekBreakStatement,ekContinueStatement:
      res.add "\n"
      traverse(res, level + 1, n.blabel)
    of ekIfStatement:
      res.add "\n"
      traverse(res, level + 1, n.test)
      res.add "\n"
      traverse(res, level + 1, n.iconsequent)
      res.add "\n"
      traverse(res, level + 1, n.ialternate)
    of ekSwitchCase:
      res.add "\n"
      traverse(res, level + 1, n.test)
      for j in 0..n.sconsequent.len-1:
        res.add "\n"
        traverse(res, level + 1, n.sconsequent[j])
    of ekSwitchStatement:
      res.add "\n"
      traverse(res, level+1, n.sdiscriminant)
      for j in 0..n.scases.len-1:
        res.add "\n"
        traverse(res, level + 1, n.scases[j])
    of ekThrowStatement:
      res.add "\n"
      traverse(res, level+1, n.argument)
    of ekTryStatement:
      res.add "\n"
      traverse(res, level+1, n.tblck)
      res.add "\n"
      traverse(res, level+1, n.thandler)
      res.add "\n"
      traverse(res, level+1, n.tfinalizer)
    of ekCatchClause:
      res.add "\n"
      traverse(res, level+1, n.cparam)
      res.add "\n"
      traverse(res, level+1, n.body)
    of ekWhileStatement:
      res.add "\n"
      traverse(res, level+1, n.body)
    of ekDoWhileStatement:
      res.add "\n"
      traverse(res, level+1, n.test)
      res.add "\n"
      traverse(res, level+1, n.body)
    of ekForStatement:
      res.add "\n"
      traverse(res, level+1, n.finit)
      res.add "\n"
      traverse(res, level+1, n.test)
      res.add "\n"
      traverse(res, level+1, n.fupdate)
      res.add "\n"
      traverse(res, level+1, n.body)
    of ekForInStatement:
      res.add "\n"
      traverse(res, level+1, n.left)
      res.add "\n"
      traverse(res, level+1, n.right)
      res.add "\n"
      traverse(res, level+1, n.body)
    of ekVariableDeclaration:
      add res, "\n"
      for i in 0..level: res.add "  "
      add res, "kind: " & n.vkind
      for j in 0..n.vdeclarations.len-1:
        res.add "\n"
        traverse(res, level + 1, n.vdeclarations[j])
    of ekVariableDeclarator:
      res.add "\n"
      traverse(res, level + 1, n.vid)
      res.add "\n"
      traverse(res, level + 1, n.vinit)
    of ekThisExpression: add res, "this"
    of ekArrayExpression:
      for j in 0..n.elements.len-1:
        res.add "\n"
        traverse(res, level + 1, n.elements[j])
    of ekObjectExpression:
      for j in 0..n.properties.len-1:
        res.add "\n"
        traverse(res, level + 1, n.properties[j])
    of ekProperty:
      res.add "\n"
      traverse(res, level + 1, n.key)
      res.add "\n"
      traverse(res, level + 1, n.value)
      res.add "\n"
      add res, n.pkind
    of ekUnaryExpression:
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, n.unoperator
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, $n.unprefix
      res.add "\n"
      traverse(res, level + 1, n.argument)
    of ekUpdateExpression:
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, n.uoperator
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, $n.uprefix
      res.add "\n"
      traverse(res, level + 1, n.argument)
    of ekBinaryExpression:
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, n.boperator
      res.add "\n"
      traverse(res, level + 1, n.left)
      res.add "\n"
      traverse(res, level + 1, n.right)
    of ekAssignmentExpression:
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, n.aoperator
      res.add "\n"
      traverse(res, level + 1, n.left)
      res.add "\n"
      traverse(res, level + 1, n.right)
    of ekLogicalExpression:
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, n.loperator
      res.add "\n"
      traverse(res, level + 1, n.left)
      res.add "\n"
      traverse(res, level + 1, n.right)
    of ekMemberExpression:
      res.add "\n"
      traverse(res, level + 1, n.mobject)
      res.add "\n"
      traverse(res, level + 1, n.property)
      res.add "\n"
      for i in 0..level: res.add "  "
      add res, $n.computed
    of ekConditionalExpression:
      res.add "\n"
      traverse(res, level + 1, n.test)
      res.add "\n"
      traverse(res, level + 1, n.calternate)
      res.add "\n"
      traverse(res, level + 1, n.cconsequent)
    of ekCallExpression,ekNewExpression:
      res.add "\n"
      traverse(res, level + 1, n.callee)
      for j in 0..n.arguments.len-1:
        res.add "\n"
        traverse(res, level + 1, n.arguments[j])
    of ekSequenceExpression:
      for j in 0..n.expressions.len-1:
        res.add "\n"
        traverse(res, level + 1, n.expressions[j])
    of ekEmit:
      res.add n.code
  result = ""
  traverse(result, 0, n)