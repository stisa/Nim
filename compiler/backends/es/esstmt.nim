import esast, esexpr
import strutils
# Statements and declarations

proc newExpressionStmt*(expression:ESNode, loc:SourceLocation=nil): ESNode =
  assert(expression.isExpression, $expression.typ)
  result = newESNode(ekExpressionStatement,loc)
  result.expression = expression

proc newBlockStmt*(body:varargs[ESNode], loc:SourceLocation=nil): ESNode =
  if body.len>0:
    for el in body: assert(el.isStatement, "got: " & $el.typ )
  result = newESNode(ekBlockStatement, loc)
  result.body = @body

proc newEmptyStmt*(loc:SourceLocation=nil):ESNode =
  result = newESNode(ekEmptyStatement, loc)
  
proc newDebuggerStmt*(loc:SourceLocation=nil):ESNode =
  result = newESNode(ekDebuggerStatement, loc)

proc newWithStatement*(obj:ESNode, body:ESNode, loc:SourceLocation=nil):ESNode =
  assert obj.isExpression
  assert body.isStatement
  result = newESNode(ekWithStatement, loc)
  result.obj = obj
  result.body = body

proc newReturnStmt*(arg:ESNode,loc:SourceLocation=nil):ESNode =
  assert arg.isExpression or arg.typ == ekExpressionStatement, $arg.typ
  result = newESNode(ekReturnStatement, loc)
  result.argument = arg

proc newLabeledStmt*(lb,body:ESNode,loc:SourceLocation=nil):ESNode =
  assert lb.typ == ekIdentifier
  assert body.isStatement, $body.typ
  result = newESNode(ekLabeledStatement,loc)
  result.llabel = lb
  result.body = body

proc newBreakStmt*(lb:ESNode,loc:SourceLocation=nil):ESNode =
  assert lb.typ == ekIdentifier
  result = newESNode(ekBreakStatement,loc)
  result.blabel = lb

proc newContinueStmt*(lb:ESNode,loc:SourceLocation=nil):ESNode =
  assert lb.typ == ekIdentifier
  result = newESNode(ekContinueStatement,loc)
  result.blabel = lb

proc newIfStmt*(cond,then: ESNode,other:ESNode= newEmptyStmt(),loc:SourceLocation=nil):ESNode =
  assert cond.isExpression, $cond.typ
  assert then.isStatement or then.typ == ekCallExpression, $then.typ
  assert other.isStatement, $other.typ

  result = newESNode(ekIfStatement, loc)
  result.test = cond
  result.iconsequent = then
  result.ialternate = other

proc newSwitchStmt*(disc:ESNode, cases:varargs[ESNode], def: ESNode= newEmptyStmt(),loc:SourceLocation=nil):ESNode =
  assert disc.isExpression
  for el in cases: assert el.typ == ekSwitchCase
  assert def.typ in {ekEmptyStatement, ekDefaultCase}
  result = newESNode(ekSwitchStatement,loc)
  result.sdiscriminant = disc
  result.scases = @cases
  result.def = def

proc newSwitchCase*(cond:ESNode, thens:varargs[ESNode], fall:bool = false, loc:SourceLocation=nil):ESNode =
  assert cond.isExpression
  if not fall:
    for el in thens: assert el.isStatement, $el.typ

  result = newESNode(ekSwitchCase)
  result.test = cond
  result.sconsequent = @thens
  result.sfall = fall

proc newDefaultCase*(thens:varargs[ESNode], loc:SourceLocation=nil):ESNode =
  for el in thens: assert el.isStatement, $el.typ

  result = newESNode(ekDefaultCase)
  result.dconsq = @thens

proc newThrowStmt*(arg:ESNode,loc:SourceLocation=nil):ESNode =
  assert arg.isExpression

  result = newESNode(ekThrowStatement,loc)
  result.argument = arg

proc newTryStmt*(blc,handler,finalizer:ESNode,loc:SourceLocation=nil):ESNode =
  assert blc.isStatement, $blc.typ
  assert handler.typ == ekCatchClause, $handler.typ
  assert finalizer.isStatement, $finalizer.typ

  result = newESNode(ekTryStatement,loc)
  result.tblck = blc
  result.thandler = handler
  result.tfinalizer = finalizer

proc newCatchClause*(par,bod:ESNode,loc:SourceLocation=nil):ESNode =
  assert par.isPattern, $par.typ
  assert bod.isStatement, $bod.typ
  
  result = newESNode(ekCatchClause,loc)
  result.cparam = par
  result.body = bod

proc newWhileStmt*(cond,bod:ESNode,loc:SourceLocation=nil):ESNode =
  assert cond.isExpression
  assert bod.isStatement

  result = newESNode(ekWhileStatement,loc)
  result.test = cond
  result.body = bod

proc newDoWhileStmt*(cond,bod:ESNode,loc:SourceLocation=nil):ESNode =
  assert cond.isExpression
  assert bod.isStatement

  result = newESNode(ekDoWhileStatement,loc)
  result.test = cond
  result.body = bod

proc newForStmt*(init,test,update,bod:ESNode,loc:SourceLocation=nil):ESNode =
  if not init.isNil:
    assert(init.isExpression or init.typ == ekVariableDeclaration)
  if not test.isNil:
    assert(test.isExpression)
  if not update.isNil:
    assert(update.isExpression)
  assert(bod.isStatement)

  result = newESNode(ekForStatement,loc)
  result.finit = init
  result.test = test
  result.fupdate = update
  result.body = bod

proc newForInStmt*(left,right,bod:ESNode,loc:SourceLocation=nil):ESNode =
  assert left.isPattern or left.typ == ekVariableDeclaration
  assert right.isExpression
  assert bod.isStatement

  result = newESNode(ekForInStatement,loc)
  result.left = left
  result.right = right
  result.body = bod

proc newVarDecl*(kind:ESVarKind, exported: bool, decls:openArray[ESNode],loc:SourceLocation=nil):ESNode =
  for d in decls: assert(d.typ == ekVariableDeclarator, $d.typ)

  result = newESNode(ekVariableDeclaration, loc)
  result.vkind = kind
  result.vexp = exported
  result.vdeclarations = @decls

proc newVarDeclarator*(id, init:ESNode, loc:SourceLocation=nil):ESNode =
  # FIXME: assert id.isPattern, $id.typ
  
  result = newESNode(ekVariableDeclarator,loc)
  result.vid = id

  if not init.isNil:
    # we can create variables without initializing,
    # but we are explicit and init to nil
    assert init.isExpression, $init.typ
    result.vinit = init
  else:
    result.vinit = newESLiteral()


