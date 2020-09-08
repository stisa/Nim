import esast

# Expressions

proc newThisExpr*(loc:SourceLocation=nil):ESNode = newESNode(ekThisExpression,loc)
proc newArrayExpr*(els:openArray[ESNode] = @[], loc:SourceLocation=nil):ESNode =
  for el in els: assert el.isExpression, $el.typ

  result = newESNode(ekArrayExpression, loc)
  result.elements = @els

proc newObjectExpr*(props:varargs[ESNode], loc:SourceLocation=nil):ESNode =
  for el in props: assert el.typ == ekProperty

  result = newESNode(ekObjectExpression, loc)
  result.properties = @props

proc newProperty*(k,val:ESNode,kind:string="", loc:SourceLocation=nil):ESNode =
  assert k.isLiteral or k.typ == ekIdentifier
  assert val.isExpression
  assert kind in ["init","get","set", ""]

  result = newESNode(ekProperty,loc)
  result.key = k
  result.value = val
  result.pkind = kind

proc newUnaryExpr*(op:string, prefix:bool,arg:ESNode,loc:SourceLocation=nil):ESNode =
  assert op.isUnaryOp, op
  assert arg.isExpression

  result = newESNode(ekUnaryExpression,loc)
  result.unoperator = op
  result.unprefix = prefix
  result.argument = arg

proc newUpdateExpr*(op:string, prefix:bool,arg:ESNode,loc:SourceLocation=nil):ESNode =
  assert op.isUpdateOp, op
  assert arg.isExpression

  result = newESNode(ekUpdateExpression,loc)
  result.uoperator = op
  result.uprefix = prefix
  result.argument = arg

proc newBinaryExpr*(op:string, left,right:ESNode,loc:SourceLocation=nil):ESNode =
  assert op.isBinaryOp, op
  assert left.isExpression
  assert right.isExpression

  result = newESNode(ekBinaryExpression,loc)
  result.boperator = op
  result.left = left
  result.right = right

proc newAsgnExpr*(op:string, left,right:ESNode,loc:SourceLocation=nil):ESNode =
  assert op.isAsgnOp , op
  assert left.isExpression or left.isPattern, $left.typ
  assert right.isExpression, $right.typ

  result = newESNode(ekAssignmentExpression,loc)
  result.aoperator = op
  result.left = left
  result.right = right

proc newLogicalExpr*(op:string, left,right:ESNode,loc:SourceLocation=nil):ESNode =
  assert op.isLogicalOp, op
  assert left.isExpression
  assert right.isExpression

  result = newESNode(ekLogicalExpression,loc)
  result.loperator = op
  result.left = left
  result.right = right

proc newMemberExpr*(obj,prop:ESNode,computed:bool,loc:SourceLocation=nil):ESNode =
  assert obj.isExpression
  assert prop.isExpression

  result = newESNode(ekMemberExpression,loc)
  result.mobject = obj
  result.property = prop
  result.computed = computed

proc newMemberCallExpr*(obj,prop:ESNode, args: varargs[ESNode],loc:SourceLocation=nil):ESNode =
  assert obj.isExpression
  assert prop.isExpression

  result = newESNode(ekMemberCallExpression,loc)
  result.cobj = obj
  result.objprop = prop
  result.args = @args


proc newCondExpr*(cond,then,other:ESNode, loc:SourceLocation=nil):ESNode =
  # if _ then _ else _
  assert cond.isExpression
  assert then.isExpression
  assert other.isExpression

  result = newESNode(ekConditionalExpression,loc)
  result.test = cond
  result.calternate = then
  result.cconsequent = other

proc newCallExpr*(callee:ESNode, args:varargs[ESNode],loc:SourceLocation=nil):ESNode =
  assert callee.isExpression, $callee.typ
  for a in args: assert a.isExpression, $a.typ

  result = newESNode(ekCallExpression,loc)
  result.callee = callee
  result.arguments = @args

proc newNewExpr*(callee:ESNode, args:varargs[ESNode],loc:SourceLocation=nil):ESNode =
  assert callee.isExpression
  for a in args: assert a.isExpression

  result = newESNode(ekNewExpression,loc)
  result.callee = callee
  result.arguments = @args

proc newSequenceExpr*(exprs:varargs[ESNode],loc:SourceLocation=nil):ESNode =
  for s in exprs: assert s.isExpression

  result = newESNode(ekSequenceExpression,loc)
  result.expressions = @exprs