#https://github.com/estree/estree/blob/master/es5.md
#https://github.com/estree/estree/blob/master/es2015.md

type
  ESVarKind* = enum
    esVar, esLet, esConst
  ESNodeKind* = enum
    # estree es5 
    ekIdentifier
    #ekLiteral  see non standerd
    ekRegExpLiteral
    ekProgram
    ekFunction
    ekExpressionStatement
    ekBlockStatement
    ekEmptyStatement
    ekDebuggerStatement
    ekWithStatement
    ekReturnStatement
    ekLabeledStatement
    ekBreakStatement
    ekContinueStatement
    ekIfStatement
    ekSwitchStatement 
    ekSwitchCase
    ekThrowStatement
    ekTryStatement 
    ekCatchClause
    ekWhileStatement
    ekDoWhileStatement
    ekForStatement
    ekForInStatement
    ekFunctionDeclaration
    ekVariableDeclaration 
    ekVariableDeclarator
    ekThisExpression
    ekArrayExpression
    ekObjectExpression 
    ekProperty
    ekFunctionExpression
    ekUnaryExpression 
    #ekUnaryOperator
    ekUpdateExpression 
    #ekUpdateOperator
    ekBinaryExpression 
    #ekBinaryOperator
    ekAssignmentExpression 
    #ekAssignmentOperator
    ekLogicalExpression 
    #ekLogicalOperator
    ekMemberExpression
    ekConditionalExpression
    ekCallExpression
    ekNewExpression
    ekSequenceExpression
    #ekPattern
    #es6
    
    ekModule
    ekExport
    ekImport

    # --v-- Non standard --v--
    ekStrLit
    ekBoolLit
    ekNullLit
    ekIntLit
    ekFloatLit
    ekEmit # pass js code directly as string
    ekMemberCallExpression
  
  ESType* = enum
    etNum,etString,etObj,etArray,etNil,etFunc
  
  ESFlag* = enum
    efImmediateAsgn, efDeclared
  
  SourceLocation* = ref object
    source*:string
    starts*,ends*:tuple[line,col:int]

  ESNode* = ref object
    loc*: SourceLocation
    case typ*: ESNodeKind
    of ekEmit:
      code*: string 
      # Literals
    of ekIdentifier:
      name*: string # May be Expression or Pattern ?
      ptyp*: string 
    of ekStrLit:
      strval*: ESNode
    of ekBoolLit:
      bval*: bool
    of ekNullLit:
      discard # nval: void?
    of ekIntLit:
      ival*: BiggestInt
    of ekFloatLit:
      fval*: BiggestFloat
    of ekRegExpLiteral:
      rval*: string # regex
      regex*: tuple[patter,flags:string]
      # Structural
    of ekProgram:
      pbody*: seq[ESNode] # statements
    of ekModule:
      mname*: string
      mbody*: seq[ESNode]
      mimports*: seq[ESNode]
      mexports*: seq[ESNode]
    of ekFunction,ekFunctionDeclaration,ekFunctionExpression:
      id*: ESNode #identifier if ekFunctionDecl id can't be null
      params*: seq[ESNode] #pattern
      fbody: ESNode # BlockStatement
      fexported*: bool
    of ekImport:
      imodule*: string
      iident*: string
    of ekExport:
      eident*: string
      # Statements
    of ekExpressionStatement:
      expression*: ESNode #expression
    of ekBlockStatement:
      bbody*: seq[ESNode] #statement
    of ekEmptyStatement: discard # empty duh
    of ekDebuggerStatement: discard # ??
    of ekWithStatement:
      obj*: ESNode #epxression
      wsbody: ESNode # statement
    # Control flow
    of ekReturnStatement:
      rargument: ESNode # expression
    of ekLabeledStatement:
      llabel*: ESNode #identifier
      lbody: ESNode #statement
    of ekBreakStatement,ekContinueStatement:
      blabel*: ESNode #Identifier
    #Choice
    of ekIfStatement:
      itest: ESNode # expression
      iconsequent*: ESNode #statement
      ialternate*: ESnode # statement
    of ekSwitchStatement:
      sdiscriminant*: ESNode # expression
      scases*: seq[ESNode] #switchcase
    of ekSwitchCase:
      stest: ESNode # expression
      sconsequent*: seq[ESNode] #statement
    # Exception
    of ekThrowStatement:
      targument: ESNode # expression
    of ekTryStatement:
      tblck*: ESNode #blockstatemnt
      thandler*: ESNode # ekCatchClause
      tfinalizer*: ESNode # ekBlockStatement
    of ekCatchClause:
      cparam*: ESNode #pattern
      cbody: ESNode # ekBlockStatement
    # Loops
    of ekWhileStatement:
      wtest: ESNode #expression
      wbody: ESNode #statement
    of ekDoWhileStatement:
      dtest: ESNode #expression
      dbody: ESNode #statement
    of ekForStatement:
      finit*: ESNode #variabledecl or expression or nil
      ftest: ESNode #expression or nil
      fupdate*: ESNode #expression or nil
      fsbody: ESNode #statement
    of ekForInStatement:
      fleft: ESNode # ekVariableDeclaration or ekPattern
      fright: ESNode # expression
      fibody: ESNode #ekStatement
    #Declarations Note that declarations are considered statements; 
    of ekVariableDeclaration:
      vdeclarations*: seq[ESNode] # ekVariableDeclarator
      vkind*: ESVarKind # var
      vexp*: bool
    of ekVariableDeclarator:
      vid*: ESNode #pattern
      vinit*: ESNode #expression
    # Expressions
    of ekThisExpression: discard
    of ekArrayExpression:
      elements*: seq[ESNode] # expression
    of ekObjectExpression:
      properties*: seq[ESNode] # ekPropety
    of ekProperty:
      key*: ESNode # Literal or ekIdentifier
      pvalue: ESNode #expression
      pkind*: string #init,get,set
    of ekUnaryExpression:
      unoperator*: string #TODO: enum - + ! ~ typeof void delete
      unprefix*: bool
      unargument: ESNode #expression
    of ekUpdateExpression:
      uoperator*: string # ++ or --
      uargument: ESNode # expression
      uprefix*: bool
    of ekBinaryExpression:
      boperator*: string #["==" | "!=" | "===" | "!=="
                                    | "<" | "<=" | ">" | ">="
                                    | "<<" | ">>" | ">>>"
                                    | "+" | "-" | "*" | "/" | "%"
                                    | "|" | "^" | "&" | "in"
                                    | "instanceof" ]#
      bleft: ESNode # expression
      bright: ESNode # expression
    of ekAssignmentExpression:
      aoperator*: string #["=" | "+=" | "-=" | "*=" | "/=" | "%="
                          | "<<=" | ">>=" | ">>>="
                          | "|=" | "^=" | "&="]#
      aleft: ESNode # pattern or expr
      aright: ESNode # ecpr
    of ekLogicalExpression:
      loperator*: string # "||" | "&&"
      lleft,lright:ESNode #expression
    of ekMemberExpression:
      mobject*, property*: ESNode #expression
      computed*: bool
    of ekConditionalExpression:
      ctest, calternate*,cconsequent*:ESNode #expresssion
    of ekCallExpression,ekNewExpression:
      callee*: ESNode #expression
      arguments*: seq[ESNode] #expression
    of ekMemberCallExpression:
      cobj*, objprop*: ESNode
      args*: seq[ESNode]
    of ekSequenceExpression:
      expressions*: seq[ESNode] # expression

# These procs are used in place of interfaces
proc isLiteral*(n:ESNode):bool =
  n.typ in {ekBoolLit,ekFloatLit,ekIntLit,ekStrLit,ekNullLit,ekRegExpLiteral}

proc isExpression*(n:ESNode):bool =
  n.typ in {ekIdentifier, ekThisExpression, ekArrayExpression, ekObjectExpression,
            ekFunctionExpression, ekUnaryExpression, ekUpdateExpression, 
            ekBinaryExpression, ekAssignmentExpression,ekLogicalExpression,
            ekMemberExpression, ekConditionalExpression, ekCallExpression,
            ekNewExpression, ekSequenceExpression, ekEmit } or n.isLiteral()

proc isDeclaration*(n:ESNode):bool =
  n.typ in {ekFunctionDeclaration, ekVariableDeclaration}

proc isFunction*(n:ESNode):bool =
  n.typ in {ekFunctionDeclaration,ekFunctionExpression}

proc isStatement*(n:ESNode):bool =
  n.typ in {ekExpressionStatement, ekBlockStatement, ekEmptyStatement,
            ekDebuggerStatement, ekWithStatement, ekReturnStatement,
            ekLabeledStatement, ekBreakStatement, ekContinueStatement,
            ekIfStatement, ekSwitchStatement, ekThrowStatement,
            ekTryStatement, ekWhileStatement, ekDoWhileStatement,
            ekForStatement, ekForInStatement, ekEmit} or n.isDeclaration()

proc isPattern*(n:ESNode):bool =
  n.typ in {ekIdentifier} #es5: only identifier matchs pattern. future: deconstructors etc

proc isBinaryOp*(op:string):bool = 
  op in ["==", "!=", "===", "!==", "<", "<=", ">", ">=", "<<", ">>", ">>>",
        "+", "-", "*", "/", "%", "|", "^", "&", "in", "instanceof" ]

proc isAsgnOp*(op:string):bool =
  op in ["=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=",
        ">>>=", "|=", "^=", "&=" ]

proc isLogicalOp*(op:string):bool =
  op in ["&&", "||"]

proc isUnaryOp*(op:string):bool =
  op in ["-", "+", "!", "~", "typeof", "void", "delete"]

proc isUpdateOp*(op:string):bool =
  op in ["++", "--"]

# Accessors

proc `value=`*(lit: var ESNode, val:bool) = 
  assert(lit.typ == ekBoolLit)
  lit.bval = val

proc `value=`*(lit: var ESNode, val: SomeFloat) = 
  assert(lit.typ == ekFloatLit)
  lit.fval = val
proc `value=`*(lit: var ESNode, val: SomeInteger) = 
  assert(lit.typ == ekIntLit)
  lit.ival = val
proc `value=`*(prop: var ESNode, val: ESNode) =
  if prop.typ == ekProperty:
    prop.pvalue = val
  elif prop.typ == ekStrLit:
    prop.strval = val
  else:
    echo "value= error"
proc value*(prop: ESNode): ESNode = prop.pvalue
proc `argument=`*(n: var ESNode, val:ESNode) =
  case n.typ:
  of ekReturnStatement: n.rargument = val
  of ekThrowStatement: n.targument = val
  of ekUnaryExpression: n.unargument = val
  of ekUpdateExpression: n.uargument = val
  else:
    assert(false, "argument= wrong node typ: " & $n.typ)

proc argument*(n: ESNode):ESNode=
  case n.typ:
  of ekReturnStatement: result = n.rargument
  of ekThrowStatement: result = n.targument
  of ekUnaryExpression: result = n.unargument
  of ekUpdateExpression: result = n.uargument
  else:
    assert(false, "argument= wrong node typ: " & $n.typ)

proc add*(n: var ESNode, val: ESNode) =
  # TODO: case? also check val typ
  if n.typ == ekProgram: 
    if val.isNil: return # TODO: error?
    if val.typ == ekProgram:
      n.pbody.add(val.pbody)
    else:
      n.pbody.add(val)
  elif n.typ in {ekFunction,ekFunctionDeclaration,ekFunctionExpression}: n.params.add(val) 
  elif n.typ == ekBlockStatement: n.bbody.add(val)
  elif n.typ == ekSwitchStatement: n.scases.add(val)
  elif n.typ == ekSwitchCase: n.sconsequent.add(val)
  elif n.typ == ekVariableDeclaration: n.vdeclarations.add(val)
  elif n.typ == ekArrayExpression: n.elements.add(val)
  elif n.typ in {ekCallExpression,ekNewExpression}: n.properties.add(val)
  elif n.typ == ekSequenceExpression: n.arguments.add(val)
  elif n.typ == ekObjectExpression: n.expressions.add(val)
  elif n.typ == ekModule: 
    if val.isNil: return # TODO: error?
    if val.typ == ekProgram:
      n.mbody.add(val.pbody)
    elif val.typ == ekImport:
      n.mimports.add(val)
    elif val.typ == ekExport:
      n.mexports.add(val)
    else:
      n.mbody.add(val)

proc `left=`*(n: var ESNode, val:ESNode) =
  case n.typ:
  of ekForInStatement: n.fleft = val
  of ekBinaryExpression: n.bleft = val
  of ekAssignmentExpression: n.aleft = val
  of ekLogicalExpression: n.lleft = val
  else:
    assert(false, "left= wrong node kind: " & $n.typ)

proc left*(n: ESNode): ESNode =
  case n.typ:
  of ekForInStatement: 
    result = n.fleft
  of ekBinaryExpression: 
    result = n.bleft
  of ekAssignmentExpression: 
    result = n.aleft
  of ekLogicalExpression: 
    result = n.lleft
  else:
    assert(false, "left wrong node kind: " & $n.typ)

proc `right=`*(n: var ESNode, val:ESNode) =
  case n.typ:
  of ekForInStatement: n.fright = val
  of ekBinaryExpression: n.bright = val
  of ekAssignmentExpression: n.aright = val
  of ekLogicalExpression: n.lright = val
  else:
    assert(false, "right= wrong node kind: " & $n.typ)

proc right*(n: ESNode): ESNode =
  case n.typ:
  of ekForInStatement: 
    result = n.fright
  of ekBinaryExpression: 
    result = n.bright
  of ekAssignmentExpression: 
    result = n.aright
  of ekLogicalExpression: 
    result = n.lright
  else:
    assert(false, "right wrong node kind: " & $n.typ)

proc `test=`*(n: var ESNode, val:ESNode) =
  case n.typ:
  of ekIfStatement: n.itest = val
  of ekSwitchCase: n.stest = val
  of ekWhileStatement: n.wtest = val
  of ekDoWhileStatement: n.dtest = val
  of ekForStatement: n.ftest = val
  of ekConditionalExpression: n.ctest = val
  else:
    assert(false, "test= wrong node kind: " & $n.typ)

proc test*(n: ESNode): ESNode =
  case n.typ:
  of ekIfStatement: result = n.itest
  of ekSwitchCase: result = n.stest
  of ekWhileStatement: result = n.wtest
  of ekDoWhileStatement: result = n.dtest
  of ekForStatement: result = n.ftest
  of ekConditionalExpression: result = n.ctest
  else:
    assert(false, "test= wrong node kind: " & $n.typ)


proc `body=`*(n: var ESNode, val:seq[ESNode]) =
  case n.typ:
  of ekProgram: n.pbody = val
  of ekBlockStatement: n.bbody = val
  of ekModule: n.mbody = val
  else:
    assert(false, "body= wrong node kind: " & $n.typ)

proc `body=`*(n: var ESNode, val:ESNode) =
  case n.typ:
  of ekWithStatement: n.wsbody = val
  of ekLabeledStatement: n.lbody = val
  of ekCatchClause: n.cbody = val
  of ekWhileStatement: n.wbody = val
  of ekDoWhileStatement: n.dbody = val
  of ekForStatement: n.fsbody = val
  of ekForInStatement: n.fibody = val
  of ekFunction,ekFunctionDeclaration,ekFunctionExpression:
    n.fbody = val
  else:
    assert(false, "body= wrong node kind: " & $n.typ)

#[
proc body*(n: ESNode):seq[ESNode] =
  case n.typ:
  of ekProgram: result = n.pbody
  of ekBlockStatement: result = n.bbody
  else:
    assert(false, "test wrong node kind: " & $n.typ)
]#

proc body*(n: ESNode):ESNode =
  case n.typ:
  of ekWithStatement: result = n.wsbody
  of ekLabeledStatement: result = n.lbody
  of ekCatchClause: result = n.cbody
  of ekWhileStatement: result = n.wbody
  of ekDoWhileStatement: result = n.dbody
  of ekForStatement: result = n.fsbody
  of ekForInStatement: result = n.fibody
  of ekFunction,ekFunctionDeclaration,ekFunctionExpression:
    result = n.fbody
  else:
    assert(false, "body wrong node kind: " & $n.typ)

# Basic nodes
proc newSourceLoc*(file:string, starts,ends:tuple[line,col:int]): SourceLocation=
  SourceLocation(source: file, starts: starts, ends: ends)

proc newNode*(kind:ESNodeKind,loc:SourceLocation=newSourceLoc("nil",(-1,-1),(-1,-1))):ESNode =
  ESNode(typ: kind, loc:loc)

proc newIdent*(name:string, loc:SourceLocation=nil):ESNode =
  result = newNode(ekIdentifier,loc)
  result.name = name

proc newIdent*(name:string, typ: string, loc:SourceLocation=nil):ESNode =
  result = newNode(ekIdentifier,loc)
  result.ptyp = typ
  result.name = name

proc newLiteral*[T: SomeNumber|bool](val:T,loc:SourceLocation=nil):ESNode =
  var kind : ESNodeKind
  if T is bool:
    kind = ekBoolLit
  elif T is SomeFloat:
    kind = ekFloatLit
  elif T is SomeInteger:
    kind = ekIntLit
  elif T is string:
    kind = ekStrLit
  result = newNode(kind,loc)
  result.value = val

proc newLiteral*(loc:SourceLocation=nil):ESNode =
  result = newNode(ekNullLit,loc)

proc newProgram*(loc:SourceLocation):ESNode = 
  result = newNode(ekProgram,loc)
  result.pbody = newSeq[ESNode]()

proc newProgram*(body:varargs[ESNode],loc:SourceLocation=nil):ESNode = 
  result = newNode(ekProgram,loc)
  result.pbody = @body

proc newModule*(name:string):ESNode = 
  result = newNode(ekModule)
  result.mname = name
  result.mbody = newSeq[ESNode]()
  result.mexports = newSeq[ESNode]()
  result.mimports = newSeq[ESNode]()

proc newImport*(module,ident:string):ESNode =
  result = newNode(ekImport)
  result.iident = ident
  result.imodule = module

proc newExport*(ident:string):ESNode =
  result = newNode(ekExport)
  result.eident = ident

proc newFuncDecl*(id,body:ESNode, params:varargs[ESNode], exp: bool=false, loc:SourceLocation=nil):ESNode =
  result = newNode(ekFunctionDeclaration,loc)
  assert id.typ == ekIdentifier
  assert body.typ == ekBlockStatement
  for el in params: assert el.isPattern
  result.fexported = exp
  result.id = id
  result.params = @params
  result.body = body

proc newEmitExpr*(code:string, loc:SourceLocation=nil):ESNode =
  result = newNode(ekEmit, loc)
  result.code = code