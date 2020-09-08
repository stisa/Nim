import esast
from strutils import `%`,splitLines, indent
import strformat

proc render*(en:ESNode, indlvl:int=0):string

proc renderSourceLoc*(sl:SourceLocation):string = 
  "\n// source:" & sl.source & " line: " & $sl.starts.line & ", col: " & $sl.starts.col & "\n"

proc renderIdent*(sl:ESNode):string =
  assert sl.typ == ekIdentifier, $sl.typ
  sl.name

proc renderLit*(lit:ESNode):string =
  case lit.typ:
  of ekBoolLit: result = $lit.bval
  of ekFloatLit: 
    let f = lit.fval
    if f != f: result = "NaN"
    elif f == 0.0: result = "0.0"
    elif f == 0.5 * f:
      if f > 0.0: result = "Infinity"
      else: result = "-Infinity"
    else: result = $f
  of ekIntLit: result = $lit.ival
  of ekStrLit: result = render(lit.strval)
  of ekNullLit: result = "null"
  else:
    assert false, "not a literal " & $lit.typ

proc renderProgram(p:ESNode): string =
  result = "'use strict'" # TODO: only 1 per script
  for el in p.pbody:
    add result, "\n"&render(el)

proc renderModule(p:ESNode): string =
  result = "'use strict'" # TODO: only 1 per script
  var indlvl = 0
  for i in p.mimports:
    add result, "\n" & render(i, indlvl)
  for el in p.mbody:
    add result, "\n" & render(el, indlvl)
  for e in p.mexports:
    add result, "\n" & render(e, indlvl)

proc renderImport(p:ESNode): string =
  result = &"import {p.iident} from {p.imodule};"

proc renderExport(p:ESNode): string =
  result = &"export {{ {p.eident} }};"

proc renderVarDeclarator(v:ESNode):string =
  #result = fmt"{render(v.vid)} /*{v.vid.ptyp}*/ = {render(v.vinit)}"
  if v.vid.typ == ekIdentifier:
    result = fmt"{render(v.vid)} /*{v.vid.ptyp}*/ = {render(v.vinit)}"
  else:
    result = fmt"{render(v.vid)} /**/ = {render(v.vinit)}"

proc renderParam(p: ESNode): string =
  if p.typ == ekIdentifier:
    result = &"{p.name} /*{p.ptyp}*/" 
  elif p.typ == ekVariableDeclarator:
    result = renderVarDeclarator(p)
  else:
    assert(p.isPattern, $p.typ)

proc renderFunc(f:ESNode, indlvl=0):string =
  result = if f.fexported: "export " else: ""
  result &= &"function {render(f.id)}("
  for i,par in f.params:
    add result, renderParam par
    if i!=f.params.len-1: add result , ", "
  add result, ") {\n$1\n} /*$2*/" % [render(f.body).indent(indlvl+2), f.id.ptyp]

proc renderExprStmt(e:ESNode, indlvl=0):string =
  (render(e.expression) & ";").indent(indlvl)

proc renderBlockStmt(b:ESNode, indlvl=0):string =
  result = ""
  for i, s in b.bbody:
    if i == 0: discard
    else:
      add result, "\n"
    add result, render(s) #& ";" 
  result = result.indent(indlvl)

proc renderEmptyStmt(s:ESNode):string = ";"

proc renderDebuggerStmt(s:ESNode):string = "debugger;"

proc renderWithStmt(s:ESNode):string =
  "//withstmt not supported for now"

proc renderReturnStmt(s:ESNode):string =
  result = "return " & render(s.argument) & ";"

proc renderLabeledStmt(s:ESNode, indlvl = 0):string = 
  result = render(s.llabel) & ": {\n"
  add result, render(s.body).indent(indlvl+2) & 
  "\n};"

proc renderBreakStmt(s:ESNode):string =
  result = "break "
  if not s.blabel.isNil:
    add result, render(s.blabel)
  add result, ";"

proc renderContinueStmt(s:ESNode):string =
  result = "continue "
  if not s.blabel.isNil:
    add result, render(s.blabel)
  add result, ";"

proc renderIfStmt(i:ESNode, indlvl=0):string =
  result = "if ( $1 ) {\n$2\n}" % [ render(i.test), render(i.iconsequent).indent(indlvl+2)]
  if not i.ialternate.isNil:
    if i.ialternate.typ != ekIfStatement:
      #just the else
      if i.ialternate.typ != ekEmptyStatement:
        add result, " else {\n$1\n}" % [render(i.ialternate).indent(indlvl+2)]
    else:
      add result, " else $1 " % [render(i.ialternate).indent(indlvl+2)]

proc renderSwitchStmt(s:ESNode):string =
  result = "switch ($1) {\n" % [render(s.sdiscriminant)]
  for c in s.scases:
    add result, render(c)
  add result, "\n}"

proc renderSwitchCase(c:ESNode):string =
  result = "case ($1):\n" % [render(c.test)]
  if not c.sfall: 
    for s in c.sconsequent:
      add result, render(s)
      add result, "\nbreak;\n"

proc renderDefaultCase(c:ESNode, indlvl=0):string =
  result = "default:\n"
  var tmp = ""
  for s in c.dconsq:
    add tmp, render(s)
  tmp = tmp.indent(indlvl+2)
  result.add(tmp)
  
proc renderThrowStmt(t:ESNode):string = 
  result = "throw $1;" % [render(t.argument)]

proc renderTryStmt(t:ESNode):string = 
  result = "try {\n$1 \n} " % [render(t.tblck)]
  if not t.thandler.isNil:
    add result, render(t.thandler)
  if not t.tfinalizer.isNil:
    add result, "finally {\n$1\n}" % [render(t.tfinalizer)]

proc renderCatchClause(c:ESNode):string =
  result = "catch ($1) {$2}" % [render(c.cparam), render(c.body)]

proc renderWhileStmt(w:ESNode, indlvl=0):string =
  result = "while ($1) {\n$2\n}" % [render(w.test), render(w.body).indent(indlvl+2)]

proc renderDoWhileStmt(d:ESNode):string =
  result = "do {\n$1\n} while ($2)" % [render(d.body),render(d.test)]

proc renderForStmt(f:ESNode, indlvl=0):string =
  result = "for ($1 $2; $3) {\n$4\n}" % [
    render(f.finit), render(f.test), render(f.fupdate), render(f.body,indlvl+2)]

proc renderForInStmt(f:ESNode):string =
  result = "for ($1 in $2) {\n$3\n}" % [
    render(f.left), render(f.right), render(f.body)]

proc render(k: ESVarKind): string = 
  case k:
  of esLet: "let"
  of esVar: "var"
  of esConst: "const"

proc renderVarDecl(v:ESNode):string =
  result = if v.vexp: "export " else: "" 
  result &= render(v.vkind) & " "
  for i,vd in v.vdeclarations:
    add result, render(vd)
    if i != v.vdeclarations.len-1:
      add result,", "
    else:
      add result,";"

proc renderThisExpr(t:ESNode):string = "this"

proc renderArrayExpr(a:ESNode):string =
  result = "["
  for i,el in a.elements:
    add result, render(el)
    if i != a.elements.len-1:
      add result, ", "
    else:
      add result, "]"

proc renderObjExpr(o:ESNode):string = 
  result = "{"
  for i,prop in o.properties:
    add result, render(prop)
    if i != o.properties.len-1:
      add result, ", "
    else:
      add result, "}"

proc renderProperty(p:ESNode):string =
  result = "\"$1\" : $2" % [render(p.key), render(p.value)]

proc renderUnaryExpr(u:ESNode):string =
  if u.unprefix:
    result = "$1($2)" % [u.unoperator, render(u.argument)]
  else:
    result = "($2)$1" % [u.unoperator, render(u.argument)]

proc renderUpdateExpr(u:ESNode): string =
  if u.uprefix:
    result = "$1$2" % [u.uoperator, render(u.argument)]
  else:
    result = "$2$1" % [u.uoperator, render(u.argument)]

proc renderBinaryExpr(b:ESNode):string =
  result = "$1 $2 $3" % [render(b.left), b.boperator, render(b.right)]

proc renderAsgnExpr(a:ESNode):string =
  result = "$1 $2 $3" % [render(a.left), a.aoperator, render(a.right)]

proc renderLogicalExpr(e:ESNode):string =
  result = "$1 $2 $3" % [render(e.left), e.loperator, render(e.right)]

proc renderMemberExpr(m:ESNode):string =
  if m.computed:
    result = "$1.$2" % [render(m.mobject), render(m.property)]
  else:
    result = "$1[$2]" % [render(m.mobject), render(m.property)]

proc renderCondExpr(c:ESNode):string =
  result = "$1 ? ($2) : ($3)" % [render(c.test), render(c.cconsequent),
    render(c.calternate)]

proc renderCallExpr(c:ESNode):string =
  result = render(c.callee)&"(" 
  for i,arg in c.arguments:
    add result, render(arg)
    if i!=c.arguments.len-1:
      add result, ","
  add result, ")"

proc renderMemberCallExpr(c:ESNode):string =
  result = &"{render(c.cobj)}.{render(c.objprop)}(" 
  for i,arg in c.args:
    add result, render(arg)
    if i!=c.args.len-1:
      add result, ","
  add result, ")"

proc renderNewExpr(c:ESNode):string =
  result = "new $1(" % [render(c.callee)]
  for i,arg in c.arguments:
    add result, render(arg)
    if i!=c.arguments.len-1:
      add result, ","
  add result, ")"

proc renderSeqExpr(s:ESNode):string =
  for i,ex in s.expressions:
    add result, render(ex)
    if i!=s.expressions.len-1:
      add result, ","

proc render*(en:ESNode, indlvl=0):string =
  if en.isNil: 
    when defined debug:
      return "/*ESNode is nil*/"
    else:
      return "fuck"
  result = ""
  # TODO:  add result, renderSourceLoc(en.loc)
  case en.typ:
  of ekIdentifier: add result, renderIdent(en)
  of ekStrLit, ekBoolLit, ekNullLit, ekIntLit,
    ekFloatLit, ekRegExpLiteral:
    add result, renderLit(en)
  of ekProgram:
    add result, renderProgram(en)
  of ekModule:
    add result, renderModule(en)
  of ekFunction,ekFunctionDeclaration,ekFunctionExpression:
    add result, renderFunc(en, indlvl)
  of ekExpressionStatement:
    add result, renderExprStmt(en, indlvl)
  of ekBlockStatement:
    add result, renderBlockStmt(en, indlvl)
  of ekEmptyStatement:
    discard
    #add result, renderEmptyStmt(en)
  of ekDebuggerStatement: 
    add result, renderDebuggerStmt(en)
  of ekWithStatement:
    add result, renderWithStmt(en)
  of ekReturnStatement:
    add result, renderReturnStmt(en)
  of ekLabeledStatement:
    add result, renderLabeledStmt(en, indlvl)
  of ekBreakStatement:
    add result, renderBreakStmt(en)
  of ekContinueStatement:
    add result, renderContinueStmt(en)
  of ekIfStatement:
    add result, renderIfStmt(en, indlvl)
  of ekSwitchStatement:
    add result, renderSwitchStmt(en)
  of ekSwitchCase:
    add result, renderSwitchCase(en)
  of ekThrowStatement:
    add result, renderThrowStmt(en)
  of ekTryStatement:
    add result, renderTryStmt(en)
  of ekCatchClause:
    add result, renderCatchClause(en)
  of ekWhileStatement:
    add result, renderWhileStmt(en, indlvl)
  of ekDoWhileStatement:
    add result, renderDoWhileStmt(en)
  of ekForStatement:
    add result, renderForStmt(en)
  of ekForInStatement:
    add result, renderForInStmt(en)
  of ekVariableDeclaration:
    add result, renderVarDecl(en)
  of ekVariableDeclarator:
    add result, renderVarDeclarator(en)
  of ekThisExpression:
    add result, renderThisExpr(en)
  of ekArrayExpression:
    add result, renderArrayExpr(en)
  of ekObjectExpression:
    add result, renderObjExpr(en)
  of ekProperty:
    add result, renderProperty(en)
  of ekUnaryExpression:
    add result, renderUnaryExpr(en)
  of ekUpdateExpression:
    add result, renderUpdateExpr(en)
  of ekBinaryExpression:
    add result, renderBinaryExpr(en)
  of ekAssignmentExpression:
    add result, renderAsgnExpr(en)
  of ekLogicalExpression:
    add result, renderLogicalExpr(en)
  of ekMemberExpression:
    add result, renderMemberExpr(en)
  of ekConditionalExpression:
    add result, renderCondExpr(en)
  of ekCallExpression:
    add result, renderCallExpr(en)
  of ekNewExpression:
    add result, renderNewExpr(en)
  of ekSequenceExpression:
    add result, renderSeqExpr(en)
  of ekEmit:
    add result, en.code
  of ekImport:
    add result, renderImport(en)
  of ekExport:
    add result, renderExport(en)
  of ekMemberCallExpression:
    add result, renderMemberCallExpr(en)
  of ekDefaultCase:
    add result, renderDefaultCase(en, indlvl)
  
proc renderAndClean*(esn:ESNode):string =
  result = render(esn)
  #for ln in s.splitLines:
  #  if ln == "": continue
  #  result.add(ln&"\n")