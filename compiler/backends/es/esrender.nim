import esast
from strutils import `%`,splitLines, indent
import strformat

proc render*(en:ESNode, indlvl:int=0 ):string

proc renderSourceLoc*(sl:SourceLocation):string = 
  "\n/* source:" & sl.source & " line: " & $sl.starts.line & ", col: " & $sl.starts.col & "*/\n"

proc renderIdent*(sl:ESNode, indlvl=0):string =
  assert sl.typ == ekIdentifier, $sl.typ
  sl.name

proc renderLit*(lit:ESNode, indlvl=0):string =
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
  of ekStrLit: result = "\"" & lit.strval & "\""
  of ekNullLit: result = "null"
  else:
    assert false, "not a literal " & $lit.typ

proc renderProgram(p:ESNode, indlvl=0): string =
  result = fmt"/* Generated by the Nim Compiler v{NimVersion} */" & "\n'use strict'"
  for el in p.pbody:
    add result, "\n"&render(el)

proc renderModule(p:ESNode, indlvl=0): string =
  result = fmt"/* Generated by the Nim Compiler v{NimVersion} */" & "\n'use strict'"
  var indlvl = 0
  for i in p.mimports:
    add result, "\n" & render(i, indlvl)
  for el in p.mbody:
    add result, "\n" & render(el, indlvl)
  for e in p.mexports:
    add result, "\n" & render(e, indlvl)

proc renderImport(p:ESNode, indlvl=0): string =
  result = &"import {p.iident} from {p.imodule};"

proc renderExport(p:ESNode, indlvl=0): string =
  result = &"export {{ {p.eident} }};"

proc renderVarDeclarator(v:ESNode, indlvl=0):string =
  #result = fmt"{render(v.vid)} /*{v.vid.ptyp}*/ = {render(v.vinit)}"
  if v.vid.typ == ekIdentifier:
    result = fmt"{render(v.vid)} /*{v.vid.ptyp}*/ = {render(v.vinit)}"
  else:
    result = fmt"{render(v.vid)} /**/ = {render(v.vinit)}"

proc renderParamProperty(p:ESNode, indlvl=0):string =
  result = "$1 = $2" % [render(p.key), render(p.value)]

proc renderParam(p: ESNode, indlvl=0): string =
  if p.typ == ekIdentifier:
    result = &"{p.name} /*{p.ptyp}*/" 
  elif p.typ == ekVariableDeclarator:
    result = renderVarDeclarator(p)
  elif p.typ == ekObjectExpression:
    result = "{"
    for i,prop in p.properties:
      add result, renderParamProperty(prop)
      if i != p.properties.len-1:
        add result, ", "
    add result, "}={}" #FIXME: move ={} to the ast?
  else:
    assert(p.isPattern, $p.typ)

proc renderFunc(f:ESNode, indlvl=0):string =
  result = if f.fexported: "export " else: ""
  result &= &"function {render(f.id)}("
  for i,par in f.params:
    add result, renderParam(par,indlvl)
    if i!=f.params.len-1: add result , ", "
  add result, ") {\n$1\n} /*$2*/" % [render(f.body).indent(indlvl+2), f.id.ptyp]

proc renderExprStmt(e:ESNode, indlvl=0):string =
  (render(e.expression) & ";").indent(indlvl)

proc renderBlockStmt(b:ESNode, indlvl=0):string =
  result = ""
  for i, s in b.bbody:
    if i == 0: discard
    else: add result, "\n"
    add result, render(s) #& ";" 
  result = result.indent(indlvl)

proc renderEmptyStmt(s:ESNode, indlvl=0):string = ";"

proc renderDebuggerStmt(s:ESNode, indlvl=0):string = "debugger;"

proc renderWithStmt(s:ESNode, indlvl=0):string =
  "//withstmt not supported for now"

proc renderReturnStmt(s:ESNode, indlvl=0):string =
  result = "return " & render(s.argument) & ";"

proc renderLabeledStmt(s:ESNode, indlvl = 0):string = 
  result = render(s.llabel) & ": {\n"
  add result, render(s.body).indent(indlvl+2) & 
  "\n};"

proc renderBreakStmt(s:ESNode, indlvl=0):string =
  result = "break "
  if not s.blabel.isNil:
    add result, render(s.blabel)
  add result, ";"

proc renderContinueStmt(s:ESNode, indlvl=0):string =
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
      add result, " else $1 " % [render(i.ialternate).indent(indlvl)]

proc renderSwitchCase(c:ESNode, indlvl=0):string =
  result = "\ncase ($1):" % [render(c.test)]
  if not c.sfall: 
    for i,s in c.sconsequent:
      add result, "\n"
      add result, render(s).indent(2)
      add result, "\nbreak;".indent(2)
      if not(i==c.sconsequent.len-1): add result, "\n"
  result = result.indent(indlvl)

proc renderDefaultCase(c:ESNode, indlvl=0):string =
  result = "\ndefault:"
  for i, s in c.dconsq:
    add result, "\n"
    add result, render(s).indent(2)
    if not(i==c.dconsq.len-1): add result, "\n"
  result = result.indent(indlvl)

proc renderSwitchStmt(s:ESNode,indlvl=0):string =
  result = "switch ($1) {" % [render(s.sdiscriminant)]
  for c in s.scases:
    add result, renderSwitchCase(c).indent(2)
  if s.def.typ == ekDefaultCase:
    add result, renderDefaultCase(s.def).indent(2)
  add result, "\n}"
  result = result.indent(indlvl)


proc renderThrowStmt(t:ESNode, indlvl=0):string = 
  result = "throw $1;" % [render(t.argument)]

proc renderTryStmt(t:ESNode, indlvl=0):string = 
  result = "try {\n$1 \n} " % [render(t.tblck, indlvl+2)]
  if not t.thandler.isNil:
    add result, render(t.thandler, indlvl)
  if not t.tfinalizer.isNil:
    add result, " finally {\n$1\n}" % [render(t.tfinalizer, indlvl+2)]

proc renderCatchClause(c:ESNode, indlvl=0):string =
  result = "catch ($1) {\n$2\n}" % [render(c.cparam), render(c.body, indlvl+2)]

proc renderWhileStmt(w:ESNode, indlvl=0):string =
  result = "while ($1) {\n$2\n}" % [render(w.test), render(w.body).indent(indlvl+2)]

proc renderDoWhileStmt(d:ESNode, indlvl=0):string =
  result = "do {\n$1\n} while ($2)" % [render(d.body),render(d.test)]

proc renderForStmt(f:ESNode, indlvl=0):string =
  result = "for ($1 $2; $3) {\n$4\n}" % [
    render(f.finit), render(f.test), render(f.fupdate), render(f.body,indlvl+2)]

proc renderForInStmt(f:ESNode, indlvl=0):string =
  result = "for ($1 in $2) {\n$3\n}" % [
    render(f.left), render(f.right), render(f.body)]

proc render(k: ESVarKind, indlvl=0): string = 
  case k:
  of esLet: "let"
  of esVar: "var"
  of esConst: "const"

proc renderVarDecl(v:ESNode, indlvl=0):string =
  result = if v.vexp: "export " else: "" 
  result &= render(v.vkind) & " "
  for i,vd in v.vdeclarations:
    if vd.typ == ekEmptyStatement: continue 
    add result, render(vd)
    if i != v.vdeclarations.len-1:
      add result,", "
    else:
      add result,";"

proc renderThisExpr(t:ESNode, indlvl=0):string = "this"

proc renderArrayExpr(a:ESNode, indlvl=0):string =
  result = "["
  for i,el in a.elements:
    add result, render(el)
    if i != a.elements.len-1:
      add result, ", "
  add result, "]"

proc renderObjExpr(o:ESNode, indlvl=0):string = 
  result = "{"
  for i,prop in o.properties:
    add result, render(prop)
    if i != o.properties.len-1:
      add result, ", "
  add result, "}"

proc renderProperty(p:ESNode, indlvl=0):string =
  result = "\"$1\" : $2" % [render(p.key), render(p.value)]

proc renderUnaryExpr(u:ESNode, indlvl=0):string =
  if u.unprefix:
    result = "$1($2)" % [u.unoperator, render(u.argument)]
  else:
    result = "($2)$1" % [u.unoperator, render(u.argument)]

proc renderUpdateExpr(u:ESNode, indlvl=0): string =
  if u.uprefix:
    result = "$1$2" % [u.uoperator, render(u.argument)]
  else:
    result = "$2$1" % [u.uoperator, render(u.argument)]

proc renderBinaryExpr(b:ESNode, indlvl=0):string =
  result = "$1 $2 $3" % [render(b.left), b.boperator, render(b.right)]

proc renderAsgnExpr(a:ESNode, indlvl=0):string =
  result = "$1 $2 $3" % [render(a.left), a.aoperator, render(a.right)]

proc renderLogicalExpr(e:ESNode, indlvl=0):string =
  result = "$1 $2 $3" % [render(e.left), e.loperator, render(e.right)]

proc renderMemberExpr(m:ESNode, indlvl=0):string =
  if m.computed:
    result = "$1.$2" % [render(m.mobject), render(m.property)]
  else:
    result = "$1[$2]" % [render(m.mobject), render(m.property)]

proc renderCondExpr(c:ESNode, indlvl=0):string =
  result = "$1 ? ($2) : ($3)" % [render(c.test), render(c.cconsequent),
    render(c.calternate)]

proc renderCallExpr(c:ESNode, indlvl=0):string =
  result = render(c.callee)&"(" 
  for i,arg in c.arguments:
    add result, render(arg)
    if i!=c.arguments.len-1:
      add result, ","
  add result, ")"

proc renderMemberCallExpr(c:ESNode, indlvl=0):string =
  result = &"{render(c.cobj)}.{render(c.objprop)}(" 
  for i,arg in c.args:
    add result, render(arg)
    if i!=c.args.len-1:
      add result, ","
  add result, ")"

proc renderNewExpr(c:ESNode, indlvl=0):string =
  result = "new $1(" % [render(c.callee)]
  for i,arg in c.arguments:
    add result, render(arg)
    if i!=c.arguments.len-1:
      add result, ","
  add result, ")"

proc renderSeqExpr(s:ESNode, indlvl=0):string =
  for i,ex in s.expressions:
    add result, render(ex)
    if i!=s.expressions.len-1:
      add result, ","

proc render*(en:ESNode, indlvl=0):string =
  if en.isNil: 
    when defined debug:
      return fmt"/*An ESNode is nil*/"
    else:
      {.warning: "An ESNode is nil".}
  result = "" #& $en.typ
  # TODO:  
  if not (en.loc.isNil) and en.isStatement:
    add result, renderSourceLoc(en.loc)
  case en.typ:
  of ekIdentifier: add result, renderIdent(en, indlvl)
  of ekStrLit, ekBoolLit, ekNullLit, ekIntLit,
    ekFloatLit, ekRegExpLiteral:
    add result, renderLit(en, indlvl)
  of ekProgram:
    add result, renderProgram(en, indlvl)
  of ekModule:
    add result, renderModule(en, indlvl)
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
    add result, renderDebuggerStmt(en, indlvl)
  of ekWithStatement:
    add result, renderWithStmt(en, indlvl)
  of ekReturnStatement:
    add result, renderReturnStmt(en, indlvl)
  of ekLabeledStatement:
    add result, renderLabeledStmt(en, indlvl)
  of ekBreakStatement:
    add result, renderBreakStmt(en, indlvl)
  of ekContinueStatement:
    add result, renderContinueStmt(en, indlvl)
  of ekIfStatement:
    add result, renderIfStmt(en, indlvl)
  of ekSwitchStatement:
    add result, renderSwitchStmt(en, indlvl)
  of ekSwitchCase:
    add result, renderSwitchCase(en, indlvl)
  of ekThrowStatement:
    add result, renderThrowStmt(en, indlvl)
  of ekTryStatement:
    add result, renderTryStmt(en, indlvl)
  of ekCatchClause:
    add result, renderCatchClause(en, indlvl)
  of ekWhileStatement:
    add result, renderWhileStmt(en, indlvl)
  of ekDoWhileStatement:
    add result, renderDoWhileStmt(en, indlvl)
  of ekForStatement:
    add result, renderForStmt(en, indlvl)
  of ekForInStatement:
    add result, renderForInStmt(en, indlvl)
  of ekVariableDeclaration:
    add result, renderVarDecl(en, indlvl)
  of ekVariableDeclarator:
    add result, renderVarDeclarator(en, indlvl)
  of ekThisExpression:
    add result, renderThisExpr(en, indlvl)
  of ekArrayExpression:
    add result, renderArrayExpr(en, indlvl)
  of ekObjectExpression:
    add result, renderObjExpr(en, indlvl)
  of ekProperty:
    add result, renderProperty(en, indlvl)
  of ekUnaryExpression:
    add result, renderUnaryExpr(en, indlvl)
  of ekUpdateExpression:
    add result, renderUpdateExpr(en, indlvl)
  of ekBinaryExpression:
    add result, renderBinaryExpr(en, indlvl)
  of ekAssignmentExpression:
    add result, renderAsgnExpr(en, indlvl)
  of ekLogicalExpression:
    add result, renderLogicalExpr(en, indlvl)
  of ekMemberExpression:
    add result, renderMemberExpr(en, indlvl)
  of ekConditionalExpression:
    add result, renderCondExpr(en, indlvl)
  of ekCallExpression:
    add result, renderCallExpr(en, indlvl)
  of ekNewExpression:
    add result, renderNewExpr(en, indlvl)
  of ekSequenceExpression:
    add result, renderSeqExpr(en, indlvl)
  of ekEmit:
    add result, en.code
  of ekImport:
    add result, renderImport(en, indlvl)
  of ekExport:
    add result, renderExport(en, indlvl)
  of ekMemberCallExpression:
    add result, renderMemberCallExpr(en, indlvl)
  of ekDefaultCase:
    add result, renderDefaultCase(en, indlvl)

proc renderAndClean*(esn:ESNode):string =
  result = render(esn)
  #for ln in s.splitLines:
  #  if ln == "": continue
  #  result.add(ln&"\n")